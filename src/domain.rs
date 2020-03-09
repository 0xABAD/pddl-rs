use std::collections::{HashMap, HashSet};
use std::{error, fmt};

use crate::tokens::{Token, TokenError, TokenType, Tokenizer};

use rayon::prelude::*;

pub type TypeId = usize;
pub type PredId = usize;
pub type FuncId = usize;
pub type ConstId = usize;
pub type ActionId = usize;
pub type ParseErrors = Vec<ParseError>;

/// `Domain` represents the final output from parsing the contents
/// representing some PDDL domain.
pub struct Domain<'a> {
    /// The parsed domain name.
    pub name: &'a str,

    reqs: u32,                  // Parsed (:requirements) as a bit vector.
    types: Types,               // Parsed (:types).
    predicates: Vec<Predicate>, // Parsed (:predicates) ordered by PredId.
    functions: Vec<Function>,   // Parsed (:functions) ordered by FuncId.
    constants: Vec<Constant>,   // Parsed (:constants) ordered by ConstId.
    actions: Vec<Action>,       // Parsed (:action ...) definitions.
}

impl<'a> Domain<'a> {
    /// `is_domain` return true if `contents` represents a PDDL domain.
    /// Only the first few tokens of `cotents` is paresed to make this
    /// determination.
    pub fn is_domain(contents: &str) -> bool {
        let mut dp = DomainParser::new(contents);
        dp.consume(TokenType::LParen)
            .and_then(|_| dp.specific_ident("define"))
            .and_then(|_| dp.consume(TokenType::LParen))
            .and_then(|_| dp.specific_ident("domain"))
            .is_ok()
    }

    /// `parse` returns a complete domain represented by the PDDL domain
    /// within `contents.`  Returns a `ParseError` if any syntax or semantic
    /// error is encountered.
    pub fn parse(contents: &str) -> Result<Domain, ParseErrors> {
        let mut top = DomainParser::new(contents);

        let tr: ParseResult;
        match top.top_level() {
            Ok(pr) => tr = pr,
            Err(e) => return Err(vec![e]),
        }

        let mut dom = Domain {
            name: tr.name,
            reqs: tr.reqs,
            types: tr.types,
            predicates: vec![],
            functions: vec![],
            constants: vec![],
            actions: vec![],
        };

        let mut parsers: Vec<DomainParser> = vec![];

        if tr.pred_loc != Token::default() {
            let loc = tr.pred_loc;
            let src = &contents[loc.pos..];
            let mut dp = DomainParser::with_offset(src, loc.col, loc.line);

            dp.reqs = dom.reqs;
            dp.what = ParsingWhat::Predicates;
            parsers.push(dp);
        }

        if tr.func_loc != Token::default() {
            let loc = tr.func_loc;
            let src = &contents[loc.pos..];
            let mut dp = DomainParser::with_offset(src, loc.col, loc.line);

            dp.reqs = dom.reqs;
            dp.what = ParsingWhat::Functions;
            parsers.push(dp);
        }

        if tr.const_loc != Token::default() {
            let loc = tr.const_loc;
            let src = &contents[loc.pos..];
            let mut dp = DomainParser::with_offset(src, loc.col, loc.line);

            dp.reqs = dom.reqs;
            dp.what = ParsingWhat::Constants;
            parsers.push(dp);
        }

        let types = &dom.types;
        let results: Vec<Result<ParseResult, ParseError>> = parsers
            .par_iter_mut()
            .map(|dp| match dp.what {
                ParsingWhat::Predicates => dp.predicates(types),
                ParsingWhat::Functions => dp.functions(types),
                ParsingWhat::Constants => dp.constants(types),
                _ => panic!("Parsing incorrect contents: {:?}", dp.what),
            })
            .collect();

        let mut errors: Vec<ParseError> = vec![];
        for result in results {
            let pr = match result {
                Ok(r) => r,
                Err(e) => {
                    errors.push(e);
                    ParseResult::with_name("")
                }
            };
            if errors.len() > 0 {
                continue;
            }
            match pr.what {
                ParsingWhat::Predicates => dom.predicates = pr.predicates,
                ParsingWhat::Functions => dom.functions = pr.functions,
                ParsingWhat::Constants => dom.constants = pr.constants,
                _ => panic!("Parse result of unhandled kind: {:?}", pr.what),
            }
        }

        if errors.len() > 0 {
            return Err(errors);
        }
        parsers.clear();

        let mut const_map: HashMap<String, ConstId> = HashMap::new();
        for i in 0..dom.constants.len() {
            let c = &dom.constants[i];
            if c.id != i {
                panic!("Constant ID not equal to its index");
            }
            const_map.insert(c.name.clone(), c.id);
        }

        let mut pred_map: HashMap<String, PredId> = HashMap::new();
        for i in 0..dom.predicates.len() {
            let p = &dom.predicates[i];
            if p.id != i {
                panic!("Predicate ID not equal to its index");
            }
            pred_map.insert(p.signature_key(), p.id);
        }

        let mut func_map: HashMap<String, FuncId> = HashMap::new();
        for i in 0..dom.functions.len() {
            let f = &dom.functions[i];
            if f.id != i {
                panic!("Function ID not equal to its index");
            }
            func_map.insert(f.signature_key(), f.id);
        }

        for loc in tr.action_locs {
            let src = &contents[loc.pos..];
            let mut dp = DomainParser::with_offset(src, loc.col, loc.line);

            dp.reqs = dom.reqs;
            dp.what = ParsingWhat::Action;
            dp.types = Some(&dom.types);
            dp.const_map = Some(&const_map);
            dp.constants = Some(&dom.constants);
            dp.pred_map = Some(&pred_map);
            dp.predicates = Some(&dom.predicates);
            dp.func_map = Some(&func_map);
            dp.functions = Some(&dom.functions);

            parsers.push(dp);
        }

        let results: Vec<Result<ParseResult, ParseError>> = parsers
            .par_iter_mut()
            .map(|dp| match dp.what {
                ParsingWhat::Action => dp.action(),
                _ => panic!("Parsing incorrect contents: {:?}", dp.what),
            })
            .collect();

        let mut act_id: ActionId = 0;
        let mut act_names: HashSet<String> = HashSet::new();

        for result in results {
            let pr = match result {
                Ok(r) => r,
                Err(e) => {
                    errors.push(e);
                    ParseResult::with_name("")
                }
            };
            if errors.len() > 0 {
                continue;
            }
            match pr.what {
                ParsingWhat::Action => {
                    let mut act = pr.action.expect("did not receive a parsed :action");
                    if act_names.contains(&act.name) {
                        let s = format!("action, {}, is already defined", &act.name);
                        errors.push(ParseError::semantic(act.line, act.col, &s));
                    } else {
                        act.id = act_id;
                        act_id += 1;
                        act_names.insert(act.name.clone());
                        dom.actions.push(act);
                    }
                }
                _ => panic!("Parse result of unhandled kind: {:?}", pr.what),
            }
        }

        if errors.len() > 0 {
            return Err(errors);
        }

        Ok(dom)
    }

    pub fn parse_seq(contents: &str) -> Result<Domain, ParseErrors> {
        let mut top = DomainParser::new(contents);
        let mut errors: Vec<ParseError> = vec![];

        let tr: ParseResult;
        match top.top_level() {
            Ok(r) => tr = r,
            Err(e) => return Err(vec![e]),
        }

        let mut dom = Domain {
            name: tr.name,
            reqs: tr.reqs,
            types: tr.types,
            predicates: vec![],
            functions: vec![],
            constants: vec![],
            actions: vec![],
        };

        if tr.pred_loc != Token::default() {
            let loc = tr.pred_loc;
            let src = &contents[loc.pos..];
            let mut dp = DomainParser::with_offset(src, loc.col, loc.line);

            dp.reqs = dom.reqs;
            match dp.predicates(&dom.types) {
                Ok(pr) => dom.predicates = pr.predicates,
                Err(e) => errors.push(e),
            }
        }

        if tr.func_loc != Token::default() {
            let loc = tr.func_loc;
            let src = &contents[loc.pos..];
            let mut dp = DomainParser::with_offset(src, loc.col, loc.line);

            dp.reqs = dom.reqs;
            match dp.functions(&dom.types) {
                Ok(pr) => dom.functions = pr.functions,
                Err(e) => errors.push(e),
            }
        }

        if tr.const_loc != Token::default() {
            let loc = tr.const_loc;
            let src = &contents[loc.pos..];
            let mut dp = DomainParser::with_offset(src, loc.col, loc.line);

            dp.reqs = dom.reqs;
            match dp.constants(&dom.types) {
                Ok(pr) => dom.constants = pr.constants,
                Err(e) => errors.push(e),
            }
        }

        let mut const_map: HashMap<String, ConstId> = HashMap::new();
        for i in 0..dom.constants.len() {
            let c = &dom.constants[i];
            if c.id != i {
                panic!("Constant ID not equal to its index");
            }
            const_map.insert(c.name.clone(), c.id);
        }

        let mut pred_map: HashMap<String, PredId> = HashMap::new();
        for i in 0..dom.predicates.len() {
            let p = &dom.predicates[i];
            if p.id != i {
                panic!("Predicate ID not equal to its index");
            }
            pred_map.insert(p.signature_key(), p.id);
        }

        let mut func_map: HashMap<String, FuncId> = HashMap::new();
        for i in 0..dom.functions.len() {
            let f = &dom.functions[i];
            if f.id != i {
                panic!("Function ID not equal to its index");
            }
            func_map.insert(f.signature_key(), f.id);
        }

        let mut act_id: ActionId = 0;
        let mut act_names: HashSet<String> = HashSet::new();
        for loc in tr.action_locs {
            let src = &contents[loc.pos..];
            let mut dp = DomainParser::with_offset(src, loc.col, loc.line);

            dp.reqs = dom.reqs;
            dp.types = Some(&dom.types);
            dp.const_map = Some(&const_map);
            dp.constants = Some(&dom.constants);
            dp.pred_map = Some(&pred_map);
            dp.predicates = Some(&dom.predicates);
            dp.func_map = Some(&func_map);
            dp.functions = Some(&dom.functions);

            match dp.action() {
                Ok(pr) => {
                    let mut act = pr.action.expect("did not receive a parsed :action");
                    if act_names.contains(&act.name) {
                        let s = format!("action, {}, is already defined", &act.name);
                        errors.push(ParseError {
                            what: ParseErrorType::SemanticError(s),
                            line: act.line,
                            col: act.col,
                        });
                    } else {
                        act.id = act_id;
                        act_id += 1;
                        act_names.insert(act.name.clone());
                        dom.actions.push(act);
                    }
                }
                Err(e) => errors.push(e),
            }
        }

        if errors.len() > 0 {
            return Err(errors);
        }
        Ok(dom)
    }

    /// `has_requirement` returns true if this `Domain` has the requirement
    /// of `r`.
    pub fn has_requirement(&self, r: Requirement) -> bool {
        let b = self.reqs & (1 << r.index());
        if r == Requirement::Strips {
            return self.reqs == 0 || b > 0;
        }
        b > 0
    }

    /// `id_for_type` possibly returns the `TypeId` for the string `t`.
    pub fn id_for_type(&self, t: &str) -> Option<&TypeId> {
        let k = t.to_ascii_lowercase();
        self.types.types.get(&k)
    }

    /// `parent_type_ids` retuns the immediate parent TypeID set for `id`.
    /// Note that this doesn't include any grandparent Ids, etc.
    pub fn parent_type_ids(&self, id: TypeId) -> &HashSet<TypeId> {
        &self.types.parent_types[id]
    }
}

/// `Requirement` represents one of the allowed requirement specifications
/// that may be within a PDDL domain.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Requirement {
    Strips,
    Typing,
    Equality,
    NegativePreconditions,
    DisjunctivePreconditions,
    ExistentialPreconditions,
    UniversalPreconditions,
    QuantifiedPreconditions,
    ConditionalEffects,
    Fluents,
    NumericFluents,
    ObjectFluents,
    Adl,
    DurativeActions,
    DurationInequalities,
    ContinuousEffects,
    DerivedPredicates,
    TimedInitialLiterals,
    Preferences,
    Constraints,
    ActionCosts,
}

/// String forms of `Requirement`.  Note that there positions must match.
const REQUIREMENTS: [&'static str; 21] = [
    ":strips",
    ":typing",
    ":equality",
    ":negative-preconditions",
    ":disjunctive-preconditions",
    ":existential-preconditions",
    ":universal-preconditions",
    ":quantified-preconditions",
    ":conditional-effects",
    ":fluents",
    ":numeric-fluents",
    ":object-fluents",
    ":adl",
    ":durative-actions",
    ":duration-inequalities",
    ":continuous-effects",
    ":derived-predicates",
    ":timed-initial-literals",
    ":preferences",
    ":constraints",
    ":action-costs",
];

impl Requirement {
    /// `index` returns index of the `Requirement` to get the string form
    /// from the `REQUIREMENTS` array.
    pub fn index(self) -> usize {
        match self {
            Requirement::Strips => 0,
            Requirement::Typing => 1,
            Requirement::Equality => 2,
            Requirement::NegativePreconditions => 3,
            Requirement::DisjunctivePreconditions => 4,
            Requirement::ExistentialPreconditions => 5,
            Requirement::UniversalPreconditions => 6,
            Requirement::QuantifiedPreconditions => 7,
            Requirement::ConditionalEffects => 8,
            Requirement::Fluents => 9,
            Requirement::NumericFluents => 10,
            Requirement::ObjectFluents => 11,
            Requirement::Adl => 12,
            Requirement::DurativeActions => 13,
            Requirement::DurationInequalities => 14,
            Requirement::ContinuousEffects => 15,
            Requirement::DerivedPredicates => 16,
            Requirement::TimedInitialLiterals => 17,
            Requirement::Preferences => 18,
            Requirement::Constraints => 19,
            Requirement::ActionCosts => 20,
        }
    }

    /// `from_index` is the dual of `Requirement::index` function.  Panics
    /// if index is out of bounds.
    ///
    /// # Example
    ///
    /// ```
    /// use pddl_rs::domain::Requirement;
    /// let p = Requirement::Preferences;
    /// let i = p.index();
    /// assert_eq!(p, Requirement::from_index(i));
    /// ```
    pub fn from_index(index: usize) -> Requirement {
        match index {
            0 => Requirement::Strips,
            1 => Requirement::Typing,
            2 => Requirement::Equality,
            3 => Requirement::NegativePreconditions,
            4 => Requirement::DisjunctivePreconditions,
            5 => Requirement::ExistentialPreconditions,
            6 => Requirement::UniversalPreconditions,
            7 => Requirement::QuantifiedPreconditions,
            8 => Requirement::ConditionalEffects,
            9 => Requirement::Fluents,
            10 => Requirement::NumericFluents,
            11 => Requirement::ObjectFluents,
            12 => Requirement::Adl,
            13 => Requirement::DurativeActions,
            14 => Requirement::DurationInequalities,
            15 => Requirement::ContinuousEffects,
            16 => Requirement::DerivedPredicates,
            17 => Requirement::TimedInitialLiterals,
            18 => Requirement::Preferences,
            19 => Requirement::Constraints,
            20 => Requirement::ActionCosts,
            _ => panic!("Unrecognized Requirement index: {}", index),
        }
    }
}

impl fmt::Display for Requirement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", REQUIREMENTS[self.index()])
    }
}

/// `Predicate` represents a predicate definition that is found
/// within the `:predicates` section of a PDDL domain.
#[derive(Debug)]
pub struct Predicate {
    /// A unique assigned ID for the predicate.
    pub id: PredId,
    /// Predicate's name in lowercase form.
    pub name: String,
    /// Predicate's parameters.
    pub params: Vec<Param>,
}

impl Predicate {
    fn signature_key(&self) -> String {
        Signature::create_key(&self.name, self.params.len())
    }
}

/// `Function` represents a predicate definition that is found
/// within the `:predicates` section of a PDDL domain.
#[derive(Debug)]
pub struct Function {
    /// A unique assigned ID for the predicate.
    pub id: PredId,
    /// Function's name in lowercase form.
    pub name: String,
    /// The function's parameters.
    pub params: Vec<Param>,
    /// Return types of the function.
    pub return_types: Vec<TypeId>,
    /// True if the function returns a number.
    pub returns_number: bool,
}

impl Function {
    fn signature_key(&self) -> String {
        Signature::create_key(&self.name, self.params.len())
    }
}

/// `Param` is a parsed parameter that can be found within various
/// constructs of a PDDL domain (e.g. within a predicate or function
/// definition, or within an :action or :durative-action).  The
/// parameter maintains its list of immediate `TypeId`s, that the
/// parameter may be.
#[derive(Debug, PartialEq)]
pub struct Param {
    pub types: Vec<TypeId>,

    // Need to track the token positions of the parameter as
    // there is a need to check if a parameter has been previously
    // defined while also being able to shadow previously defined
    // parameters.
    start: usize, // Token start position of the param.
    end: usize,   // Token end position of the param.
}

impl Default for Param {
    fn default() -> Self {
        Param {
            types: vec![],
            start: 0,
            end: 0,
        }
    }
}

/// `Constant` is a PDDL declared constant object that is declared
/// within a domain description.
#[derive(Debug)]
pub struct Constant {
    /// A unique assigned ID for the constant.
    pub id: ConstId,
    /// Constant's name.
    pub name: String,
    /// The types that this constant derives from.
    pub types: Vec<TypeId>,
}

/// `Action` is a basic :strips PDDL action that is declared within
/// a domain description.
#[derive(Debug)]
pub struct Action {
    /// A unique assigned ID for the action.
    pub id: ActionId,
    /// Action's name in lowercase form.
    pub name: String,
    /// Parameters of the action.  An action is grounded
    /// (i.e. instantiated) when the parameters are replaced
    /// with defined objects of a problem.
    pub params: Vec<Param>,
    /// Precondition of the action that specifies what must
    /// fulfilled before the action can be executed.
    pub precondition: Option<Goal>,

    line: usize, // Line number where the action is defined.
    col: usize,  // Column number where the action is defined.
}

impl Action {
    fn new(name: &str) -> Action {
        Action {
            name: name.to_ascii_lowercase(),
            id: 0,
            params: vec![],
            precondition: None,
            line: 0,
            col: 0,
        }
    }
}

/// `Goal` represents one of several options that construct an over
/// all goal in a precondition, condition, problem goal, etc.
#[derive(Debug, PartialEq)]
pub enum Goal {
    Not(Box<Goal>),
    And(Vec<Goal>),
    Or(Vec<Goal>),
    Preference(String, Box<Goal>),
    Forall(Vec<Param>, Box<Goal>),
    Exists(Vec<Param>, Box<Goal>),
    Imply(Box<Goal>, Box<Goal>),
    Pred(PredId, Vec<Term>),
    EqualTerms(Term, Term),
    EqualFexps(Fexp, Fexp),
    Less(Fexp, Fexp),
    LessEq(Fexp, Fexp),
    Greater(Fexp, Fexp),
    GreaterEq(Fexp, Fexp),
}

/// `Term` represents one of the values that can be associated with
/// `Goal::Pred` or within a `Term::Func` itself.  In other words,
/// it represents the arguments to a predicate or a function.
#[derive(Debug, PartialEq)]
pub enum Term {
    Const(ConstId),
    Var(Vec<TypeId>),
    Func(FuncId, Vec<Term>),
}

impl Term {
    fn is_func(&self) -> bool {
        if let Term::Func(_, _) = self {
            true
        } else {
            false
        }
    }
}

/// `TermInfo` allows packaging a `Term` along with the `Token` of
/// when it was parsed.  This facilitates type checking after the
/// term has bene parsed and returned to the caller.
#[derive(Debug)]
struct TermInfo {
    what: Term,
    tok: Token,
}

#[derive(Debug, PartialEq)]
pub enum Fexp {
    Number(f64),
    Mult(Box<Fexp>, Vec<Fexp>),
    Add(Box<Fexp>, Vec<Fexp>),
    Div(Box<Fexp>, Box<Fexp>),
    Sub(Box<Fexp>, Box<Fexp>),
    Neg(Box<Fexp>),
    Func(FuncId, Vec<Term>),
    FnSymbol(String),
}

/// `expect!` provides a concise way of returning a `ParseError` from
/// a given `Token` and arbitrary number of arguments that represent the
/// expected tokens.
macro_rules! expect {
    ($dp:tt, $tok:tt, $($arg:tt)*) => {
        {
            let s = $tok.to_str($dp.contents);
            let v = vec![$($arg)*];
            (Err(ParseError::expect($tok.line, $tok.col, s, v)))
        }
    }
}

/// `token_error!` provides a concise way of returning a `ParseError` from
/// a given `TokenError` and arbitrary number of arguments that represent
/// the expected tokens.
macro_rules! token_error {
    ($dp:tt, $err:tt, $($arg:tt)*) => {
        {
            let v = vec![$($arg)*];
            (Err(ParseError::from_token_error($err, $dp.contents, v)))
        }
    }
}

/// `next_token!` calls the `next_token` method from `$dp` but converts
/// `TokenError`, if it occurs, to a `ParseError`..
macro_rules! next_token {
    ($dp:tt, $($arg:tt)*) => {
        $dp.next_token().or_else(|te| {
            let v = vec![$($arg)*];
            (Err(ParseError::from_token_error(te, $dp.contents, v)))
        });
    };
}

#[derive(Debug)]
enum ParsingWhat {
    Any,
    Functions,
    Predicates,
    Constants,
    Action,
}

/// `DomainParser` maintains the state necessary to parse a portion of
/// of a PDDL domain.
struct DomainParser<'a> {
    contents: &'a str,         // Source contents that will be parsed.
    tokenizer: Tokenizer<'a>,  // Scans contents.
    last_token: Option<Token>, // Last scanned token that hasn't been consumed.
    reqs: u32,                 // Parsed :requirements.
    what: ParsingWhat,         // What is being parsed by the parser.
    types: Option<&'a Types>,  // Previously parsed types.
    const_map: Option<&'a HashMap<String, ConstId>>, // Mapping of a constants to its ID.
    pred_map: Option<&'a HashMap<String, PredId>>, // Mapping of a predicates signature to its ID.
    func_map: Option<&'a HashMap<String, FuncId>>, // Mapping of a functions signature to its ID.
    constants: Option<&'a Vec<Constant>>, // All known constants ordered by ConstId.
    predicates: Option<&'a Vec<Predicate>>, // All known predicates ordered by PredId.
    functions: Option<&'a Vec<Function>>, // All known functions ordered by FuncId.
}

impl<'a> DomainParser<'a> {
    /// Creates a new `DomainParser` where `source` entails the entire
    /// PDDL domain to be parsed.
    fn new(source: &'a str) -> DomainParser<'a> {
        return DomainParser {
            contents: source,
            tokenizer: Tokenizer::new(source),
            last_token: None,
            reqs: 0,
            what: ParsingWhat::Any,
            types: None,
            const_map: None,
            pred_map: None,
            func_map: None,
            constants: None,
            predicates: None,
            functions: None,
        };
    }

    /// `with_offset` returns a `DomainParser` that starts at `column` and `line`, and
    /// assumes that `source` is offset at this position.  This allows the parsing
    /// to begin a specific place that was determined by the `top_level`.
    fn with_offset(source: &'a str, column: usize, line: usize) -> DomainParser<'a> {
        return DomainParser {
            contents: source,
            tokenizer: Tokenizer::with_offset(source, column, line),
            last_token: None,
            reqs: 0,
            what: ParsingWhat::Any,
            types: None,
            const_map: None,
            pred_map: None,
            func_map: None,
            constants: None,
            predicates: None,
            functions: None,
        };
    }

    /// `has_requirement` returns true if this `DomainParser` has the requirement
    /// of `r`.
    fn has_requirement(&self, r: Requirement) -> bool {
        let b = self.reqs & (1 << r.index());
        if r == Requirement::Strips {
            return self.reqs == 0 || b > 0;
        }
        b > 0
    }

    fn get_const(&self, tok: &Token, name: &str) -> Result<&Constant, ParseError> {
        let map = self.const_map.expect("constant map not set for parser");
        if let Some(&id) = map.get(name) {
            let consts = self.constants.expect("constant list not set for parser");
            return Ok(&consts[id]);
        }
        let s = format!("constant, {}, is not defined", name);
        Err(self.semantic(tok, &s))
    }

    fn get_pred(&self, tok: &Token, name: &str, terms: &[Term]) -> Result<&Predicate, ParseError> {
        let key = Signature::create_key(name, terms.len());
        let map = self.pred_map.expect("predicate map not set for parser");
        if let Some(&id) = map.get(&key) {
            let preds = self.predicates.expect("predicate list not set for parser");
            return Ok(&preds[id]);
        }
        let s = format!("predicate, {}, is not defined", name);
        Err(self.semantic(tok, &s))
    }

    fn get_func(&self, tok: &Token, name: &str, terms: &[Term]) -> Result<&Predicate, ParseError> {
        let key = Signature::create_key(name, terms.len());
        let map = self.func_map.expect("function map not set for parser");
        if let Some(&id) = map.get(&key) {
            let funcs = self.predicates.expect("function list not set for parser");
            return Ok(&funcs[id]);
        }
        let s = format!("function, {}, is not defined", name);
        Err(self.semantic(tok, &s))
    }

    /// `top_level` parses the top level forms of a PDDL domain.
    ///
    /// While the entire contents of the `DomainParser` are scanned only the
    /// `:requirements` and `:typing` section of the domain, if they exist,
    /// are parsed.  All other constructs are partially scanned to just
    /// determine their starting location within the contents of the
    /// `DomainParser` and that they form a balance construct (i.e. have
    /// balanced parenthesis.
    fn top_level(&mut self) -> Result<ParseResult<'a>, ParseError> {
        self.consume(TokenType::LParen)?;
        self.specific_ident("define")?;
        self.consume(TokenType::LParen)?;
        self.specific_ident("domain")?;

        let mut result = self.consume_ident().map(ParseResult::with_name)?;
        self.consume(TokenType::RParen)?;

        const PARENS: [TokenType; 2] = [TokenType::LParen, TokenType::RParen];
        const TOP_LEVEL_KEYWORDS: [&'static str; 9] = [
            ":derived",
            ":durative-action",
            ":action",
            ":constraints",
            ":functions",
            ":predicates",
            ":constants",
            ":types",
            ":requirements",
        ];

        let mut top_keys = &TOP_LEVEL_KEYWORDS[0..9];
        self.check_next_token_is_one_of(&PARENS)?;

        while self.next_token_is(TokenType::LParen) {
            self.check_next_is_one_of(top_keys)?;

            if top_keys.len() == 9 {
                top_keys = &top_keys[0..8];
                if self.next_keyword_is(TOP_LEVEL_KEYWORDS[8]) {
                    result.add_requirements(self.parse_requirements()?);
                    self.check_next_token_is_one_of(&PARENS)?;
                    continue;
                }
            }

            if top_keys.len() == 8 {
                top_keys = &top_keys[0..7];
                if let Some(t) = self.with_last_keyword(TOP_LEVEL_KEYWORDS[7]) {
                    if !result.has_requirement(Requirement::Typing) {
                        let e = ParseError::missing(t.line, t.col, Requirement::Typing, ":types");
                        return Err(e);
                    }
                    result.types = self.parse_types()?;
                    self.check_next_token_is_one_of(&PARENS)?;
                    continue;
                }
            }

            if top_keys.len() == 7 {
                top_keys = &top_keys[0..6];
                if self.next_keyword_is(TOP_LEVEL_KEYWORDS[6]) {
                    result.const_loc = self.balance_parens()?;
                    self.check_next_token_is_one_of(&PARENS)?;
                    continue;
                }
            }

            if top_keys.len() == 6 {
                top_keys = &top_keys[0..5];
                if self.next_keyword_is(TOP_LEVEL_KEYWORDS[5]) {
                    result.pred_loc = self.balance_parens()?;
                    self.check_next_token_is_one_of(&PARENS)?;
                    continue;
                }
            }

            if top_keys.len() == 5 {
                top_keys = &top_keys[0..4];
                if self.next_keyword_is(TOP_LEVEL_KEYWORDS[4]) {
                    result.func_loc = self.balance_parens()?;
                    self.check_next_token_is_one_of(&PARENS)?;
                    continue;
                }
            }

            if top_keys.len() == 4 {
                top_keys = &top_keys[0..3];
                if let Some(t) = self.with_last_keyword(TOP_LEVEL_KEYWORDS[3]) {
                    if !result.has_requirement(Requirement::Constraints) {
                        return Err(ParseError::missing(
                            t.line,
                            t.col,
                            Requirement::Constraints,
                            ":constraints section",
                        ));
                    }
                    result.constraints = self.balance_parens()?;
                    self.check_next_token_is_one_of(&PARENS)?;
                    continue;
                }
            }

            if self.next_keyword_is(TOP_LEVEL_KEYWORDS[2]) {
                result.action_locs.push(self.balance_parens()?);
                self.check_next_token_is_one_of(&PARENS)?;
                continue;
            }

            if let Some(t) = self.with_last_keyword(TOP_LEVEL_KEYWORDS[1]) {
                if !result.has_requirement(Requirement::DurativeActions) {
                    return Err(ParseError::missing(
                        t.line,
                        t.col,
                        Requirement::DurativeActions,
                        ":durative-action",
                    ));
                }
                result.duratives.push(self.balance_parens()?);
                self.check_next_token_is_one_of(&PARENS)?;
                continue;
            }

            if let Some(t) = self.with_last_keyword(TOP_LEVEL_KEYWORDS[0]) {
                if !result.has_requirement(Requirement::DerivedPredicates) {
                    return Err(ParseError::missing(
                        t.line,
                        t.col,
                        Requirement::DerivedPredicates,
                        ":derived predicate",
                    ));
                }
                result.deriveds.push(self.balance_parens()?);
                self.check_next_token_is_one_of(&PARENS)?;
                continue;
            }
        }

        self.consume(TokenType::RParen)?;
        match self.tokenizer.next() {
            Err(TokenError::EndOfInput { line: _, col: _ }) => Ok(result),
            Err(TokenError::InvalidInput(te)) => {
                let s = te.to_string(self.contents).to_string();
                Err(ParseError {
                    what: ParseErrorType::ExtraInput(s),
                    col: te.col,
                    line: te.line,
                })
            }
            Ok(t) => {
                let s = t.to_str(self.contents).to_string();
                Err(ParseError {
                    what: ParseErrorType::ExtraInput(s),
                    col: t.col,
                    line: t.line,
                })
            }
        }
    }

    /// `next_token` consumes the last token of the `DomainParser` if
    /// it exists; otherwise, it calls the tokenizer to return the next
    /// `Token`.
    fn next_token(&mut self) -> Result<Token, TokenError> {
        if let Some(t) = self.last_token {
            self.last_token = None;
            Ok(t)
        } else {
            self.tokenizer.next()
        }
    }

    /// `expect_next` is like `next_token` but transforms the `TokenError`
    /// into a `ParseError` if such an error is returned.  The transformed
    /// error uses `what` as the expected next token.
    fn expect_next(&mut self, what: &'a str) -> Result<Token, ParseError> {
        self.next_token().or_else(|e| token_error!(self, e, what))
    }

    /// `next_token_is` returns true if the last token received from the
    /// tokenizer has a `TokenType` that is equal to `what`.  If the is not
    /// the case or there is no last token (i.e. it has already been
    /// consumed) then false is returned.
    fn next_token_is(&mut self, what: TokenType) -> bool {
        if let Some(t) = self.last_token {
            if t.what == what {
                self.last_token = None;
                return true;
            }
        }
        false
    }

    /// `next_ident_is` is like `next_token_is` but only applies if the
    /// previous unconsumed token is a `TokenType::Ident` and its string
    /// form is case insensitive equal to `ident`.
    fn next_ident_is(&mut self, ident: &str) -> bool {
        if let Some(t) = self.last_token {
            if t.is_keyword() {
                let s = t.to_str(self.contents);
                if s.eq_ignore_ascii_case(ident) {
                    self.last_token = None;
                    return true;
                }
            }
        }
        false
    }

    /// `next_keyword_is` is like `next_token_is` but only applies if the
    /// previous unconsumed token is a `TokenType::Keyword` and its string
    /// form is case insensitive equal to `keyword`.
    fn next_keyword_is(&mut self, keyword: &str) -> bool {
        if let Some(t) = self.last_token {
            if t.is_keyword() {
                let s = t.to_str(self.contents);
                if s.eq_ignore_ascii_case(keyword) {
                    self.last_token = None;
                    return true;
                }
            }
        }
        false
    }

    /// `with_last_keyword` returns the last token that wasn't consumed
    /// if it is case insensitive equal to `keyword`.  Note, this consumes
    /// the last token if there is one.
    fn with_last_keyword(&mut self, keyword: &str) -> Option<Token> {
        if let Some(t) = self.last_token {
            if t.is_keyword() {
                let s = t.to_str(self.contents);
                if s.eq_ignore_ascii_case(keyword) {
                    self.last_token = None;
                    return Some(t);
                }
            }
        }
        None
    }

    /// `specific_ident` consumes and returns the next token that is an
    /// identifier whose string form is case insensitive equal to `what`.
    /// If that is not the case then a `ParseError` is returned that expects
    /// `what`.
    fn specific_ident(&mut self, what: &'a str) -> Result<Token, ParseError> {
        self.expect_next(what).and_then(|tok| {
            if let TokenType::Ident(s, e) = tok.what {
                let ident = &self.contents[s..e];
                if ident.eq_ignore_ascii_case(what) {
                    Ok(tok)
                } else {
                    expect!(self, tok, what)
                }
            } else {
                expect!(self, tok, what)
            }
        })
    }

    /// `specific_keyword` consumes and returns the next token that is a
    /// keyword whose string form is case insensitive equal to `what`.
    /// If that is not the case then a `ParseError` is returned that expects
    /// `what`.
    fn specific_keyword(&mut self, what: &'a str) -> Result<Token, ParseError> {
        self.expect_next(what).and_then(|tok| {
            if let TokenType::Keyword(s, e) = tok.what {
                let kw = &self.contents[s..e];
                if kw.eq_ignore_ascii_case(what) {
                    Ok(tok)
                } else {
                    expect!(self, tok, what)
                }
            } else {
                expect!(self, tok, what)
            }
        })
    }

    /// `consume` consumes and returns the next token whose `TokenType` is
    /// is equal to `what`. If that is not the case then a `ParseError` is
    /// returned that expects `what`.
    fn consume(&mut self, what: TokenType) -> Result<Token, ParseError> {
        self.expect_next(what.to_str(self.contents))
            .and_then(|tok| {
                if tok.what == what {
                    Ok(tok)
                } else {
                    expect!(self, tok, what.to_str(self.contents))
                }
            })
    }

    /// `next_ident` consumes the next token that needs to be an
    /// identifier and returns the token of that identifier.
    fn next_ident(&mut self) -> Result<Token, ParseError> {
        self.expect_next("identifier").and_then(|tok| {
            if tok.is_ident() {
                Ok(tok)
            } else {
                expect!(self, tok, "identifier")
            }
        })
    }

    /// `consume_ident` consumes the next token that needs to be an
    /// identifier and returns the string form of that identifier.
    fn consume_ident(&mut self) -> Result<&'a str, ParseError> {
        self.next_ident().map(|t| t.to_str(self.contents))
    }

    /// `check_next_token_is_one_of` checks to see if the next token is
    /// one of `ttypes`.  Note this does not consume the checked token as
    /// further decisions may be made depending on the value of the next
    /// token.
    fn check_next_token_is_one_of(&mut self, ttypes: &[TokenType]) -> Result<(), ParseError> {
        let tok: Token;

        if let Some(t) = self.last_token {
            tok = t
        } else {
            tok = self.tokenizer.next().or_else(|e| {
                let v = ttypes.iter().map(|tt| tt.to_str(self.contents)).collect();
                Err(ParseError::from_token_error(e, self.contents, v))
            })?;
            self.last_token = Some(tok);
        }

        for &tt in ttypes {
            if tok.what == tt {
                return Ok(());
            }
        }

        let v = ttypes.iter().map(|tt| tt.to_str(self.contents)).collect();
        let s = tok.to_str(self.contents);
        Err(ParseError::expect(tok.line, tok.col, s, v))
    }

    /// `check_next_is_one_of` is like `check_next_token_is_one_of` but
    /// checks if the string form of the next token is a case insensitive
    /// match to any of the elements of `words`.  Note, that like
    /// `check_next_token_is_one_of` this method does not consume the
    /// the next token.  The Ok result returned is the index of the match
    /// into the `words` slice.
    fn check_next_is_one_of(&mut self, words: &[&'a str]) -> Result<usize, ParseError> {
        let tok: Token;

        if let Some(t) = self.last_token {
            tok = t
        } else {
            tok = self.tokenizer.next().or_else(|e| {
                let v = words.to_vec();
                Err(ParseError::from_token_error(e, self.contents, v))
            })?;
            self.last_token = Some(tok);
        }

        for i in 0..words.len() {
            let w = words[i];
            let s = tok.to_str(self.contents);
            if s.eq_ignore_ascii_case(w) {
                return Ok(i);
            }
        }

        let v = words.to_vec();
        let s = tok.to_str(self.contents);
        Err(ParseError::expect(tok.line, tok.col, s, v))
    }

    /// `check_next_is_one_of_or_ident` is like `check_next_is_one_of` but
    /// also succeeds if the next token is an identifier or matches one of
    /// `words`.  Returns the token on success.
    fn check_next_is_one_of_or_ident(&mut self, words: &[&'a str]) -> Result<Token, ParseError> {
        let tok: Token;

        if let Some(t) = self.last_token {
            tok = t
        } else {
            tok = self.tokenizer.next().or_else(|e| {
                let mut v = words.to_vec();
                v.push("identifier");
                Err(ParseError::from_token_error(e, self.contents, v))
            })?;
            self.last_token = Some(tok);
        }

        if tok.is_ident() {
            return Ok(tok);
        }
        for i in 0..words.len() {
            let w = words[i];
            let s = tok.to_str(self.contents);
            if s.eq_ignore_ascii_case(w) {
                return Ok(tok);
            }
        }

        let s = tok.to_str(self.contents);
        let mut v = words.to_vec();
        v.push("identifier");
        Err(ParseError::expect(tok.line, tok.col, s, v))
    }

    /// `check_next_is_one_of_or_var` is like `check_next_is_one_of` but
    /// also succeeds if the next token is a variable or matches one of
    /// `words`.  Returns the token on success.
    fn check_next_is_one_of_or_var(&mut self, words: &[&'a str]) -> Result<Token, ParseError> {
        let tok: Token;

        if let Some(t) = self.last_token {
            tok = t
        } else {
            tok = self.tokenizer.next().or_else(|e| {
                let mut v = words.to_vec();
                v.push("variable");
                Err(ParseError::from_token_error(e, self.contents, v))
            })?;
            self.last_token = Some(tok);
        }

        if tok.is_var() {
            return Ok(tok);
        }
        for i in 0..words.len() {
            let w = words[i];
            let s = tok.to_str(self.contents);
            if s.eq_ignore_ascii_case(w) {
                return Ok(tok);
            }
        }

        let s = tok.to_str(self.contents);
        let mut v = words.to_vec();
        v.push("variable");
        Err(ParseError::expect(tok.line, tok.col, s, v))
    }

    /// `next_is_one_of` is exactly like `check_next_is_one_of` but
    /// also consumes the token.
    fn next_is_one_of(&mut self, words: &[&'a str]) -> Result<usize, ParseError> {
        let idx = self.check_next_is_one_of(words)?;
        self.last_token = None;
        Ok(idx)
    }

    /// `parse_requirements` parses the `:requirements` section of the
    /// PDDL domain and returns a bit vector where each bit position
    /// represents the requirement that is recognized.  The bit position
    /// for a requirement is the `Requirement::index` value.  Note,
    /// that a requirement that implies others (e.g. `:adl` implies
    /// `:strips`, `:typing`, and others) is expanded and also to the
    /// requirements bit vector.
    fn parse_requirements(&mut self) -> Result<u32, ParseError> {
        // Parse the first requirement where it is expected to be at
        // least one requriement.
        let idx = self.next_is_one_of(&REQUIREMENTS)?;
        let mut reqs = self.add_requirement(0, idx);

        // Consume any remaining requirements, if any.  If there
        // are no requirements then we expect a ')'.

        let mut valid: [&'static str; 22] = [
            "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ")",
        ];
        &valid[0..REQUIREMENTS.len()].copy_from_slice(&REQUIREMENTS);

        loop {
            let idx = self.next_is_one_of(&valid)?;
            if idx == valid.len() - 1 {
                return Ok(reqs); // Last token was a ')'.
            } else {
                reqs = self.add_requirement(reqs, idx);
            }
        }
    }

    /// `add_requirement` adds the `req_index` to the `existing` requirements
    /// bit vector while also expanding implied requirements of `req_index`.
    fn add_requirement(&self, existing: u32, req_index: usize) -> u32 {
        let mut reqs = existing | (1 << req_index);
        let req = Requirement::from_index(req_index);

        if let Requirement::QuantifiedPreconditions = req {
            reqs = reqs | (1 << Requirement::index(Requirement::ExistentialPreconditions));
            reqs = reqs | (1 << Requirement::index(Requirement::UniversalPreconditions));
        } else if let Requirement::Fluents = req {
            reqs = reqs | (1 << Requirement::index(Requirement::NumericFluents));
            reqs = reqs | (1 << Requirement::index(Requirement::ObjectFluents));
        } else if let Requirement::TimedInitialLiterals = req {
            reqs = reqs | (1 << Requirement::index(Requirement::DurativeActions));
        } else if let Requirement::Adl = req {
            reqs = reqs | (1 << Requirement::index(Requirement::Strips));
            reqs = reqs | (1 << Requirement::index(Requirement::Typing));
            reqs = reqs | (1 << Requirement::index(Requirement::Equality));
            reqs = reqs | (1 << Requirement::index(Requirement::NegativePreconditions));
            reqs = reqs | (1 << Requirement::index(Requirement::DisjunctivePreconditions));
            reqs = reqs | (1 << Requirement::index(Requirement::QuantifiedPreconditions));
            reqs = reqs | (1 << Requirement::index(Requirement::ExistentialPreconditions));
            reqs = reqs | (1 << Requirement::index(Requirement::UniversalPreconditions));
            reqs = reqs | (1 << Requirement::index(Requirement::ConditionalEffects));
        }

        reqs
    }

    fn semantic(&self, t: &Token, s: &str) -> ParseError {
        ParseError::semantic(t.line, t.col, s)
    }

    fn check_requirement(&self, t: &Token, r: Requirement, s: &str) -> Result<(), ParseError> {
        if !self.has_requirement(r) {
            return Err(ParseError::missing(t.line, t.col, r, s));
        }
        Ok(())
    }

    /// `parse_types` extracts all the `:types` out from a PDDL domain.  Aside
    /// from syntax errors, semantic errors are returned if `object` is
    /// attempted to be a derived type or a type has circular inheritance.
    fn parse_types(&mut self) -> Result<Types, ParseError> {
        let mut types = Types::default();
        let source = self.contents;

        types.insert("object");

        loop {
            let tok = next_token!(self, "identifier", ")")?;

            if tok.is_right() {
                return Ok(types);
            } else if tok.is_ident() {
                // Basic type declaration (:types vehicle).
                let name = tok.to_str(source);
                let mut siblings: Vec<(TypeId, Token)> = vec![(types.insert(name), tok)];

                if name.eq_ignore_ascii_case("object") {
                    return Err(self.semantic(&tok, "object declared as a derived type"));
                }

                // Have one type now collect more to get a set of types that
                // inherit from another (:types first second - parent).
                'more_types: loop {
                    let tok = next_token!(self, "identifier", "-", ")")?;

                    if tok.is_ident() {
                        let s = tok.to_str(self.contents);
                        if s.eq_ignore_ascii_case("object") {
                            return Err(self.semantic(&tok, "object declared as a derived type"));
                        }
                        siblings.push((types.insert(s), tok));
                    } else if tok.is_right() {
                        // No more types, we're done.
                        return Ok(types);
                    } else if tok.is_dash() {
                        // Reached inherintance, collect single or multiple parent types.
                        self.type_declarations(|t| {
                            let parent_name = t.to_str(source);
                            let parent_id = types.insert(parent_name);

                            for &(child_id, child_t) in &siblings {
                                types.insert_parent(child_id, parent_id);
                                types.insert_child(parent_id, child_id);

                                if types.has_circular_types(child_id) {
                                    let t = child_t;
                                    let s = format!(
                                        "{} has circular inherintance with {}",
                                        t.to_str(source),
                                        parent_name
                                    );
                                    return Err(ParseError::semantic(t.line, t.col, &s));
                                }
                            }
                            Ok(())
                        })?;
                        break 'more_types;
                    } else {
                        return expect!(self, tok, "identifier", "-", ")");
                    }
                }
            } else {
                return expect!(self, tok, "identifier", ")");
            }
        }
    }

    /// `type_declarations` parses the type declarations that follow a '-' in
    /// some PDDL domain construct (e.g. ?a - (either foo bar) ?b - baz) and
    /// calls `on_type` for each type encountered.
    fn type_declarations<F>(&mut self, mut on_type: F) -> Result<(), ParseError>
    where
        F: FnMut(&Token) -> Result<(), ParseError>,
    {
        let t1 = next_token!(self, "identifier", "(")?;

        if t1.is_ident() {
            on_type(&t1)?;
        } else if t1.is_left() {
            self.specific_ident("either")?;

            // Must have at least one either type.
            let t2 = next_token!(self, "identifier")?;
            if t2.is_ident() {
                on_type(&t2)?;
            } else {
                return expect!(self, t2, "identifier");
            }

            // Get the rest of the either parent types.
            loop {
                let t2 = next_token!(self, "identifier", ")")?;
                if t2.is_ident() {
                    on_type(&t2)?;
                } else if t2.is_right() {
                    return Ok(());
                } else {
                    return expect!(self, t2, "identifier", ")");
                }
            }
        } else {
            return expect!(self, t1, "identifier", "(");
        }
        Ok(())
    }

    /// `collect_types` is a more specific version for `type_declarations` that
    /// merely extracts and returns the collected `TypeId`s.
    fn collect_types(&mut self, types: &Types) -> Result<Vec<TypeId>, ParseError> {
        let mut type_ids: Vec<TypeId> = vec![];
        let src = self.contents;

        self.type_declarations(|t| {
            let name = t.to_str(src);
            if let Some(tid) = types.get(name) {
                type_ids.push(tid);
                return Ok(());
            }
            Err(ParseError::type_not_defined(t.line, t.col, name))
        })?;

        Ok(type_ids)
    }

    /// `balance_parens` consumes tokens until the current count of parenthesis
    /// reaches zero.  Initially, the count is one since it is expected that the
    /// first left paren has already been consumed.  On a successful balance then
    /// the first token that is consumed is returned.
    fn balance_parens(&mut self) -> Result<Token, ParseError> {
        // Here we have a custom token consumption function that only
        // reports end of input errors.  We want to skip over invalid
        // token input errors because we don't know what want to parse
        // as our sole goal is to find balancing parenthesis.  Later
        // at different parsing stage will these invalid tokens be
        // properly reported.  The Time token type was chosen arbitrarily
        // as this function only cares about left and right paren tokens.
        let mut next = || match self.next_token() {
            Ok(t) => Ok(t),
            Err(e) => match e {
                TokenError::EndOfInput { line: _, col: _ } => {
                    Err(ParseError::from_token_error(e, self.contents, vec![]))
                }
                TokenError::InvalidInput(te) => {
                    Ok(Token::new(TokenType::Time, te.pos, te.col, te.line))
                }
            },
        };

        let first = next()?;
        let mut tok = first;
        let mut count = 1;
        loop {
            if tok.is_left() {
                count += 1;
            } else if tok.is_right() {
                count -= 1;
                if count == 0 {
                    return Ok(first);
                }
            }
            tok = next()?;
        }
    }

    /// `predicates` parses the `:predicates` section of a PDDL domain.
    fn predicates(&mut self, types: &Types) -> Result<ParseResult, ParseError> {
        let mut result = ParseResult::with_name("");
        let mut pred_id = 0;
        let mut pred_map: HashMap<String, PredId> = HashMap::new();

        result.what = ParsingWhat::Predicates;

        let sig = self.signature(types)?;
        let key = sig.lookup_key();

        result.predicates.push(Predicate {
            id: pred_id,
            name: sig.name,
            params: sig.params,
        });
        pred_map.insert(key, pred_id);
        pred_id += 1;

        loop {
            self.check_next_token_is_one_of(&[TokenType::LParen, TokenType::RParen])?;
            if let Some(t) = self.last_token {
                if !t.is_left() {
                    break;
                }
            }

            let sig = self.signature(types)?;
            let key = sig.lookup_key();
            let mut new_pred = true;

            if let Some(&id) = pred_map.get(&key) {
                if sig.params.len() == result.predicates[id].params.len() {
                    new_pred = false;
                    for i in 0..sig.params.len() {
                        let p = &sig.params[i];
                        let param = &mut result.predicates[id].params[i];
                        param.types.extend_from_slice(&p.types);
                        param.types.sort();
                        param.types.dedup();
                    }
                }
            }

            if new_pred {
                result.predicates.push(Predicate {
                    id: pred_id,
                    name: sig.name,
                    params: sig.params,
                });
                pred_map.insert(key, pred_id);
                pred_id += 1;
            }
        }

        self.consume(TokenType::RParen)?;
        Ok(result)
    }

    /// `functions` parses the `:functions` section of a PDDL domain.
    fn functions(&mut self, types: &Types) -> Result<ParseResult, ParseError> {
        let mut func_id = 0;
        let mut funcs = Vec::<Function>::new();
        let mut func_ids = Vec::<FuncId>::new();
        let mut func_map: HashMap<String, FuncId> = HashMap::new();
        let mut parsed_types = false;

        loop {
            let sig = self.signature(types)?;
            let key = sig.lookup_key();
            let mut new_func = true;

            if let Some(&id) = func_map.get(&key) {
                if funcs[id].params.len() == sig.params.len() {
                    new_func = false;
                    func_ids.push(id);
                    for i in 0..sig.params.len() {
                        let p = &sig.params[i];
                        let param = &mut funcs[id].params[i];
                        param.types.extend_from_slice(&p.types);
                        param.types.sort();
                        param.types.dedup();
                    }
                }
            }

            if new_func {
                funcs.push(Function {
                    id: func_id,
                    name: sig.name,
                    params: sig.params,
                    return_types: vec![],
                    returns_number: false,
                });
                func_map.insert(key, func_id);
                func_ids.push(func_id);
                func_id += 1;
            }

            self.check_next_token_is_one_of(&[
                TokenType::Minus,
                TokenType::LParen,
                TokenType::RParen,
            ])?;

            if self.next_token_is(TokenType::RParen) {
                let tok = self.consume(TokenType::RParen)?;

                for &id in &func_ids {
                    funcs[id].returns_number = true;
                }

                let mut result = ParseResult::with_name("");
                result.functions = funcs;
                result.what = ParsingWhat::Functions;

                // If one or more functions isn't followed by a '-' to specify
                // the return type then it is implied that the return type is
                // 'number'.
                if !parsed_types && !self.has_requirement(Requirement::NumericFluents) {
                    return Err(ParseError::missing(
                        tok.line,
                        tok.col,
                        Requirement::NumericFluents,
                        "function(s)",
                    ));
                }

                return Ok(result);
            } else if self.next_token_is(TokenType::Minus) {
                parsed_types = true;

                let tok = self.check_next_is_one_of_or_ident(&["number", "("])?;
                let src = self.contents;

                if tok.to_str(src).eq_ignore_ascii_case("number") {
                    if !self.has_requirement(Requirement::NumericFluents) {
                        return Err(ParseError::missing(
                            tok.line,
                            tok.col,
                            Requirement::NumericFluents,
                            "function(s)",
                        ));
                    }
                    self.specific_ident("number")?;

                    for &id in &func_ids {
                        funcs[id].returns_number = true;
                    }
                    func_ids.clear();
                    continue;
                }

                if !self.has_requirement(Requirement::Typing) {
                    return Err(ParseError::missing(
                        tok.line,
                        tok.col,
                        Requirement::Typing,
                        "function(s)",
                    ));
                }

                if !self.has_requirement(Requirement::ObjectFluents) {
                    return Err(ParseError::missing(
                        tok.line,
                        tok.col,
                        Requirement::ObjectFluents,
                        "function(s)",
                    ));
                }

                let type_ids = self.collect_types(types)?;
                for &id in &func_ids {
                    funcs[id].return_types.extend_from_slice(&type_ids);
                    funcs[id].return_types.sort();
                    funcs[id].return_types.dedup();
                }
                func_ids.clear();
            } else {
                // Next token is a left paren thus another function.
                parsed_types = false;
            }
        }
    }

    /// `signature` parses the predicate or function signature
    /// found in either the :predicates or :functions section of the
    /// PDDL domain.
    fn signature(&mut self, types: &Types) -> Result<Signature, ParseError> {
        self.consume(TokenType::LParen)?;

        let ident = self.consume_ident()?.to_ascii_lowercase();
        let mut sig = Signature {
            name: ident,
            params: vec![],
        };
        // This marks the beginning of variable names that have
        // been parsed.  After the type(s) have been parsed it
        // should be set to the position of where the next variable
        // in the parameter list begins.  Every parameter from this
        // position to the end of sig.params will have whatever type
        // IDs appended to their ID list.
        let mut var_begin = 0;
        let mut var_names: Vec<&str> = vec![];

        'variables: loop {
            let tok = self.check_next_is_one_of_or_var(&[")"])?;
            self.last_token = None;

            if tok.is_right() {
                return Ok(sig);
            }

            let name = tok.to_str(self.contents);
            for n in &var_names {
                if n.eq_ignore_ascii_case(name) {
                    let s = format!("{} is a duplicated parameter", name);
                    return Err(self.semantic(&tok, &s));
                }
            }

            var_names.push(name);
            sig.params.push(Param::default());

            let tok = self.check_next_is_one_of_or_var(&["-", ")"])?;
            if self.next_token_is(TokenType::Minus) {
                if !self.has_requirement(Requirement::Typing) {
                    return Err(ParseError::missing(
                        tok.line,
                        tok.col,
                        Requirement::Typing,
                        ":types",
                    ));
                }

                let type_ids = self.collect_types(types)?;
                for i in var_begin..sig.params.len() {
                    let p = &mut sig.params[i];
                    p.types.extend_from_slice(&type_ids);
                    p.types.sort();
                    p.types.dedup();
                }
                var_begin = sig.params.len();
            }
        }
    }

    /// `constants` parses the `:constants` portion of the PDDL domain.
    fn constants(&mut self, types: &Types) -> Result<ParseResult, ParseError> {
        let mut const_id = 0;
        let mut consts: Vec<Constant> = vec![];
        let mut const_ids: Vec<ConstId> = vec![];
        let mut const_map: HashMap<String, ConstId> = HashMap::new();

        loop {
            self.check_next_is_one_of_or_ident(&[")"])?;
            if self.next_token_is(TokenType::RParen) {
                let mut result = ParseResult::with_name("");
                result.what = ParsingWhat::Constants;
                result.constants = consts;
                return Ok(result);
            }

            let ident = self.consume_ident()?.to_ascii_lowercase();
            if let Some(&id) = const_map.get(&ident) {
                const_ids.push(id);
            } else {
                consts.push(Constant {
                    id: const_id,
                    name: ident.clone(),
                    types: vec![],
                });
                const_map.insert(ident, const_id);
                const_ids.push(const_id);
                const_id += 1;
            }

            let tok = self.check_next_is_one_of_or_ident(&["-", ")"])?;

            if self.next_token_is(TokenType::Minus) {
                if !self.has_requirement(Requirement::Typing) {
                    return Err(ParseError::missing(
                        tok.line,
                        tok.col,
                        Requirement::Typing,
                        ":types",
                    ));
                }

                let type_ids = self.collect_types(types)?;
                for &id in &const_ids {
                    consts[id].types.extend_from_slice(&type_ids);
                    consts[id].types.sort();
                    consts[id].types.dedup();
                }
                const_ids.clear();
            }
        }
    }

    /// `action` parses an :action definition.  Note that the ActionId is not
    /// assigned.
    fn action(&mut self) -> Result<ParseResult, ParseError> {
        let name = self.next_ident()?;
        let mut action = Action::new(name.to_str(self.contents));
        let mut stack = ParamStack::new();

        self.specific_keyword(":parameters")?;
        stack.push(self.typed_list_variable()?);

        self.check_next_is_one_of(&[":precondition", ":effect", ")"])?;
        if self.next_keyword_is(":precondition") {
            action.precondition = self.pre_goal(&mut stack)?;
        }

        self.check_next_is_one_of(&[":effect", ")"])?;
        if self.next_keyword_is(":effect") {
            panic!("TODO: need to parse :action effects");
        }

        self.consume(TokenType::RParen)?;

        action.line = name.line;
        action.col = name.col;
        action.params = stack.pop().unwrap();

        let mut result = ParseResult::with_name("");
        result.what = ParsingWhat::Action;
        result.action = Some(action);

        Ok(result)
    }

    /// `typed_list_variable` returns the variable parameters that are associated with
    /// variable list declarations for :action parameters, forall goal, and other such
    /// constructs.  One or more variable parameters may or may not not have types.
    fn typed_list_variable(&mut self) -> Result<Vec<Param>, ParseError> {
        let mut params: Vec<Param> = vec![];

        self.consume(TokenType::LParen)?;
        'variables: loop {
            let tok = self.check_next_is_one_of_or_var(&[")"])?;
            self.last_token = None;

            if tok.is_right() {
                return Ok(params);
            }
            let mut param = Param::default();

            if let TokenType::Variable(s, e) = tok.what {
                param.start = s;
                param.end = e;
            }

            self.check_next_is_one_of_or_var(&["-", ")"])?;

            let types = &self.types.expect("no types for parsing");
            let type_ids = if self.next_token_is(TokenType::Minus) {
                self.collect_types(types)?
            } else {
                vec![]
            };

            let name = &self.contents[param.start..param.end];
            for p in &mut params {
                let prev = &self.contents[p.start..p.end];
                if prev.eq_ignore_ascii_case(name) {
                    p.types.extend_from_slice(&type_ids);
                    p.types.sort();
                    p.types.dedup();
                    continue 'variables;
                }
            }

            param.types = type_ids;
            param.types.sort();
            param.types.dedup();
            params.push(param);
        }
    }

    /// `pre_goal` parses a :precondition goal description.
    fn pre_goal(&mut self, stack: &mut ParamStack) -> Result<Option<Goal>, ParseError> {
        self.consume(TokenType::LParen)?;

        let tok = self.check_next_is_one_of_or_ident(&[
            "preference",
            "forall",
            "exists",
            "and",
            "or",
            "not",
            "imply",
            "=",
            ">",
            "<",
            ">=",
            "<=",
            ")",
        ])?;

        let result = if self.next_token_is(TokenType::RParen) {
            Ok(None)
        } else if self.next_ident_is("and") {
            self.check_next_token_is_one_of(&[TokenType::LParen, TokenType::RParen])?;

            if self.next_token_is(TokenType::RParen) {
                Ok(Some(Goal::And(vec![])))
            } else {
                let mut goals: Vec<Goal> = vec![];
                while let Some(g) = self.pre_goal(stack)? {
                    goals.push(g);
                }
                Ok(Some(Goal::And(goals)))
            }
        } else if self.next_ident_is("preference") {
            self.check_requirement(&tok, Requirement::Preferences, "preference goal")?;

            let t = self.check_next_is_one_of_or_ident(&["("])?;
            let s = if t.is_left() {
                "".to_string()
            } else {
                self.consume_ident()?.to_ascii_lowercase()
            };
            let g = Box::new(self.goal(stack)?);

            Ok(Some(Goal::Preference(s, g)))
        } else if self.next_ident_is("forall") {
            self.check_requirement(&tok, Requirement::UniversalPreconditions, "forall goal")?;

            stack.push(self.typed_list_variable()?);
            if let Some(g) = self.pre_goal(stack)? {
                let p = stack.pop().unwrap();
                Ok(Some(Goal::Forall(p, Box::new(g))))
            } else {
                Err(self.semantic(&tok, "forall condition missing valid goal description"))
            }
        } else if self.next_ident_is("exists") {
            self.check_requirement(&tok, Requirement::ExistentialPreconditions, "exists goal")?;

            stack.push(self.typed_list_variable()?);
            let g = self.goal(stack)?;
            let p = stack.pop().unwrap();
            Ok(Some(Goal::Exists(p, Box::new(g))))
        } else if self.next_ident_is("not") {
            let g = self.goal(stack)?;

            if let Goal::Pred(_, _) = &g {
                self.check_requirement(&tok, Requirement::NegativePreconditions, "not goal")?;
            } else if let Goal::EqualTerms(_, _) = &g {
                self.check_requirement(&tok, Requirement::NegativePreconditions, "not goal")?;
            } else {
                self.check_requirement(&tok, Requirement::DisjunctivePreconditions, "not goal")?;
            }
            Ok(Some(Goal::Not(Box::new(g))))
        } else if self.next_ident_is("or") {
            self.check_requirement(&tok, Requirement::DisjunctivePreconditions, "or goal")?;
            self.check_next_token_is_one_of(&[TokenType::LParen, TokenType::RParen])?;

            if self.next_token_is(TokenType::RParen) {
                Ok(Some(Goal::Or(vec![])))
            } else {
                let mut goals: Vec<Goal> = vec![];
                while let Some(g) = self.pre_goal(stack)? {
                    goals.push(g);
                }
                Ok(Some(Goal::Or(goals)))
            }
        } else if self.next_ident_is("imply") {
            self.check_requirement(&tok, Requirement::DisjunctivePreconditions, "imply goal")?;

            let ant = Box::new(self.goal(stack)?);
            let con = Box::new(self.goal(stack)?);

            Ok(Some(Goal::Imply(ant, con)))
        } else if self.next_token_is(TokenType::Equal) {
            Ok(Some(self.equality(&tok, stack)?))
        } else if self.next_token_is(TokenType::Greater) {
            self.check_requirement(&tok, Requirement::NumericFluents, "> goal")?;

            let lexp = if let Some(exp) = self.fexp(stack)? {
                exp
            } else {
                return Err(self.semantic(&tok, "> operator requires two expression but has none"));
            };
            let rexp = if let Some(exp) = self.fexp(stack)? {
                exp
            } else {
                return Err(self.semantic(&tok, "> operator requires two expression but has one"));
            };

            Ok(Some(Goal::Greater(lexp, rexp)))
        } else if self.next_token_is(TokenType::GreaterEq) {
            self.check_requirement(&tok, Requirement::NumericFluents, ">= goal")?;

            let lexp = if let Some(exp) = self.fexp(stack)? {
                exp
            } else {
                return Err(self.semantic(&tok, "> operator requires two expression but has none"));
            };
            let rexp = if let Some(exp) = self.fexp(stack)? {
                exp
            } else {
                return Err(self.semantic(&tok, "> operator requires two expression but has one"));
            };

            Ok(Some(Goal::GreaterEq(lexp, rexp)))
        } else if self.next_token_is(TokenType::Less) {
            self.check_requirement(&tok, Requirement::NumericFluents, "< goal")?;

            let lexp = if let Some(exp) = self.fexp(stack)? {
                exp
            } else {
                return Err(self.semantic(&tok, "> operator requires two expression but has none"));
            };
            let rexp = if let Some(exp) = self.fexp(stack)? {
                exp
            } else {
                return Err(self.semantic(&tok, "> operator requires two expression but has one"));
            };
            Ok(Some(Goal::Less(lexp, rexp)))
        } else if self.next_token_is(TokenType::LessEq) {
            self.check_requirement(&tok, Requirement::NumericFluents, "<= goal")?;

            let lexp = if let Some(exp) = self.fexp(stack)? {
                exp
            } else {
                return Err(self.semantic(&tok, "> operator requires two expression but has none"));
            };
            let rexp = if let Some(exp) = self.fexp(stack)? {
                exp
            } else {
                return Err(self.semantic(&tok, "> operator requires two expression but has one"));
            };
            Ok(Some(Goal::LessEq(lexp, rexp)))
        } else {
            let name = self.consume_ident()?;
            let mut terms: Vec<Term> = vec![];
            let mut tokens: Vec<Token> = vec![];

            while let Some(t) = self.term(stack)? {
                terms.push(t.what);
                tokens.push(t.tok);
            }
            let p = self.get_pred(&tok, &name, &terms)?;
            for i in 0..terms.len() {
                let ttypes = self.term_types(&terms[i]);
                let ptypes = &p.params[i].types;
                self.check_subset_types(&tokens[i], ttypes, ptypes)?;
            }
            Ok(Some(Goal::Pred(p.id, terms)))
        };
        self.consume(TokenType::RParen)?;

        result
    }

    /// `goal` parses a general goal description.
    fn goal(&mut self, stack: &mut ParamStack) -> Result<Goal, ParseError> {
        self.consume(TokenType::LParen)?;

        let tok = self.check_next_is_one_of_or_ident(&[
            "forall", "exists", "and", "or", "not", "imply", "=", ">", "<", ">=", "<=",
        ])?;

        let result = if self.next_ident_is("and") {
            let mut goals: Vec<Goal> = vec![];
            loop {
                self.check_next_token_is_one_of(&[TokenType::LParen, TokenType::RParen])?;

                if self.next_token_is(TokenType::RParen) {
                    break;
                } else {
                    goals.push(self.goal(stack)?);
                }
            }
            Ok(Goal::And(goals))
        } else if self.next_ident_is("forall") {
            self.check_requirement(&tok, Requirement::UniversalPreconditions, "forall goal")?;

            stack.push(self.typed_list_variable()?);
            let g = Box::new(self.goal(stack)?);
            let p = stack.pop().unwrap();
            Ok(Goal::Forall(p, g))
        } else if self.next_ident_is("exists") {
            self.check_requirement(&tok, Requirement::ExistentialPreconditions, "exists goal")?;

            stack.push(self.typed_list_variable()?);
            let g = Box::new(self.goal(stack)?);
            let p = stack.pop().unwrap();
            Ok(Goal::Exists(p, g))
        } else if self.next_ident_is("not") {
            let g = self.goal(stack)?;

            if let Goal::Pred(_, _) = &g {
                self.check_requirement(&tok, Requirement::NegativePreconditions, "not goal")?;
            } else if let Goal::EqualTerms(_, _) = &g {
                self.check_requirement(&tok, Requirement::NegativePreconditions, "not goal")?;
            } else {
                self.check_requirement(&tok, Requirement::DisjunctivePreconditions, "not goal")?;
            }
            Ok(Goal::Not(Box::new(g)))
        } else if self.next_ident_is("or") {
            self.check_requirement(&tok, Requirement::DisjunctivePreconditions, "or goal")?;

            let mut goals: Vec<Goal> = vec![];
            loop {
                self.check_next_token_is_one_of(&[TokenType::LParen, TokenType::RParen])?;

                if self.next_token_is(TokenType::RParen) {
                    break;
                } else {
                    goals.push(self.goal(stack)?);
                }
            }
            Ok(Goal::Or(goals))
        } else if self.next_ident_is("imply") {
            self.check_requirement(&tok, Requirement::DisjunctivePreconditions, "imply goal")?;

            let ant = Box::new(self.goal(stack)?);
            let con = Box::new(self.goal(stack)?);

            Ok(Goal::Imply(ant, con))
        } else if self.next_token_is(TokenType::Equal) {
            Ok(self.equality(&tok, stack)?)
        } else if self.next_token_is(TokenType::Greater) {
            self.check_requirement(&tok, Requirement::NumericFluents, "> goal")?;

            let lexp = if let Some(exp) = self.fexp(stack)? {
                exp
            } else {
                return Err(self.semantic(&tok, "> operator requires two expression but has none"));
            };
            let rexp = if let Some(exp) = self.fexp(stack)? {
                exp
            } else {
                return Err(self.semantic(&tok, "> operator requires two expression but has one"));
            };
            Ok(Goal::Greater(lexp, rexp))
        } else if self.next_token_is(TokenType::GreaterEq) {
            self.check_requirement(&tok, Requirement::NumericFluents, ">= goal")?;

            let lexp = if let Some(exp) = self.fexp(stack)? {
                exp
            } else {
                return Err(self.semantic(&tok, "> operator requires two expression but has none"));
            };
            let rexp = if let Some(exp) = self.fexp(stack)? {
                exp
            } else {
                return Err(self.semantic(&tok, "> operator requires two expression but has one"));
            };
            Ok(Goal::Greater(lexp, rexp))
        } else if self.next_token_is(TokenType::Less) {
            self.check_requirement(&tok, Requirement::NumericFluents, "< goal")?;

            let lexp = if let Some(exp) = self.fexp(stack)? {
                exp
            } else {
                return Err(self.semantic(&tok, "> operator requires two expression but has none"));
            };
            let rexp = if let Some(exp) = self.fexp(stack)? {
                exp
            } else {
                return Err(self.semantic(&tok, "> operator requires two expression but has one"));
            };
            Ok(Goal::Less(lexp, rexp))
        } else if self.next_token_is(TokenType::LessEq) {
            self.check_requirement(&tok, Requirement::NumericFluents, "<= goal")?;

            let lexp = if let Some(exp) = self.fexp(stack)? {
                exp
            } else {
                return Err(self.semantic(&tok, "> operator requires two expression but has none"));
            };
            let rexp = if let Some(exp) = self.fexp(stack)? {
                exp
            } else {
                return Err(self.semantic(&tok, "> operator requires two expression but has one"));
            };
            Ok(Goal::LessEq(lexp, rexp))
        } else {
            let name = self.consume_ident()?;
            let mut terms: Vec<Term> = vec![];
            let mut tokens: Vec<Token> = vec![];

            while let Some(t) = self.term(stack)? {
                terms.push(t.what);
                tokens.push(t.tok);
            }
            let p = self.get_pred(&tok, &name, &terms)?;
            for i in 0..terms.len() {
                let ttypes = self.term_types(&terms[i]);
                let ptypes = &p.params[i].types;
                self.check_subset_types(&tokens[i], ttypes, ptypes)?;
            }
            Ok(Goal::Pred(p.id, terms))
        };
        self.consume(TokenType::RParen)?;

        result
    }

    fn equality(&mut self, eqtok: &Token, stack: &mut ParamStack) -> Result<Goal, ParseError> {
        let left = next_token!(self, "number", "identifier", "variable", "(")?;
        let mut left_term = Term::Const(0);
        let mut left_fexp = Fexp::Number(0.0);
        let mut left_side_is_term = false;

        if left.is_left() {
            match self.term_or_fexp(stack)? {
                Ok(t) => {
                    left_term = t;
                    left_side_is_term = true;
                    // It's unknown if the left side is a term if the Term is
                    // is function reference.
                    if let Term::Func(_, _) = &left_term {
                        left_side_is_term = false;
                    }
                }
                Err(f) => left_fexp = f,
            }
        } else if left.is_var() {
            left_side_is_term = true;

            let var = left.to_str(self.contents);
            if let Some(p) = stack.find(self.contents, var) {
                left_term = Term::Var(p.types.clone());
            } else {
                let s = format!("variable, {}, not defined", var);
                return Err(self.semantic(&left, &s));
            }
        } else if left.is_ident() {
            let name = left.to_str(self.contents).to_ascii_lowercase();
            if let Some(&id) = self.const_map.unwrap().get(&name) {
                left_side_is_term = true;
                left_term = Term::Const(id);
            } else {
                left_fexp = Fexp::FnSymbol(name);
            }
        } else if let TokenType::Number(val, _, _) = left.what {
            left_fexp = Fexp::Number(val);
        } else {
            return expect!(self, left, "identifier", "*", "+", "/", "-",);
        }

        let result = if left_side_is_term {
            self.check_requirement(&eqtok, Requirement::Equality, "= goal")?;

            if let Some(info) = self.term(stack)? {
                Ok(Goal::EqualTerms(left_term, info.what))
            } else {
                Err(self.semantic(&eqtok, "= needs requires terms but has one"))
            }
        } else if left_term.is_func() {
            match self.term_or_fexp(stack)? {
                Ok(right_term) => {
                    if let Term::Func(right_id, right_terms) = right_term {
                        let left_id: FuncId;
                        let left_terms: Vec<Term>;

                        if let Term::Func(id, terms) = left_term {
                            left_id = id;
                            left_terms = terms;
                        } else {
                            panic!("Term::is_func() doesn't match correctly");
                        }

                        let funcs = self.functions.unwrap();
                        let left_fn = &funcs[left_id];
                        let right_fn = &funcs[right_id];
                        let ltypes = &left_fn.return_types;
                        let rtypes = &right_fn.return_types;

                        if left_fn.returns_number && right_fn.returns_number {
                            self.check_requirement(&eqtok, Requirement::NumericFluents, "= goal")?;
                            let lexp = Fexp::Func(left_id, left_terms);
                            let rexp = Fexp::Func(right_id, right_terms);
                            Ok(Goal::EqualFexps(lexp, rexp))
                        } else if ltypes.len() > 0 && rtypes.len() > 0 {
                            self.check_requirement(&eqtok, Requirement::ObjectFluents, "= goal")?;
                            let lterm = Term::Func(left_id, left_terms);
                            let rterm = Term::Func(right_id, right_terms);
                            Ok(Goal::EqualTerms(lterm, rterm))
                        } else {
                            let s = "left and right functions both don't return either both numbers or both objects";
                            Err(self.semantic(eqtok, s))
                        }
                    } else {
                        self.check_requirement(&eqtok, Requirement::ObjectFluents, "= goal")?;
                        Ok(Goal::EqualTerms(left_term, right_term))
                    }
                }
                Err(f) => {
                    let left_id: FuncId;
                    let left_terms: Vec<Term>;

                    if let Term::Func(id, terms) = left_term {
                        left_id = id;
                        left_terms = terms;
                    } else {
                        panic!("Term::is_fun() doesn't match correctly");
                    }
                    let func = Fexp::Func(left_id, left_terms);
                    Ok(Goal::EqualFexps(func, f))
                }
            }
        } else {
            self.check_requirement(&eqtok, Requirement::NumericFluents, "= goal")?;

            if let Some(rexp) = self.fexp(stack)? {
                Ok(Goal::EqualFexps(left_fexp, rexp))
            } else {
                Err(self.semantic(&eqtok, "= requires two f-exp but has one"))
            }
        };

        match &result {
            Ok(Goal::EqualTerms(lterm, rterm)) => {
                let ltypes = self.term_types(lterm);
                let rtypes = self.term_types(rterm);
                if let Err(_) = self.check_subset_types(&eqtok, ltypes, rtypes) {
                    return Err(
                        self.semantic(eqtok, "left and right terms don't have compatible types")
                    );
                }
            }
            _ => (),
        }
        result
    }

    fn fexp(&mut self, stack: &mut ParamStack) -> Result<Option<Fexp>, ParseError> {
        let tok = next_token!(self, "number", "identifier", "(", ")")?;

        if tok.is_right() {
            Ok(None)
        } else if tok.is_left() {
            let tok = next_token!(self, "identifier", "*", "+", "/", "-")?;

            if tok.is_ident() {
                let mut terms: Vec<Term> = vec![];
                let mut tokens: Vec<Token> = vec![];

                while let Some(t) = self.term(stack)? {
                    terms.push(t.what);
                    tokens.push(t.tok);
                }
                let name = tok.to_str(self.contents);
                let func = self.get_func(&tok, &name, &terms)?;

                for i in 0..terms.len() {
                    let ttypes = self.term_types(&terms[i]);
                    let ftypes = &func.params[i].types;
                    self.check_subset_types(&tokens[i], ttypes, ftypes)?;
                }
                let id = func.id;

                self.consume(TokenType::RParen)?;
                Ok(Some(Fexp::Func(id, terms)))
            } else if tok.what == TokenType::Mult
                || tok.what == TokenType::Plus
                || tok.what == TokenType::Div
                || tok.what == TokenType::Minus
            {
                let lexp = if let Some(exp) = self.fexp(stack)? {
                    exp
                } else {
                    let n = tok.to_str(self.contents);
                    let s = format!("expecting f-exp after {} but found none", n);
                    return Err(self.semantic(&tok, &s));
                };

                match tok.what {
                    TokenType::Mult => {
                        let mut rest: Vec<Fexp> = vec![];
                        while let Some(exp) = self.fexp(stack)? {
                            rest.push(exp);
                        }
                        Ok(Some(Fexp::Mult(Box::new(lexp), rest)))
                    }
                    TokenType::Plus => {
                        let mut rest: Vec<Fexp> = vec![];
                        while let Some(exp) = self.fexp(stack)? {
                            rest.push(exp);
                        }
                        Ok(Some(Fexp::Add(Box::new(lexp), rest)))
                    }
                    TokenType::Div => {
                        if let Some(rexp) = self.fexp(stack)? {
                            Ok(Some(Fexp::Div(Box::new(lexp), Box::new(rexp))))
                        } else {
                            return Err(self.semantic(
                                &tok,
                                "expecting second f-exp for / operator but found none",
                            ));
                        }
                    }
                    TokenType::Minus => {
                        if let Some(rexp) = self.fexp(stack)? {
                            Ok(Some(Fexp::Sub(Box::new(lexp), Box::new(rexp))))
                        } else {
                            Ok(Some(Fexp::Neg(Box::new(lexp))))
                        }
                    }
                    _ => expect!(self, tok, "identifier", "*", "+", "/", "-"),
                }
            } else {
                expect!(self, tok, "identifier", "*", "+", "/", "-")
            }
        } else if tok.is_ident() {
            let sym = tok.to_str(self.contents).to_ascii_lowercase();
            Ok(Some(Fexp::FnSymbol(sym)))
        } else if let TokenType::Number(num, _, _) = tok.what {
            Ok(Some(Fexp::Number(num)))
        } else {
            expect!(self, tok, "number", "identifier", "(", ")")
        }
    }

    /// `term` parses a predicate or function term (i.e. argument).
    fn term(&mut self, stack: &mut ParamStack) -> Result<Option<TermInfo>, ParseError> {
        let tok = next_token!(self, "identifier", "variable", "(", ")")?;
        let result: Term;

        if tok.is_right() {
            return Ok(None);
        } else if tok.is_ident() {
            let n = tok.to_str(self.contents);
            let c = self.get_const(&tok, n)?;
            result = Term::Const(c.id);
        } else if tok.is_var() {
            let var = tok.to_str(self.contents);
            if let Some(p) = stack.find(self.contents, var) {
                result = Term::Var(p.types.clone());
            } else {
                let s = format!("variable, {}, not defined", var);
                return Err(self.semantic(&tok, &s));
            }
        } else if tok.is_left() {
            let tok = self.next_ident()?;
            let mut terms: Vec<Term> = vec![];
            let mut tokens: Vec<Token> = vec![];

            self.check_requirement(&tok, Requirement::ObjectFluents, "function term")?;

            while let Some(t) = self.term(stack)? {
                terms.push(t.what);
                tokens.push(t.tok);
            }
            let name = tok.to_str(self.contents);
            let func = self.get_func(&tok, &name, &terms)?;

            for i in 0..terms.len() {
                let ttypes = self.term_types(&terms[i]);
                let ftypes = &func.params[i].types;
                self.check_subset_types(&tokens[i], ttypes, ftypes)?;
            }

            result = Term::Func(func.id, terms);
            self.consume(TokenType::RParen)?;
        } else {
            return expect!(self, tok, "identifier", "variable", "(", ")");
        };

        Ok(Some(TermInfo { what: result, tok }))
    }

    /// `term_types` returns the `TypeId`s that are associated with the
    /// given `term`.
    fn term_types(&self, term: &'a Term) -> &'a [TypeId] {
        match term {
            Term::Var(vtypes) => &vtypes,
            Term::Const(id) => {
                let s = &self.constants.unwrap();
                let c = &s[*id];
                &c.types
            }
            Term::Func(id, _) => {
                let s = &self.functions.unwrap();
                let f = &s[*id];
                &f.return_types
            }
        }
    }

    fn term_or_fexp(&mut self, stack: &mut ParamStack) -> Result<Result<Term, Fexp>, ParseError> {
        let tok = next_token!(self, "identifier", "*", "+", "/", "-",)?;

        if tok.is_ident() {
            let mut terms: Vec<Term> = vec![];
            let mut tokens: Vec<Token> = vec![];

            while let Some(t) = self.term(stack)? {
                terms.push(t.what);
                tokens.push(t.tok);
            }
            let name = tok.to_str(self.contents);
            let func = self.get_func(&tok, &name, &terms)?;

            for i in 0..terms.len() {
                let ttypes = self.term_types(&terms[i]);
                let ftypes = &func.params[i].types;
                self.check_subset_types(&tokens[i], ttypes, ftypes)?;
            }
            let id = func.id;

            self.consume(TokenType::RParen)?;
            Ok(Ok(Term::Func(id, terms)))
        } else if tok.what == TokenType::Mult
            || tok.what == TokenType::Plus
            || tok.what == TokenType::Div
            || tok.what == TokenType::Minus
        {
            let lexp = if let Some(exp) = self.fexp(stack)? {
                exp
            } else {
                let n = tok.to_str(self.contents);
                let s = format!("expecting f-exp after {} but found none", n);
                return Err(self.semantic(&tok, &s));
            };

            match tok.what {
                TokenType::Mult => {
                    let mut rest: Vec<Fexp> = vec![];
                    while let Some(exp) = self.fexp(stack)? {
                        rest.push(exp);
                    }
                    Ok(Err(Fexp::Mult(Box::new(lexp), rest)))
                }
                TokenType::Plus => {
                    let mut rest: Vec<Fexp> = vec![];
                    while let Some(exp) = self.fexp(stack)? {
                        rest.push(exp);
                    }
                    Ok(Err(Fexp::Add(Box::new(lexp), rest)))
                }
                TokenType::Div => {
                    if let Some(rexp) = self.fexp(stack)? {
                        Ok(Err(Fexp::Div(Box::new(lexp), Box::new(rexp))))
                    } else {
                        return Err(self.semantic(
                            &tok,
                            "expecting second f-exp for / operator but found none",
                        ));
                    }
                }
                TokenType::Minus => {
                    if let Some(rexp) = self.fexp(stack)? {
                        Ok(Err(Fexp::Sub(Box::new(lexp), Box::new(rexp))))
                    } else {
                        Ok(Err(Fexp::Neg(Box::new(lexp))))
                    }
                }
                _ => expect!(self, tok, "identifier", "*", "+", "/", "-"),
            }
        } else {
            expect!(self, tok, "identifier", "*", "+", "/", "-")
        }
    }

    /// `check_subset_types` checks if any `TypeId` of `kids` is one or
    /// or an ancestor of `parents`.
    fn check_subset_types(
        &self,
        tok: &Token,
        kids: &[TypeId],
        parents: &[TypeId],
    ) -> Result<(), ParseError> {
        let types = &self.types.unwrap();
        for &k in kids {
            for &p in parents {
                if k == p || types.is_child_an_ancestor_of(k, p) {
                    return Ok(());
                }
            }
        }
        let name = tok.to_str(self.contents);
        let mut tnames: Vec<&str> = vec![];

        for &id in parents {
            tnames.push(types.name_of(id));
        }
        let s = format!(
            "none of the types for {} are one of or a subtype of {:?}",
            name, tnames
        );
        Err(self.semantic(tok, &s))
    }
}

/// `ParamStack` maintains a stack of `Param` lists which are built
/// during the parsing of an `:action`, `forall` goal, `exists` goal,
/// etc.  As parameter list are added, parameters will shadow previous
/// parameters of the same name earlier in the stack.
struct ParamStack {
    params: Vec<Vec<Param>>,
}

impl ParamStack {
    fn new() -> Self {
        ParamStack { params: vec![] }
    }

    fn push(&mut self, p: Vec<Param>) {
        self.params.push(p);
    }

    fn pop(&mut self) -> Option<Vec<Param>> {
        self.params.pop()
    }

    fn find(&self, src: &str, var: &str) -> Option<&Param> {
        for params in self.params.iter().rev() {
            for p in params {
                let name = &src[p.start..p.end];
                if name.eq_ignore_ascii_case(var) {
                    return Some(p);
                }
            }
        }
        None
    }
}

/// `Signature` encapsulates the parsed result of a predicate or
/// function declaration (i.e. '(foo ?a ?b - object ?c - (either bar baz))' ).
struct Signature {
    name: String,       // Name of the predicate or function (e.g. 'foo').
    params: Vec<Param>, // Parameters of the declaration (e.g. '?a', '?b', etc.).
}

impl Signature {
    /// `lookup_key` returns a key that can be used to see if the Signature
    /// has already been declared.
    fn lookup_key(&self) -> String {
        Self::create_key(&self.name, self.params.len())
    }

    /// `create_key` returns a key that can be used to check if two different
    /// signatures match.  The key will be a combination of the signatures's
    /// name along with its parameter arity and is composed of characters that is
    /// impossible to be a valid identifier.
    fn create_key(name: &str, arity: usize) -> String {
        format!("{}-**-{}-**-", name, arity)
    }
}

/// `Types` is the collection of all types found from `:types` section
/// within a PDDL domain.
#[derive(Debug)]
struct Types {
    types: HashMap<String, TypeId>, // Lowercased type names to their assigned TypeId.
    names: Vec<String>,             // Lowercased names ordered by TypeId.
    parent_types: Vec<HashSet<TypeId>>, // Immediate parent TypeIds.  Vector is indexed by the child TypeId.
    child_types: Vec<HashSet<TypeId>>, // Immediate child TypeIds.  Vector is indexed by the parent TypeId.
    type_id: TypeId,                   // A TypeId counter.
}

impl Default for Types {
    fn default() -> Self {
        Types {
            types: HashMap::new(),
            names: vec![],
            type_id: 0,
            parent_types: vec![],
            child_types: vec![],
        }
    }
}

impl Types {
    /// `get` returns the `TypeId` of the lowercase form of `name`
    /// if it exists.
    fn get(&self, name: &str) -> Option<TypeId> {
        let n = name.to_ascii_lowercase();
        self.types.get(&n).map(|&id| id)
    }

    /// `name_of` returns the type name for of the given `id`.
    fn name_of(&self, id: TypeId) -> &str {
        &self.names[id]
    }

    /// `insert` inserts `s` and assigns it a `TypeId` if it hasn't already
    /// been seen.
    fn insert(&mut self, s: &str) -> TypeId {
        let id = s.to_ascii_lowercase();
        if self.types.contains_key(&id) {
            *self.types.get(&id).unwrap()
        } else {
            let tid = self.type_id;
            self.names.push(id.clone());
            self.types.insert(id, tid);
            self.type_id += 1;
            self.parent_types.push(HashSet::new());
            self.child_types.push(HashSet::new());
            tid
        }
    }

    /// `insert_parent` inserts `parent` into `child`'s immediate parent `TypeId` set.
    fn insert_parent(&mut self, child: TypeId, parent: TypeId) {
        self.parent_types[child].insert(parent);
    }

    /// `insert_child` inserts `child` into `parent`'s immediate child `TypeId` set.
    fn insert_child(&mut self, parent: TypeId, child: TypeId) {
        self.child_types[parent].insert(child);
    }

    /// `has_circular_types` returns true if `id` ends up inheriting from itself.
    fn has_circular_types(&self, id: TypeId) -> bool {
        let pt = &self.parent_types[id];
        if pt.contains(&id) {
            true
        } else {
            let mut any = false;
            for &pid in pt.iter() {
                any = any || self.check_circular_parent(id, pid);
            }
            any
        }
    }

    /// `check_circular_parent` is a helper function for `has_circular_types`.
    fn check_circular_parent(&self, child: TypeId, parent: TypeId) -> bool {
        let pt = &self.parent_types[parent];
        if pt.contains(&child) {
            true
        } else {
            let mut any = false;
            for &pid in pt.iter() {
                any = any || self.check_circular_parent(child, pid);
            }
            any
        }
    }

    /// `is_child_an_ancestor_of` returns true if `child` is an ancestor
    /// of `parent`.
    fn is_child_an_ancestor_of(&self, child: TypeId, parent: TypeId) -> bool {
        let ct = &self.child_types[parent];
        if ct.contains(&child) {
            true
        } else {
            for &id in ct.iter() {
                if self.is_child_an_ancestor_of(child, id) {
                    return true;
                }
            }
            false
        }
    }
}

/// `ParseResult` encompasses a result returned from of the different
/// methods of a `DomainParser`.
#[derive(Debug)]
struct ParseResult<'a> {
    what: ParsingWhat,          // What was parsed by this result.
    name: &'a str,              // Name of a domain.
    reqs: u32,                  // Requirements of the domain represented as bit vector.
    types: Types,               // Types extracted from the domain.
    const_loc: Token,           // Token within the PDDL source where constants are located.
    pred_loc: Token,            // Token within the PDDL source where predicates are located.
    func_loc: Token,            // Token within the PDDL source where functions are located.
    constraints: Token,         // Token within the PDDL source where constraints are located.
    action_locs: Vec<Token>,    // Tokens where :actions begin in the PDDL source.
    duratives: Vec<Token>,      // Tokens where :durative-actions begin in the PDDL source.
    deriveds: Vec<Token>,       // Tokens where :derived functions begin in the PDDL source.
    predicates: Vec<Predicate>, // Parsed predicate declarations.
    functions: Vec<Function>,   // Parsed function declarations.
    constants: Vec<Constant>,   // Parsed constant declarations.
    action: Option<Action>,     // Parsed action definition.
}

impl<'a> ParseResult<'a> {
    /// `with_name` returns a ParseResult that has a name of `name`.  All
    /// other fields have their zero value.
    fn with_name(name: &'a str) -> ParseResult<'a> {
        ParseResult {
            name,
            what: ParsingWhat::Any,
            reqs: 0,
            types: Types::default(),
            const_loc: Token::default(),
            pred_loc: Token::default(),
            func_loc: Token::default(),
            constraints: Token::default(),
            action_locs: vec![],
            duratives: vec![],
            deriveds: vec![],
            predicates: vec![],
            functions: vec![],
            constants: vec![],
            action: None,
        }
    }

    /// `add_requirements` adds the requirements of the `reqs` bit vector
    /// to the requirements contained within the `ParseResult`.
    fn add_requirements(&mut self, reqs: u32) {
        self.reqs = self.reqs | reqs
    }

    /// `has_requirement` returns true if this `ParseResult` has the requirement
    /// of `r`.
    fn has_requirement(&self, r: Requirement) -> bool {
        let b = self.reqs & (1 << r.index());
        if r == Requirement::Strips {
            return self.reqs == 0 || b > 0;
        }
        b > 0
    }
}

/// `ParseError` is the error returned from parsing a PDDL domain.
#[derive(Debug, PartialEq)]
pub struct ParseError {
    /// The specific parse error that occurred.
    pub what: ParseErrorType,
    /// The line number the error occurred on.
    pub line: usize,
    /// The column number the error occurred on.
    pub col: usize,
}

impl ParseError {
    /// `expect` returns a `ParseError` for an error that occurred
    /// on line, `line`, column, `col`, and has a value of `have` where
    /// `expect` are the expected values at the time of parse.
    fn expect(line: usize, col: usize, have: &str, expect: Vec<&str>) -> ParseError {
        let have = have.to_string();
        let expect = expect.iter().map(|s| s.to_string()).collect();
        let what = ParseErrorType::Expect { have, expect };
        ParseError { what, line, col }
    }

    /// `from_token_error` converts a `TokenError` into a `ParseError`.  `contents`
    /// are the original source contents of the `DomainParser` and `expecting` is
    /// are the values that were expected at the time of the parse.
    fn from_token_error(e: TokenError, contents: &str, expecting: Vec<&str>) -> ParseError {
        match e {
            TokenError::EndOfInput { line, col } => {
                ParseError::expect(line, col, "end of input", expecting)
            }
            TokenError::InvalidInput(te) => {
                let s = te.to_string(contents);
                ParseError::expect(te.line, te.col, s, expecting)
            }
        }
    }

    /// `missing` returns a `ParserError` where the requirement is missing
    /// for `reason`.
    fn missing(line: usize, col: usize, req: Requirement, what: &str) -> ParseError {
        let what = what.to_string();
        let what = ParseErrorType::MissingRequirement { req, what };
        ParseError { what, line, col }
    }

    /// `semantic` returns a `ParseError` that represents some semantic
    /// error in the PDDL language (i.e. predicate not defined).
    fn semantic(line: usize, col: usize, what: &str) -> ParseError {
        let what = ParseErrorType::SemanticError(what.to_string());
        ParseError { what, line, col }
    }

    /// `type_not_defined` returns a `ParseError` where `what` was declared
    /// as a type but wasn't defined within the `:types` section of the
    /// PDDL domain.
    fn type_not_defined(line: usize, col: usize, what: &str) -> ParseError {
        let what = ParseErrorType::TypeNotDefined(what.to_string());
        ParseError { what, line, col }
    }
}

impl error::Error for ParseError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: error: {}", self.line, self.col, self.what)
    }
}

/// `ParseErrorType` are the different type of `ParseError`s that
/// can occur during parsing a PDDL domain.
#[derive(Debug, PartialEq)]
pub enum ParseErrorType {
    /// Where the parser expected a specific token but received something else.
    Expect { have: String, expect: Vec<String> },
    /// Signals that extra input was detected at the end of the PDDL domain.
    ExtraInput(String),
    /// Signals that a `Requirement` is missing for a specific construct which
    /// is described by the second parameter.
    MissingRequirement { req: Requirement, what: String },
    /// Signals a semantic error that has occurred.
    SemanticError(String),
    /// A type declared was not defined within the :types section.
    TypeNotDefined(String),
}

impl fmt::Display for ParseErrorType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseErrorType::Expect { have, expect } => {
                f.write_str("Expecting ")?;

                if expect.len() == 1 {
                    write!(f, "{}, found {}", expect[0], have)
                } else {
                    f.write_str("either ")?;

                    let end = expect.len() - 1;
                    for i in 0..end {
                        write!(f, "{}, ", expect[i])?;
                    }
                    write!(f, "or {}, found {}", expect[end], have)
                }
            }
            ParseErrorType::ExtraInput(s) => write!(f, "Extra input detected: {}", s),
            ParseErrorType::SemanticError(what) => write!(f, "{}", what),
            ParseErrorType::MissingRequirement { req, what } => write!(
                f,
                "{} requires {} declaration in :requirements section",
                what, req
            ),
            ParseErrorType::TypeNotDefined(t) => {
                write!(f, "Type, {}, is not defined within :types", t)
            }
        }
    }
}
