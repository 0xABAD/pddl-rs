pub mod scanner;
pub mod types;

mod parser;
mod reqs;

#[cfg(test)]
mod problem_test;

#[cfg(test)]
mod test;

use self::{
    parser::{Parse, Parser, ParsingWhat},
    reqs::Reqs,
    scanner::{Scanner, Token, TokenType},
    types::{TypeId, Types},
};

pub use self::{
    parser::{Error, ErrorType},
    reqs::Requirement,
};

use rayon::prelude::*;
use std::collections::HashSet;

pub type Errors = Vec<Error>;

/// `Domain` represents the final output from parsing the contents
/// representing some PDDL domain.
pub struct Domain {
    /// The parsed domain name.
    pub name: String,

    types: Types,               // Parsed (:types).
    reqs: Reqs,                 // Parsed (:requirements).
    predicates: Vec<Predicate>, // Parsed (:predicates) ordered by PredId.
    functions: Vec<Function>,   // Parsed (:functions) ordered by FuncId.
    constants: Vec<Constant>,   // Parsed (:constants) ordered by ConstId.
    actions: Vec<Action>,       // Parsed (:action ...) definitions.
}

impl Default for Domain {
    fn default() -> Self {
        Domain {
            name: "".to_string(),
            reqs: Reqs::default(),
            types: Types::default(),
            predicates: vec![],
            functions: vec![],
            constants: vec![],
            actions: vec![],
        }
    }
}

impl Domain {
    /// `is_domain` return true if `src` represents a PDDL domain.
    /// Only the first few tokens of `src` is paresed to make this
    /// determination.
    pub fn is_domain(src: &str) -> bool {
        let mut lex = Scanner::new(src);

        let is_ident = |t: &Token, ident| {
            t.what == TokenType::Ident && t.to_str(src).eq_ignore_ascii_case(ident)
        };

        lex.next()
            .filter(|t| t.what == TokenType::LParen)
            .and_then(|_| lex.next())
            .filter(|t| is_ident(t, "define"))
            .and_then(|_| lex.next())
            .filter(|t| t.what == TokenType::LParen)
            .and_then(|_| lex.next())
            .filter(|t| is_ident(t, "domain"))
            .is_some()
    }

    /// `parse` returns a complete domain represented by the PDDL domain
    /// within `src.`  Returns one or many `Error`s if any syntax or semantic
    /// error are encountered.
    pub fn parse(src: &str) -> Result<Self, Errors> {
        let tokens = scanner::scan(src);
        let mut top = Parser::new(src, &tokens);

        let top_parse: Parse;
        match top.domain_top() {
            Ok(pr) => top_parse = pr,
            Err(e) => return Err(vec![e]),
        }

        let mut dom = Domain::default();
        dom.name = top_parse.name.to_string();
        dom.reqs = top_parse.reqs;
        dom.types = top_parse.types;

        let mut parsers: Vec<Parser> = vec![];
        let dom_types = &dom.types;
        let mut new_parser = |what, pos| {
            let mut p = Parser::new(src, &tokens);

            p.tokpos = pos;
            p.reqs = dom.reqs;
            p.what = what;
            p.types = Some(dom_types);

            parsers.push(p);
        };

        if top_parse.pred_pos != 0 {
            new_parser(ParsingWhat::Predicates, top_parse.pred_pos);
        }
        if top_parse.func_pos != 0 {
            new_parser(ParsingWhat::Functions, top_parse.func_pos);
        }
        if top_parse.const_pos != 0 {
            new_parser(ParsingWhat::Constants, top_parse.const_pos);
        }

        let results: Vec<Result<Parse, Error>> = parsers
            .par_iter_mut()
            .map(|p| match p.what {
                ParsingWhat::Predicates => p.predicates(),
                ParsingWhat::Functions => p.functions(),
                ParsingWhat::Constants => p.constants(),
                _ => panic!("Parsing incorrect contents: {:?}", p.what),
            })
            .collect();

        let mut errors: Vec<Error> = vec![];

        for result in results {
            let parse = match result {
                Ok(r) => r,
                Err(e) => {
                    errors.push(e);
                    Parse::default()
                }
            };
            if errors.len() > 0 {
                continue;
            }
            match parse.what {
                ParsingWhat::Predicates => dom.predicates = parse.predicates,
                ParsingWhat::Functions => dom.functions = parse.functions,
                ParsingWhat::Constants => dom.constants = parse.constants,
                _ => continue,
            }
        }

        if errors.len() > 0 {
            return Err(errors);
        }

        let mut parsers: Vec<Parser> = vec![];
        let dom_types = &dom.types;
        let dom_preds = &dom.predicates;
        let dom_funcs = &dom.functions;
        let dom_consts = &dom.constants;
        let mut pred_map: parser::PredMap = parser::PredMap::new();
        let mut func_map: parser::FuncMap = parser::FuncMap::new();
        let mut const_map: parser::ConstMap = parser::ConstMap::new();

        for i in 0..dom.predicates.len() {
            let p = &dom.predicates[i];
            if p.id != i {
                panic!("Predicate ID not equal to its index");
            }
            pred_map.insert(p.signature_key(), p.id);
        }

        for i in 0..dom.functions.len() {
            let f = &dom.functions[i];
            if f.id != i {
                panic!("Function ID not equal to its index");
            }
            func_map.insert(f.signature_key(), f.id);
        }

        for i in 0..dom.constants.len() {
            let c = &dom.constants[i];
            if c.id != i {
                panic!("Constant ID not equal to its index");
            }
            const_map.insert(c.name.clone(), c.id);
        }

        let mut new_parser = |what, pos| {
            let mut p = Parser::new(src, &tokens);

            p.tokpos = pos;
            p.reqs = dom.reqs;
            p.what = what;
            p.types = Some(dom_types);
            p.pred_map = Some(&pred_map);
            p.predicates = Some(dom_preds);
            p.func_map = Some(&func_map);
            p.functions = Some(dom_funcs);
            p.const_map = Some(&const_map);
            p.constants = Some(dom_consts);

            parsers.push(p);
        };

        for pos in top_parse.action_pos {
            new_parser(ParsingWhat::Action, pos);
        }

        let results: Vec<Result<Parse, Error>> = parsers
            .par_iter_mut()
            .map(|p| match p.what {
                ParsingWhat::Action => p.action(),
                _ => panic!("Parsing incorrect contents: {:?}", p.what),
            })
            .collect();

        let mut act_id: ActionId = 0;
        let mut act_names: HashSet<String> = HashSet::new();

        for result in results {
            let parse = match result {
                Ok(r) => r,
                Err(e) => {
                    errors.push(e);
                    Parse::default()
                }
            };
            if errors.len() > 0 {
                continue;
            }
            match parse.what {
                ParsingWhat::Action => {
                    let mut act = parse.action.expect("did not receive a parsed :action");

                    if act_names.contains(&act.name) {
                        let s = format!("action, {}, is already defined", &act.name);
                        errors.push(Error {
                            what: ErrorType::SemanticError(s),
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
                _ => continue,
            }
        }

        if errors.len() > 0 {
            return Err(errors);
        }
        Ok(dom)
    }

    /// `parse_seq` is like `parse` but only parses `src` sequentially and
    /// employs no parallelism.  It is provided mainly for benchmark testing
    /// of `parse`.
    pub fn parse_seq(src: &str) -> Result<Self, Errors> {
        let tokens = scanner::scan(src);
        let mut top = Parser::new(src, &tokens);

        let top_parse: Parse;
        match top.domain_top() {
            Ok(pr) => top_parse = pr,
            Err(e) => return Err(vec![e]),
        }

        let mut dom = Domain::default();
        dom.name = top_parse.name.to_string();
        dom.reqs = top_parse.reqs;
        dom.types = top_parse.types;

        let mut errors: Vec<Error> = vec![];
        let dom_types = &dom.types;
        let dom_reqs = dom.reqs;
        let new_parser = |what, pos| {
            let mut p = Parser::new(src, &tokens);

            p.tokpos = pos;
            p.reqs = dom_reqs;
            p.what = what;
            p.types = Some(dom_types);

            p
        };

        if top_parse.pred_pos != 0 {
            let mut p = new_parser(ParsingWhat::Predicates, top_parse.pred_pos);
            match p.predicates() {
                Ok(parse) => dom.predicates = parse.predicates,
                Err(e) => errors.push(e),
            }
        }
        if top_parse.func_pos != 0 {
            let mut p = new_parser(ParsingWhat::Functions, top_parse.func_pos);
            match p.functions() {
                Ok(parse) => dom.functions = parse.functions,
                Err(e) => errors.push(e),
            }
        }
        if top_parse.const_pos != 0 {
            let mut p = new_parser(ParsingWhat::Constants, top_parse.const_pos);
            match p.constants() {
                Ok(parse) => dom.constants = parse.constants,
                Err(e) => errors.push(e),
            }
        }

        let dom_types = &dom.types;
        let dom_preds = &dom.predicates;
        let dom_funcs = &dom.functions;
        let dom_consts = &dom.constants;
        let mut pred_map: parser::PredMap = parser::PredMap::new();
        let mut func_map: parser::FuncMap = parser::FuncMap::new();
        let mut const_map: parser::ConstMap = parser::ConstMap::new();

        for i in 0..dom.predicates.len() {
            let p = &dom.predicates[i];
            if p.id != i {
                panic!("Predicate ID not equal to its index");
            }
            pred_map.insert(p.signature_key(), p.id);
        }

        for i in 0..dom.functions.len() {
            let f = &dom.functions[i];
            if f.id != i {
                panic!("Function ID not equal to its index");
            }
            func_map.insert(f.signature_key(), f.id);
        }

        for i in 0..dom.constants.len() {
            let c = &dom.constants[i];
            if c.id != i {
                panic!("Constant ID not equal to its index");
            }
            const_map.insert(c.name.clone(), c.id);
        }

        let new_parser = |what, pos| {
            let mut p = Parser::new(src, &tokens);

            p.tokpos = pos;
            p.reqs = dom_reqs;
            p.what = what;
            p.types = Some(dom_types);
            p.pred_map = Some(&pred_map);
            p.predicates = Some(dom_preds);
            p.func_map = Some(&func_map);
            p.functions = Some(dom_funcs);
            p.const_map = Some(&const_map);
            p.constants = Some(dom_consts);

            p
        };

        let mut act_id: ActionId = 0;
        let mut act_names: HashSet<String> = HashSet::new();

        for pos in top_parse.action_pos {
            let mut p = new_parser(ParsingWhat::Action, pos);
            match p.action() {
                Ok(parse) => {
                    let mut act = parse.action.expect("did not receive a parsed :action");

                    if act_names.contains(&act.name) {
                        let s = format!("action, {}, is already defined", &act.name);
                        errors.push(Error {
                            what: ErrorType::SemanticError(s),
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

    /// `has_requirement` returns true if this `Domain` has the requirement of `r`.
    pub fn has_requirement(&self, r: Requirement) -> bool {
        self.reqs.has(r)
    }

    /// `type_id` returns the TypeId associated with `name`, is it exists.
    pub fn type_id(&self, name: &str) -> Option<TypeId> {
        self.types.get(name)
    }

    /// `is_child_type_an_ancestor_of` returns true if `child` is an ancestor of `parent`.
    pub fn is_child_type_an_ancestor_of(&self, child: TypeId, parent: TypeId) -> bool {
        self.types.is_child_an_ancestor_of(child, parent)
    }
}

pub type PredId = usize;
pub type FuncId = usize;
pub type ConstId = usize;
pub type ActionId = usize;

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
        parser::Signature::create_key(&self.name, self.params.len())
    }
}

/// `Function` represents a predicate definition that is found
/// within the `:predicates` section of a PDDL domain.
#[derive(Debug)]
pub struct Function {
    /// A unique assigned ID for the predicate.
    pub id: FuncId,
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
        parser::Signature::create_key(&self.name, self.params.len())
    }
}

/// `Param` is a parsed parameter that can be found within various
/// constructs of a PDDL domain (e.g. within a predicate or function
/// definition, or within an :action or :durative-action).  The
/// parameter maintains its list of immediate `TypeId`s, that the
/// parameter may be.
#[derive(Debug)]
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

impl std::cmp::PartialEq for Param {
    fn eq(&self, other: &Self) -> bool {
        self.types.eq(&other.types)
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
    /// Parameters of the action.
    pub params: Vec<Param>,
    /// Possible precondition of the action.
    pub precondition: Option<Goal>,
    /// Possible effect of the action.
    pub effect: Option<Effect>,

    line: usize, // Line number where the action is defined.
    col: usize,  // Column number where the action is defined.
}

impl Action {
    pub fn new(name: &str) -> Action {
        Action {
            name: name.to_ascii_lowercase(),
            id: 0,
            params: vec![],
            line: 0,
            col: 0,
            precondition: None,
            effect: None,
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
    /// `is_func` returns true if the `Term` matches the `Term::Func` variant.
    pub fn is_func(&self) -> bool {
        if let Term::Func(_, _) = self {
            true
        } else {
            false
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Fexp {
    Number(f64),
    Mult(Vec<Fexp>),
    Add(Vec<Fexp>),
    Div(Box<Fexp>, Box<Fexp>),
    Sub(Box<Fexp>, Box<Fexp>),
    Neg(Box<Fexp>),
    Func(FuncId, Vec<Term>),
    FnSymbol(String),
}

#[derive(Debug, PartialEq)]
pub enum Fhead {
    FnSymbol(String),
    Func(FuncId, Vec<Term>),
}

#[derive(Debug, PartialEq)]
pub enum Effect {
    And(Vec<Effect>),
    Forall(Vec<Param>, Box<Effect>),
    When(Goal, Box<Effect>),
    Pred(PredId, Vec<Term>),
    Equal(Term, Term),
    Not(Box<Effect>),
    AssignUndef(FuncId, Vec<Term>),
    AssignTerm(FuncId, Vec<Term>, Term),
    AssignFexp(Fhead, Fexp),
    ScaleUp(Fhead, Fexp),
    ScaleDown(Fhead, Fexp),
    Increase(Fhead, Fexp),
    Decrease(Fhead, Fexp),
}

pub struct Problem {
    pub name: String,
    pub domain: String,
}

impl Default for Problem {
    fn default() -> Self {
        Problem {
            name: "".to_string(),
            domain: "".to_string(),
        }
    }
}

impl Problem {
    /// `is_problem` return true if `src` represents a PDDL problem.
    /// Only the first few tokens of `src` is paresed to make this
    /// determination.
    pub fn is_problem(src: &str) -> bool {
        let mut lex = Scanner::new(src);

        let is_ident = |t: &Token, ident| {
            t.what == TokenType::Ident && t.to_str(src).eq_ignore_ascii_case(ident)
        };

        lex.next()
            .filter(|t| t.what == TokenType::LParen)
            .and_then(|_| lex.next())
            .filter(|t| is_ident(t, "define"))
            .and_then(|_| lex.next())
            .filter(|t| t.what == TokenType::LParen)
            .and_then(|_| lex.next())
            .filter(|t| is_ident(t, "problem"))
            .is_some()
    }

    /// `parse` returns a complete problem represented by the PDDL domain
    /// within `src.`  Returns one or many `Error`s if any syntax or semantic
    /// error are encountered.
    pub fn parse(src: &str) -> Result<Self, Errors> {
        let tokens = scanner::scan(src);
        let mut top = Parser::new(src, &tokens);

        let top_parse: Parse;
        match top.problem_top() {
            Ok(pr) => top_parse = pr,
            Err(e) => return Err(vec![e]),
        }

        let mut prob = Problem::default();

        prob.name = top_parse.problem.to_string();
        prob.domain = top_parse.name.to_string();

        Ok(prob)
    }
}
