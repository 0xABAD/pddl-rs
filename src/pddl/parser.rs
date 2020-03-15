use std::{collections::HashMap, error, fmt, iter::Iterator};

use super::{
    reqs::{Reqs, Requirement},
    scanner::{Token, TokenType},
    types::{TypeId, Types},
    Action, ConstId, Constant, Fexp, FuncId, Function, Goal, Param, PredId, Predicate, Term,
};

pub type PredMap = HashMap<String, PredId>;
pub type FuncMap = HashMap<String, PredId>;
pub type ConstMap = HashMap<String, PredId>;

pub struct Parser<'a> {
    pub src: &'a str,                           // Original source that was scanned.
    pub tokens: &'a [Token],                    // Scanned tokens to be parsed.
    pub tokpos: usize,                          // Current index into `tokens`.
    pub col: usize,                             // Current column of parse.
    pub line: usize,                            // Current line of parse.
    pub what: ParsingWhat,                      // What is specifically being parsed.
    pub reqs: Reqs,                             // Known requirements.
    pub types: Option<&'a Types>,               // Collected type declarations.
    pub pred_map: Option<&'a PredMap>,          // Mapping of a predicates signature to its ID.
    pub predicates: Option<&'a Vec<Predicate>>, // All known predicates ordered by PredId.
    pub func_map: Option<&'a FuncMap>,          // Mapping of a functions signature to its ID.
    pub functions: Option<&'a Vec<Function>>,   // All known functions ordered by FuncId.
    pub const_map: Option<&'a ConstMap>,        // Mapping of a constants to its ID.
    pub constants: Option<&'a Vec<Constant>>,   // All known constants ordered by ConstId.
}

#[derive(Debug)]
pub enum ParsingWhat {
    Any,
    Predicates,
    Functions,
    Constants,
    Action,
}

impl<'a> Parser<'a> {
    pub fn new(src: &'a str, tokens: &'a [Token]) -> Self {
        Parser {
            src,
            tokens,
            tokpos: 0,
            col: 1,
            line: 1,
            reqs: Reqs::default(),
            types: None,
            what: ParsingWhat::Any,
            pred_map: None,
            predicates: None,
            func_map: None,
            functions: None,
            const_map: None,
            constants: None,
        }
    }

    pub fn domain_top(&mut self) -> Result<Parse, Error> {
        self.consume(TokenType::LParen)?;
        self.ident("define")?;
        self.consume(TokenType::LParen)?;
        self.ident("domain")?;

        let domain_name = self.consume(TokenType::Ident)?.to_str(self.src);
        self.consume(TokenType::RParen)?;

        const TOP_LEVEL_KEYWORDS: [&str; 9] = [
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
        let mut top_count = 9;
        let mut parse = Parse::default();

        parse.name = domain_name;

        loop {
            if self.next_is(TokenType::RParen).is_ok() {
                break;
            }
            if let Err(have) = self.next_is(TokenType::LParen) {
                return Err(Error::expect(self.line, self.col, have, &["(", ")"]));
            }
            let last_count = top_count;

            if top_count == 9 {
                top_count -= 1;
                if self.keyword_is(":requirements").is_ok() {
                    parse.reqs = self.requirements()?;
                    self.reqs = parse.reqs;

                    if self.reqs.has(Requirement::Typing) {
                        parse.types = Types::default();
                        parse.types.insert("object");
                    }
                    continue;
                }
            }

            if top_count == 8 {
                top_count -= 1;
                if self.keyword_is(":types").is_ok() {
                    if !self.reqs.has(Requirement::Typing) {
                        return Err(self.missing(Requirement::Typing, ":types"));
                    }
                    parse.types = self.parse_types()?;
                    continue;
                }
            }

            if top_count == 7 {
                top_count -= 1;
                if self.keyword_is(":constants").is_ok() {
                    parse.const_pos = self.tokpos;
                    self.balance_parens();
                    continue;
                }
            }

            if top_count == 6 {
                top_count -= 1;
                if self.keyword_is(":predicates").is_ok() {
                    parse.pred_pos = self.tokpos;
                    self.balance_parens();
                    continue;
                }
            }

            if top_count == 5 {
                top_count -= 1;
                if self.keyword_is(":functions").is_ok() {
                    parse.func_pos = self.tokpos;
                    self.balance_parens();
                    continue;
                }
            }

            if top_count == 4 {
                top_count -= 1;
                if self.keyword_is(":constraints").is_ok() {
                    if !self.reqs.has(Requirement::Constraints) {
                        return Err(self.missing(Requirement::Constraints, ":constraints section"));
                    }
                    parse.constraints_pos = self.tokpos;
                    self.balance_parens();
                    continue;
                }
            }

            if self.keyword_is(":action").is_ok() {
                parse.action_pos.push(self.tokpos);
                self.balance_parens();
                continue;
            }

            if self.keyword_is(":durative-action").is_ok() {
                if !self.reqs.has(Requirement::DurativeActions) {
                    return Err(self.missing(Requirement::DurativeActions, ":durative-action"));
                }
                parse.daction_pos.push(self.tokpos);
                self.balance_parens();
                continue;
            }

            if self.keyword_is(":derived").is_ok() {
                if !self.reqs.has(Requirement::DerivedPredicates) {
                    return Err(self.missing(Requirement::DerivedPredicates, ":derived predicate"));
                }
                parse.derived_pos.push(self.tokpos);
                self.balance_parens();
                continue;
            }

            return Err(self.expect_str(&TOP_LEVEL_KEYWORDS[0..last_count]));
        }

        if let Some(t) = self.next() {
            let s = t.to_str(self.src).to_string();
            return Err(Error {
                what: ErrorType::ExtraInput(s),
                col: t.col,
                line: t.line,
            });
        }

        Ok(parse)
    }

    fn expect(&mut self, ttypes: &[TokenType]) -> Error {
        let what: Vec<&str> = ttypes.iter().map(|t| t.as_str()).collect();
        self.expect_str(&what)
    }

    fn expect_str(&mut self, what: &[&str]) -> Error {
        if let Some(t) = self.next() {
            let have = t.to_str(self.src);
            return Error::expect(t.line, t.col, have, what);
        } else {
            return Error::expect(self.line, self.col, "end of input", what);
        }
    }

    /// `consume_and` is a generalization of `consume` where `what_str` is
    /// the value to be passed to an `Expect` error and `and` is a simple
    /// closure that returns true.
    fn consume_and<F>(&mut self, what: TokenType, what_str: &str, and: F) -> Result<&Token, Error>
    where
        F: FnOnce(&Token) -> bool,
    {
        let tok = self
            .next()
            .ok_or_else(|| Error::expect(self.line, self.col, "end of input", &[what_str]))?;

        if tok.what != what || !and(tok) {
            let have = tok.to_str(self.src);
            return Err(Error::expect(self.line, self.col, have, &[what_str]));
        }
        Ok(tok)
    }

    /// `consume` consumes and returns the next token whose `TokenType` is
    /// is equal to `what`. If that is not the case then a `ParseError` is
    /// returned that expects `what`.
    fn consume(&mut self, what: TokenType) -> Result<&Token, Error> {
        self.consume_and(what, what.as_str(), |_| true)
    }

    /// `ident` consumes the next input if the next token is an identifier
    /// that matches `what`.
    fn ident(&mut self, what: &str) -> Result<&Token, Error> {
        let src = self.src;
        self.consume_and(TokenType::Ident, what, |t| {
            t.to_str(src).eq_ignore_ascii_case(what)
        })
    }

    /// `keyword` consumes the next input if the next token is a keyword
    /// that matches `what`.
    fn keyword(&mut self, what: &str) -> Result<&Token, Error> {
        let src = self.src;
        self.consume_and(TokenType::Keyword, what, |t| {
            t.to_str(src).eq_ignore_ascii_case(what)
        })
    }

    /// `next_is_and` returns the next token in the stream if it has
    /// a `TokenType` of `what` and fulfills the predicate of `and`.  If
    /// false then the token is not consumed.
    fn next_is_and<F>(&mut self, what: TokenType, and: F) -> Result<&Token, &'a str>
    where
        F: FnOnce(&Token) -> bool,
    {
        if self.tokpos >= self.tokens.len() {
            return Err("end of input");
        }
        let t = &self.tokens[self.tokpos];
        if t.what == what && and(t) {
            self.tokpos += 1;
            self.col = t.col;
            self.line = t.line;
            Ok(t)
        } else {
            Err(t.to_str(self.src))
        }
    }

    /// `next_is` is like calling `next_is_and` where `and` is a tautology.
    fn next_is(&mut self, what: TokenType) -> Result<&Token, &'a str> {
        self.next_is_and(what, |_| true)
    }

    /// `keyword_is` returns true if the next token in the stream is an keyword
    /// and whose string contents are case insensitive match to `what`.  If false
    /// then the token is not consumed.
    fn keyword_is(&mut self, what: &str) -> Result<&Token, &'a str> {
        let src = self.src;
        self.next_is_and(TokenType::Keyword, |t| {
            t.to_str(src).eq_ignore_ascii_case(what)
        })
    }

    /// `ident_is` returns true if the next token in the stream is an identifier
    /// and whose string contents are case insensitive match to `what`.  If false
    /// then the token is not consumed.
    fn ident_is(&mut self, what: &str) -> Result<&Token, &'a str> {
        let src = self.src;
        self.next_is_and(TokenType::Ident, |t| {
            t.to_str(src).eq_ignore_ascii_case(what)
        })
    }

    /// `peek` returns the next token without consuming it from the stream.
    fn peek(&self) -> Option<&Token> {
        if self.tokpos >= self.tokens.len() {
            None
        } else {
            Some(&self.tokens[self.tokpos])
        }
    }

    /// `peek_is` returns the next token without consuming it from the stream
    /// if it is of type `what`.
    fn peek_is(&self, what: TokenType) -> Option<&Token> {
        if self.tokpos >= self.tokens.len() {
            None
        } else {
            let t = &self.tokens[self.tokpos];
            if t.what == what {
                Some(t)
            } else {
                None
            }
        }
    }

    /// `get_pred` returns the `Function` whose name matches the string form of
    /// `tok` and has the same `arity`.
    fn get_pred(&self, tok: &Token, arity: usize) -> Result<&Predicate, Error> {
        let name = tok.to_str(self.src).to_ascii_lowercase();
        let key = Signature::create_key(&name, arity);
        let map = self.pred_map.expect("predicate map not set for parser");

        if let Some(&id) = map.get(&key) {
            let preds = self.predicates.expect("predicate list not set for parser");
            return Ok(&preds[id]);
        }

        let s = format!("predicate, {}, not defined", name);
        Err(Error::semantic(tok.line, tok.col, &s))
    }

    /// `get_func` returns the `Function` whose name matches the string form of
    /// `tok` and has the same `arity`.
    fn get_func(&self, tok: &Token, arity: usize) -> Result<&Function, Error> {
        let name = tok.to_str(self.src).to_ascii_lowercase();
        let key = Signature::create_key(&name, arity);
        let map = self.func_map.expect("function map not set for parser");

        if let Some(&id) = map.get(&key) {
            let funcs = self.functions.expect("function list not set for parser");
            return Ok(&funcs[id]);
        }

        let s = format!("function, {}, not defined", name);
        Err(Error::semantic(tok.line, tok.col, &s))
    }

    /// `get_const` returns the `Constant` that is associated with string contents of `tok`.
    fn get_const(&self, tok: &Token) -> Result<&Constant, Error> {
        let name = tok.to_str(self.src).to_ascii_lowercase();
        let map = self.const_map.expect("constant map not set for parser");

        if let Some(&id) = map.get(&name) {
            let consts = self.constants.expect("constant list not set for parser");
            return Ok(&consts[id]);
        }

        let s = format!("constant, {}, not defined", name);
        Err(Error::semantic(tok.line, tok.col, &s))
    }

    /// `balance_parens` consumes tokens until the current count of parenthesis
    /// reaches zero.  Initially, the count is one since it is expected that the
    /// first left paren has already been consumed.
    fn balance_parens(&mut self) {
        let mut count = 1;

        while let Some(tok) = self.next() {
            if tok.what == TokenType::LParen {
                count += 1;
            } else if tok.what == TokenType::RParen {
                count -= 1;
                if count == 0 {
                    return;
                }
            }
        }
    }

    /// `requirements` parses the `:requirements` section of the
    /// PDDL domain and returns a bit vector where each bit position
    /// represents the requirement that is recognized.  The bit position
    /// for a requirement is the `Requirement::index` value.  Note,
    /// that a requirement that implies others (e.g. `:adl` implies
    /// `:strips`, `:typing`, and others) is expanded and also to the
    /// requirements bit vector.
    fn requirements(&mut self) -> Result<Reqs, Error> {
        const ALL: &[&str] = &[
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
        // Parse the first requirement where it is expected to be at
        // least one requriement.
        let mut reqs = Reqs::default();
        reqs.add(self.parse_requirement(ALL)?);

        loop {
            if self.next_is(TokenType::RParen).is_ok() {
                return Ok(reqs);
            }
            reqs.add(self.parse_requirement(ALL)?);
        }
    }

    /// `parse_requirement` is helper for `requirements`.
    fn parse_requirement(&mut self, all: &[&str]) -> Result<Requirement, Error> {
        for &r in all {
            if self.keyword_is(r).is_ok() {
                return Ok(to_requirement(r));
            }
        }
        let mut v = vec!["("];
        v.extend_from_slice(all);
        Err(self.expect_str(&v))
    }

    fn semantic(&self, s: &str) -> Error {
        Error::semantic(self.line, self.col, s)
    }

    fn missing(&self, r: Requirement, s: &str) -> Error {
        Error::missing(self.line, self.col, r, s)
    }

    /// `parse_types` extracts all the `:types` out from a PDDL domain.  Aside
    /// from syntax errors, semantic errors are returned if `object` is
    /// attempted to be a derived type or a type has circular inheritance.
    fn parse_types(&mut self) -> Result<Types, Error> {
        let mut types = Types::default();

        types.insert("object");

        loop {
            let mut siblings: Vec<(TypeId, Token)> = vec![];
            let src = self.src;

            if self.next_is(TokenType::RParen).is_ok() {
                return Ok(types);
            }

            // Basic type declaration (:types vehicle).
            if let Ok(tok) = self.next_is(TokenType::Ident) {
                let name = tok.to_str(src);
                if name.eq_ignore_ascii_case("object") {
                    return Err(self.semantic("object declared as a derived type"));
                }
                siblings.push((types.insert(name), *tok));
            }

            // Have one type now collect more to get a set of types that
            // inherit from another (:types first second - parent).
            'more_types: loop {
                if self.next_is(TokenType::RParen).is_ok() {
                    return Ok(types);
                } else if let Ok(tok) = self.next_is(TokenType::Ident) {
                    let s = tok.to_str(src);
                    if s.eq_ignore_ascii_case("object") {
                        return Err(self.semantic("object declared as a derived type"));
                    }
                    siblings.push((types.insert(s), *tok));
                } else if self.next_is(TokenType::Minus).is_ok() {
                    // Reached inherintance, collect single or multiple parent types.
                    self.type_declarations(|t| {
                        let parent_name = t.to_str(src);
                        let parent_id = types.insert(parent_name);
                        for &(child_id, child_t) in &siblings {
                            types.relate(child_id, parent_id);
                            if types.has_circular_types(child_id) {
                                let t = child_t;
                                let s = format!(
                                    "{} has circular inherintance with {}",
                                    t.to_str(src),
                                    parent_name
                                );
                                return Err(Error::semantic(t.line, t.col, &s));
                            }
                        }
                        Ok(())
                    })?;
                    break 'more_types;
                } else {
                    return Err(self.expect(&[
                        TokenType::Ident,
                        TokenType::Minus,
                        TokenType::RParen,
                    ]));
                }
            }
        }
    }

    /// `type_declarations` parses the type declarations that follow a '-' in
    /// some PDDL domain construct (e.g. ?a - (either foo bar) ?b - baz) and
    /// calls `on_type` for each type encountered.
    fn type_declarations<F>(&mut self, mut on_type: F) -> Result<(), Error>
    where
        F: FnMut(&Token) -> Result<(), Error>,
    {
        if let Ok(tok) = self.next_is(TokenType::Ident) {
            on_type(tok)?;
        } else if self.next_is(TokenType::LParen).is_ok() {
            self.ident("either")?;

            // Must have at least one either type.
            let first = self.consume(TokenType::Ident)?;
            on_type(first)?;

            // Get the rest of the either parent types.
            loop {
                if self.next_is(TokenType::RParen).is_ok() {
                    return Ok(());
                } else if let Ok(tok) = self.next_is(TokenType::Ident) {
                    on_type(tok)?;
                } else {
                    return Err(self.expect(&[TokenType::Ident, TokenType::RParen]));
                }
            }
        } else {
            return Err(self.expect(&[TokenType::Ident, TokenType::LParen]));
        }
        Ok(())
    }

    /// `collect_types` is a more specific version for `type_declarations` that
    /// merely extracts and returns the collected `TypeId`s.
    fn collect_types(&mut self) -> Result<Vec<TypeId>, Error> {
        let mut type_ids: Vec<TypeId> = vec![];
        let src = self.src;
        let types = self.types.unwrap();

        self.type_declarations(|t| {
            let name = t.to_str(src);
            if let Some(tid) = types.get(name) {
                type_ids.push(tid);
                return Ok(());
            }
            Err(Error::type_not_defined(t.line, t.col, name))
        })?;

        Ok(type_ids)
    }

    /// `predicates` parses the `:predicates` section of a PDDL domain.
    pub fn predicates(&mut self) -> Result<Parse, Error> {
        let mut result = Parse::default();
        let mut pred_id = 0;
        let mut pred_map: HashMap<String, PredId> = HashMap::new();

        result.what = ParsingWhat::Predicates;
        self.consume(TokenType::LParen)?;

        let sig = self.signature()?;
        let key = sig.lookup_key();

        result.predicates.push(Predicate {
            id: pred_id,
            name: sig.name,
            params: sig.params,
        });
        pred_map.insert(key, pred_id);
        pred_id += 1;

        loop {
            if self.next_is(TokenType::RParen).is_ok() {
                break;
            } else if self.next_is(TokenType::LParen).is_err() {
                return Err(self.expect(&[TokenType::LParen, TokenType::RParen]));
            }

            let sig = self.signature()?;
            let key = sig.lookup_key();

            if let Some(&id) = pred_map.get(&key) {
                for i in 0..sig.params.len() {
                    let p = &sig.params[i];
                    let param = &mut result.predicates[id].params[i];
                    param.types.extend_from_slice(&p.types);
                    param.types.sort();
                    param.types.dedup();
                }
            } else {
                result.predicates.push(Predicate {
                    id: pred_id,
                    name: sig.name,
                    params: sig.params,
                });
                pred_map.insert(key, pred_id);
                pred_id += 1;
            }
        }
        Ok(result)
    }

    /// `functions` parses the `:functions` section of a PDDL domain.
    pub fn functions(&mut self) -> Result<Parse, Error> {
        let mut func_id = 0;
        let mut funcs = Vec::<Function>::new();
        let mut func_ids = Vec::<FuncId>::new();
        let mut func_map: HashMap<String, FuncId> = HashMap::new();
        let mut parsed_types = false;
        let mut result = Parse::default();

        result.what = ParsingWhat::Functions;

        self.consume(TokenType::LParen)?;
        let sig = self.signature()?;
        let key = sig.lookup_key();

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

        loop {
            if self.next_is(TokenType::RParen).is_ok() {
                for &id in &func_ids {
                    funcs[id].returns_number = true;
                }
                result.functions = funcs;
                // If one or more functions are not followed by a '-' to specify
                // the return type then it is implied that the return type is
                // 'number'.
                if !parsed_types && !self.reqs.has(Requirement::NumericFluents) {
                    return Err(self.missing(Requirement::NumericFluents, "function(s)"));
                }
                return Ok(result);
            } else if self.next_is(TokenType::LParen).is_ok() {
                parsed_types = false;

                let sig = self.signature()?;
                let key = sig.lookup_key();

                if let Some(&id) = func_map.get(&key) {
                    func_ids.push(id);
                    for i in 0..sig.params.len() {
                        let p = &sig.params[i];
                        let param = &mut funcs[id].params[i];
                        param.types.extend_from_slice(&p.types);
                        param.types.sort();
                        param.types.dedup();
                    }
                } else {
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
            } else if self.next_is(TokenType::Minus).is_ok() {
                parsed_types = true;

                if let Some(tok) = self.peek() {
                    let s = tok.to_str(self.src);
                    if tok.what == TokenType::Ident && s.eq_ignore_ascii_case("number") {
                        self.next();

                        if !self.reqs.has(Requirement::NumericFluents) {
                            return Err(self.missing(Requirement::NumericFluents, "function(s)"));
                        }
                        for &id in &func_ids {
                            funcs[id].returns_number = true;
                        }
                        func_ids.clear();
                        continue;
                    }
                }

                if !self.reqs.has(Requirement::Typing) {
                    return Err(self.missing(Requirement::Typing, "function(s)"));
                }
                if !self.reqs.has(Requirement::ObjectFluents) {
                    return Err(self.missing(Requirement::ObjectFluents, "function(s)"));
                }

                let type_ids = self.collect_types()?;
                for &id in &func_ids {
                    funcs[id].return_types.extend_from_slice(&type_ids);
                    funcs[id].return_types.sort();
                    funcs[id].return_types.dedup();
                }
                func_ids.clear();
            } else {
                return Err(self.expect(&[TokenType::Minus, TokenType::LParen, TokenType::RParen]));
            }
        }
    }

    /// `signature` parses the predicate or function signature
    /// found in either the :predicates or :functions section of the
    /// PDDL domain.  It is assumed that the first left paren has been
    /// consumed.
    fn signature(&mut self) -> Result<Signature, Error> {
        let ident = self.consume(TokenType::Ident)?;
        let mut sig = Signature {
            name: ident.to_str(self.src).to_ascii_lowercase(),
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

        // Get the first variable if there is one.
        if self.next_is(TokenType::RParen).is_ok() {
            return Ok(sig);
        } else if let Ok(tok) = self.next_is(TokenType::Variable) {
            var_names.push(tok.to_str(self.src));
            sig.params.push(Param::default());
        } else {
            return Err(self.expect(&[TokenType::Variable, TokenType::RParen]));
        }

        // Get the rest of the variables and their types if they have some.
        loop {
            if self.next_is(TokenType::RParen).is_ok() {
                return Ok(sig);
            } else if let Ok(tok) = self.next_is(TokenType::Variable) {
                let name = tok.to_str(self.src);
                for n in &var_names {
                    if n.eq_ignore_ascii_case(name) {
                        let s = format!("{} is a duplicated parameter", name);
                        return Err(self.semantic(&s));
                    }
                }
                var_names.push(name);
                sig.params.push(Param::default());
            } else if self.next_is(TokenType::Minus).is_ok() {
                if !self.reqs.has(Requirement::Typing) {
                    return Err(self.missing(Requirement::Typing, ":types"));
                }
                let type_ids = self.collect_types()?;
                for i in var_begin..sig.params.len() {
                    let p = &mut sig.params[i];
                    p.types.extend_from_slice(&type_ids);
                    p.types.sort();
                    p.types.dedup();
                }
                var_begin = sig.params.len();
            } else {
                return Err(self.expect(&[
                    TokenType::Variable,
                    TokenType::Minus,
                    TokenType::RParen,
                ]));
            }
        }
    }

    /// `constants` parses the `:constants` portion of the PDDL domain.
    pub fn constants(&mut self) -> Result<Parse, Error> {
        let mut const_id = 0;
        let mut consts: Vec<Constant> = vec![];
        let mut const_ids: Vec<ConstId> = vec![];
        let mut const_map: HashMap<String, ConstId> = HashMap::new();
        let mut result = Parse::default();

        result.what = ParsingWhat::Constants;

        if let Ok(_) = self.next_is(TokenType::RParen) {
            result.constants = consts;
            return Ok(result);
        } else if let Ok(tok) = self.next_is(TokenType::Ident) {
            let ident = tok.to_str(self.src).to_ascii_lowercase();
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
        } else {
            return Err(self.expect(&[TokenType::Ident, TokenType::RParen]));
        }

        loop {
            if self.next_is(TokenType::RParen).is_ok() {
                result.constants = consts;
                return Ok(result);
            } else if let Ok(tok) = self.next_is(TokenType::Ident) {
                let ident = tok.to_str(self.src).to_ascii_lowercase();
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
            } else if self.next_is(TokenType::Minus).is_ok() {
                if !self.reqs.has(Requirement::Typing) {
                    return Err(self.missing(Requirement::Typing, ":types"));
                }
                let type_ids = self.collect_types()?;
                for &id in &const_ids {
                    consts[id].types.extend_from_slice(&type_ids);
                    consts[id].types.sort();
                    consts[id].types.dedup();
                }
                const_ids.clear();
            } else {
                return Err(self.expect(&[TokenType::Ident, TokenType::Minus, TokenType::RParen]));
            }
        }
    }

    /// `action` parses an :action definition.  Note that the ActionId is not
    /// assigned.
    pub fn action(&mut self) -> Result<Parse, Error> {
        let src = self.src;
        let act_token = self.consume(TokenType::Ident)?;
        let act_name = act_token.to_str(src);
        let mut action = Action::new(act_name);
        let mut result = Parse::default();
        let mut stack = ParamStack::new();

        action.line = act_token.line;
        action.col = act_token.col;

        self.keyword(":parameters")?;
        stack.push(self.typed_list_variable()?);

        let mut have_pre = false;
        if self.keyword_is(":precondition").is_ok() {
            if !self.is_empty_construct() {
                action.precondition = Some(self.pre_goal(&mut stack)?);
                have_pre = true;
            } else {
                self.consume(TokenType::LParen)?;
                self.consume(TokenType::RParen)?;
            }
        }

        let have_eff = false;

        if self.next_is(TokenType::RParen).is_err() {
            let mut v: Vec<&str> = vec![];
            if !have_pre && !have_eff {
                v.push(":precondition");
                v.push(":effect");
            }
            if have_pre && !have_eff {
                v.push(":effect");
            }
            v.push(")");
            return Err(self.expect_str(&v));
        }

        action.params = stack.pop().unwrap();
        result.what = ParsingWhat::Action;
        result.action = Some(action);

        Ok(result)
    }

    /// `is_empty_construct` peeks ahead to see if the upcoming tokens form
    /// an empty construct (i.e. "()").
    fn is_empty_construct(&self) -> bool {
        if self.tokpos + 1 >= self.tokens.len() {
            return false;
        }
        let t0 = &self.tokens[self.tokpos];
        let t1 = &self.tokens[self.tokpos + 1];
        t0.what == TokenType::LParen && t1.what == TokenType::RParen
    }

    /// `check_requirement` ensures that the `Requirement` is fulfilled with
    /// this parser.
    fn check_requirement(&self, r: Requirement, s: &str) -> Result<(), Error> {
        if !self.reqs.has(r) {
            return Err(Error::missing(self.line, self.col, r, s));
        }
        Ok(())
    }

    /// `check_types` checks if any `TypeId` of `kids` is one or
    /// or an ancestor of `parents`.
    fn check_types(&self, tok: &Token, kids: &[TypeId], parents: &[TypeId]) -> Result<(), Error> {
        if kids.len() == 0 && parents.len() == 0 {
            return Ok(());
        }

        let name = tok.to_str(self.src);
        if kids.len() == 0 {
            let s = format!("{} does not represent a type", name);
            return Err(Error::semantic(tok.line, tok.col, &s));
        }
        if parents.len() == 0 {
            let s = format!(
                "{} implements a type but none are allowed for the argument",
                name
            );
            return Err(Error::semantic(tok.line, tok.col, &s));
        }

        let types = &self.types.unwrap();
        for &k in kids {
            for &p in parents {
                if k == p || types.is_child_an_ancestor_of(k, p) {
                    return Ok(());
                }
            }
        }

        let mut tnames: Vec<&str> = vec![];
        for &id in parents {
            tnames.push(types.name_of(id));
        }
        let s = format!(
            "none of the types for {} are one of or a subtype of {:?}",
            name, tnames
        );
        Err(Error::semantic(tok.line, tok.col, &s))
    }

    /// `pre_goal` parses a :precondition goal description.
    fn pre_goal(&mut self, stack: &mut ParamStack) -> Result<Goal, Error> {
        self.consume(TokenType::LParen)?;

        if self.ident_is("and").is_ok() {
            let mut goals: Vec<Goal> = vec![];
            while let Some(_) = self.peek_is(TokenType::LParen) {
                goals.push(self.pre_goal(stack)?);
            }
            self.consume(TokenType::RParen)?;
            Ok(Goal::And(goals))
        } else if self.ident_is("preference").is_ok() {
            self.check_requirement(Requirement::Preferences, "preference goal")?;

            let mut name = "".to_string();
            if let Ok(t) = self.next_is(TokenType::Ident) {
                name = t.to_str(self.src).to_ascii_lowercase();
            }

            if self.peek_is(TokenType::LParen).is_some() {
                let g = Box::new(self.goal(stack)?);
                self.consume(TokenType::RParen)?;
                Ok(Goal::Preference(name, g))
            } else {
                let mut v = vec![];
                if name.len() == 0 {
                    v.push("identifier");
                }
                v.push("(");
                Err(self.expect_str(&v))
            }
        } else if self.ident_is("forall").is_ok() {
            self.check_requirement(Requirement::UniversalPreconditions, "forall goal")?;

            stack.push(self.typed_list_variable()?);

            let g = self.pre_goal(stack)?;
            let p = stack.pop().unwrap();
            self.consume(TokenType::RParen)?;
            Ok(Goal::Forall(p, Box::new(g)))
        } else if self.peek_is(TokenType::Equal).is_some()
            || self.peek_is(TokenType::Less).is_some()
            || self.peek_is(TokenType::LessEq).is_some()
            || self.peek_is(TokenType::Greater).is_some()
            || self.peek_is(TokenType::GreaterEq).is_some()
            || self.peek_is(TokenType::Ident).is_some()
        {
            // Unconsume the left paren before parsing the goal.
            self.tokpos -= 1;
            self.goal(stack)
        } else {
            Err(self.expect_str(&[
                "and",
                "preference",
                "forall",
                "exists",
                "imply",
                "or",
                "not",
                "identifier",
                "=",
                "<",
                "<=",
                ">",
                ">=",
            ]))
        }
    }

    /// `goal` parses a general goal description.
    fn goal(&mut self, stack: &mut ParamStack) -> Result<Goal, Error> {
        self.consume(TokenType::LParen)?;

        if self.ident_is("and").is_ok() {
            let mut goals: Vec<Goal> = vec![];
            while self.peek_is(TokenType::LParen).is_some() {
                goals.push(self.goal(stack)?);
            }
            self.consume(TokenType::RParen)?;
            Ok(Goal::And(goals))
        } else if self.ident_is("forall").is_ok() {
            self.check_requirement(Requirement::UniversalPreconditions, "forall goal")?;

            stack.push(self.typed_list_variable()?);

            let g = self.goal(stack)?;
            let p = stack.pop().unwrap();
            self.consume(TokenType::RParen)?;
            Ok(Goal::Forall(p, Box::new(g)))
        } else if self.ident_is("exists").is_ok() {
            self.check_requirement(Requirement::ExistentialPreconditions, "exists goal")?;

            stack.push(self.typed_list_variable()?);

            let g = self.goal(stack)?;
            let p = stack.pop().unwrap();
            self.consume(TokenType::RParen)?;
            Ok(Goal::Exists(p, Box::new(g)))
        } else if self.ident_is("imply").is_ok() {
            self.check_requirement(Requirement::DisjunctivePreconditions, "imply goal")?;

            let g1 = self.goal(stack)?;
            let g2 = self.goal(stack)?;
            self.consume(TokenType::RParen)?;

            Ok(Goal::Imply(Box::new(g1), Box::new(g2)))
        } else if self.ident_is("or").is_ok() {
            self.check_requirement(Requirement::DisjunctivePreconditions, "or goal")?;

            let mut goals: Vec<Goal> = vec![];
            while self.peek_is(TokenType::LParen).is_some() {
                goals.push(self.goal(stack)?);
            }
            self.consume(TokenType::RParen)?;
            Ok(Goal::Or(goals))
        } else if self.ident_is("not").is_ok() {
            let g = self.goal(stack)?;

            if let Goal::Pred(_, _) = &g {
                self.check_requirement(Requirement::NegativePreconditions, "not goal")?;
            } else if let Goal::EqualTerms(_, _) = &g {
                self.check_requirement(Requirement::NegativePreconditions, "not goal")?;
            } else {
                self.check_requirement(Requirement::DisjunctivePreconditions, "not goal")?;
            }
            Ok(Goal::Not(Box::new(g)))
        } else if let Ok(&ident) = self.next_is(TokenType::Ident) {
            let mut terms: Vec<Term> = vec![];
            let mut tokens: Vec<Token> = vec![];

            while !self.peek_is(TokenType::RParen).is_some() {
                let t = self.term(stack)?;
                terms.push(t.what);
                tokens.push(t.info);
            }

            let pred = self.get_pred(&ident, terms.len())?;
            let id = pred.id;

            for i in 0..terms.len() {
                let ttypes = self.term_types(&terms[i]);
                let ftypes = &pred.params[i].types;
                self.check_types(&tokens[i], ttypes, ftypes)?;
            }
            self.consume(TokenType::RParen)?;

            Ok(Goal::Pred(id, terms))
        } else if self.next_is(TokenType::Less).is_ok() {
            self.check_requirement(Requirement::NumericFluents, "<")?;
            Ok(Goal::Less(self.fexp(stack)?, self.fexp(stack)?))
        } else {
            Err(self.expect_str(&[
                "and",
                "forall",
                "exists",
                "imply",
                "or",
                "not",
                "identifier",
                "<",
            ]))
        }
    }

    /// `typed_list_variable` returns the variable parameters that are associated with
    /// variable list declarations for :action parameters, forall goal, and other such
    /// constructs.  One or more variable parameters may or may not not have types.
    fn typed_list_variable(&mut self) -> Result<Vec<Param>, Error> {
        let mut params: Vec<Param> = vec![];
        let mut par_indices: Vec<usize> = vec![];

        self.consume(TokenType::LParen)?;

        if let Ok(_) = self.next_is(TokenType::RParen) {
            return Ok(params);
        } else if let Ok(tok) = self.next_is(TokenType::Variable) {
            let mut param = Param::default();
            par_indices.push(params.len());
            param.start = tok.pos;
            param.end = tok.end;
            params.push(param);
        } else {
            return Err(self.expect(&[TokenType::Variable, TokenType::RParen]));
        }

        'variables: loop {
            let src = self.src;

            if let Ok(_) = self.next_is(TokenType::RParen) {
                return Ok(params);
            } else if let Ok(tok) = self.next_is(TokenType::Variable) {
                let name = tok.to_str(src);

                // Skip if this variable has already been seen.
                for i in 0..params.len() {
                    let p = &params[i];
                    let pname = &src[p.start..p.end];
                    if pname.eq_ignore_ascii_case(name) {
                        par_indices.push(i);
                        continue 'variables;
                    }
                }

                let mut param = Param::default();
                par_indices.push(params.len());
                param.start = tok.pos;
                param.end = tok.end;
                params.push(param);
            } else if let Ok(_) = self.next_is(TokenType::Minus) {
                if !self.reqs.has(Requirement::Typing) {
                    return Err(self.missing(Requirement::Typing, ":types"));
                }

                let type_ids = self.collect_types()?;
                for &i in &par_indices {
                    let p = &mut params[i];
                    p.types.extend_from_slice(&type_ids);
                    p.types.sort();
                    p.types.dedup();
                }
                par_indices.clear();
            } else {
                return Err(self.expect(&[
                    TokenType::Variable,
                    TokenType::Minus,
                    TokenType::RParen,
                ]));
            }
        }
    }

    /// `fexp` parses the functional expression that is part of a goal
    /// goal description.
    fn fexp(&mut self, stack: &mut ParamStack) -> Result<Fexp, Error> {
        if let Ok(tok) = self.next_is(TokenType::Ident) {
            let sym = tok.to_str(self.src).to_ascii_lowercase();
            Ok(Fexp::FnSymbol(sym))
        } else if let Ok(tok) = self.next_is(TokenType::Number) {
            let num = tok.to_str(self.src).parse().unwrap();
            Ok(Fexp::Number(num))
        } else if self.next_is(TokenType::LParen).is_ok() {
            if let Ok(&ident) = self.next_is(TokenType::Ident) {
                let (id, terms) = self.func_term(&ident, stack)?;
                let func = &self.functions.unwrap()[id];

                if !func.returns_number {
                    let f = ident.to_str(self.src);
                    let s = format!("function, {}, does not return a number", f);
                    return Err(Error::semantic(ident.line, ident.col, &s));
                }
                Ok(Fexp::Func(id, terms))
            } else if self.next_is(TokenType::Mult).is_ok() {
                let first = self.fexp(stack)?;
                let second = self.fexp(stack)?;
                let mut args: Vec<Fexp> = vec![second];

                while self.peek_is(TokenType::Ident).is_some()
                    || self.peek_is(TokenType::Number).is_some()
                    || self.peek_is(TokenType::LParen).is_some()
                {
                    args.push(self.fexp(stack)?);
                }
                self.consume(TokenType::RParen)?;

                Ok(Fexp::Mult(Box::new(first), args))
            } else if self.next_is(TokenType::Plus).is_ok() {
                let first = self.fexp(stack)?;
                let second = self.fexp(stack)?;
                let mut args: Vec<Fexp> = vec![second];

                while self.peek_is(TokenType::Ident).is_some()
                    || self.peek_is(TokenType::Number).is_some()
                    || self.peek_is(TokenType::LParen).is_some()
                {
                    args.push(self.fexp(stack)?);
                }
                self.consume(TokenType::RParen)?;

                Ok(Fexp::Add(Box::new(first), args))
            } else if self.next_is(TokenType::Div).is_ok() {
                let f1 = self.fexp(stack)?;
                let f2 = self.fexp(stack)?;

                self.consume(TokenType::RParen)?;

                Ok(Fexp::Div(Box::new(f1), Box::new(f2)))
            } else if self.next_is(TokenType::Minus).is_ok() {
                let f1 = self.fexp(stack)?;

                if self.peek_is(TokenType::RParen).is_some() {
                    self.consume(TokenType::RParen)?;
                    Ok(Fexp::Neg(Box::new(f1)))
                } else {
                    let f2 = self.fexp(stack)?;
                    self.consume(TokenType::RParen)?;
                    Ok(Fexp::Sub(Box::new(f1), Box::new(f2)))
                }
            } else {
                Err(self.expect_str(&["identifier", "*", "+", "/", "-"]))
            }
        } else {
            Err(self.expect_str(&["number", "identifier", "("]))
        }
    }

    /// `term` parses a predicate or function term (i.e. argument).
    fn term(&mut self, stack: &mut ParamStack) -> Result<TermInfo, Error> {
        if let Ok(&tok) = self.next_is(TokenType::Ident) {
            let c = self.get_const(&tok)?;
            Ok(TermInfo {
                what: Term::Const(c.id),
                info: tok,
            })
        } else if let Ok(&tok) = self.next_is(TokenType::Variable) {
            let var = tok.to_str(self.src);

            if let Some(p) = stack.find(self.src, var) {
                Ok(TermInfo {
                    what: Term::Var(p.types.clone()),
                    info: tok,
                })
            } else {
                Err(self.semantic(&format!("variable, {}, not defined", var)))
            }
        } else if self.next_is(TokenType::LParen).is_ok() {
            let &ident = self.consume(TokenType::Ident)?;
            let (id, terms) = self.func_term(&ident, stack)?;
            Ok(TermInfo {
                what: Term::Func(id, terms),
                info: ident,
            })
        } else {
            Err(self.expect_str(&["identifier", "variable", "("]))
        }
    }

    /// `func_term` parses the function term that is part an expression.
    /// It expects the function name has already been parsed which is
    /// passed as `ident`.
    fn func_term(
        &mut self,
        ident: &Token,
        stack: &mut ParamStack,
    ) -> Result<(FuncId, Vec<Term>), Error> {
        let mut terms: Vec<Term> = vec![];
        let mut tokens: Vec<Token> = vec![];

        while !self.peek_is(TokenType::RParen).is_some() {
            let t = self.term(stack)?;
            terms.push(t.what);
            tokens.push(t.info);
        }
        let func = self.get_func(&ident, terms.len())?;

        for i in 0..terms.len() {
            let ttypes = self.term_types(&terms[i]);
            let ftypes = &func.params[i].types;
            self.check_types(&tokens[i], ttypes, ftypes)?;
        }

        let id = func.id;
        self.consume(TokenType::RParen)?;
        Ok((id, terms))
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
}

impl<'a> Iterator for Parser<'a> {
    type Item = &'a Token;

    fn next(&mut self) -> Option<Self::Item> {
        if self.tokpos >= self.tokens.len() {
            return None;
        }
        let t = &self.tokens[self.tokpos];
        self.tokpos += 1;
        self.col = t.col;
        self.line = t.line;
        Some(t)
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

/// `TermInfo` allows packaging a `Term` along with the `Token` of
/// when it was parsed.  This facilitates type checking after the
/// term has bene parsed and returned to the caller.
#[derive(Debug)]
struct TermInfo {
    what: Term,
    info: Token,
}

/// `Signature` encapsulates the parsed result of a predicate or
/// function declaration (i.e. '(foo ?a ?b - object ?c - (either bar baz))' ).
pub struct Signature {
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
    pub fn create_key(name: &str, arity: usize) -> String {
        format!("{}-**-{}-**-", name, arity)
    }
}

/// `to_requirement` transforms the `TokenType` to its equivilant Requirement.
/// This method will panic if there is no such equivilant.
fn to_requirement(s: &str) -> Requirement {
    match s {
        ":strips" => Requirement::Strips,
        ":typing" => Requirement::Typing,
        ":equality" => Requirement::Equality,
        ":negative-preconditions" => Requirement::NegativePreconditions,
        ":disjunctive-preconditions" => Requirement::DisjunctivePreconditions,
        ":existential-preconditions" => Requirement::ExistentialPreconditions,
        ":universal-preconditions" => Requirement::UniversalPreconditions,
        ":quantified-preconditions" => Requirement::QuantifiedPreconditions,
        ":conditional-effects" => Requirement::ConditionalEffects,
        ":fluents" => Requirement::Fluents,
        ":numeric-fluents" => Requirement::NumericFluents,
        ":object-fluents" => Requirement::ObjectFluents,
        ":adl" => Requirement::Adl,
        ":durative-actions" => Requirement::DurativeActions,
        ":duration-inequalities" => Requirement::DurationInequalities,
        ":continuous-effects" => Requirement::ContinuousEffects,
        ":derived-predicates" => Requirement::DerivedPredicates,
        ":timed-initial-literals" => Requirement::TimedInitialLiterals,
        ":preferences" => Requirement::Preferences,
        ":constraints" => Requirement::Constraints,
        ":action-costs" => Requirement::ActionCosts,
        _ => panic!("no such Requirement for TokenType {:?}", s),
    }
}

/// `Parse` encompasses a successful parse returned from one of the
/// different methods of a `Parser`.
#[derive(Debug)]
pub struct Parse<'a> {
    pub what: ParsingWhat,          // What was parsed by this result.
    pub name: &'a str,              // Name of a domain.
    pub reqs: Reqs,                 // Requirements of the domain represented as bit vector.
    pub types: Types,               // Types extracted from the domain.
    pub const_pos: usize, // Token position within the PDDL source where constants are located.
    pub pred_pos: usize,  // Token position within the PDDL source where predicates are located.
    pub func_pos: usize,  // Token position within the PDDL source where functions are located.
    pub constraints_pos: usize, // Token position within the PDDL source where constraints are located.
    pub action_pos: Vec<usize>, // Token positions where :actions begin in the PDDL source.
    pub daction_pos: Vec<usize>, // Token positions where :durative-actions begin in the PDDL source.
    pub derived_pos: Vec<usize>, // Token positions where :derived functions begin in the PDDL source.
    pub predicates: Vec<Predicate>, // Parsed predicate declarations.
    pub functions: Vec<Function>, // Parsed function declarations.
    pub constants: Vec<Constant>, // Parsed constant declarations.
    pub action: Option<Action>,  // Parsed action definition.
}

impl<'a> Default for Parse<'a> {
    fn default() -> Self {
        Parse {
            what: ParsingWhat::Any,
            name: "",
            reqs: Reqs::default(),
            types: Types::default(),
            const_pos: 0,
            pred_pos: 0,
            func_pos: 0,
            constraints_pos: 0,
            action_pos: vec![],
            daction_pos: vec![],
            derived_pos: vec![],
            predicates: vec![],
            functions: vec![],
            constants: vec![],
            action: None,
        }
    }
}

/// `ParseError` is the error returned from parsing a PDDL domain.
#[derive(Debug, PartialEq)]
pub struct Error {
    /// The specific parse error that occurred.
    pub what: ErrorType,
    /// The line number the error occurred on.
    pub line: usize,
    /// The column number the error occurred on.
    pub col: usize,
}

impl Error {
    /// `expect` returns a `Error` for an error that occurred
    /// on line, `line`, column, `col`, and has a value of `have` where
    /// `expect` are the expected values at the time of parse.
    pub fn expect(line: usize, col: usize, have: &str, expect: &[&str]) -> Self {
        let have = have.to_string();
        let expect = expect.iter().map(|s| s.to_string()).collect();
        let what = ErrorType::Expect { have, expect };
        Error { what, line, col }
    }

    /// `missing` returns a `ParserError` where the requirement is missing
    /// for `reason`.
    pub fn missing(line: usize, col: usize, req: Requirement, what: &str) -> Self {
        let what = what.to_string();
        let what = ErrorType::MissingRequirement { req, what };
        Error { what, line, col }
    }

    /// `semantic` returns a `Error` that represents some semantic
    /// error in the PDDL language (i.e. predicate not defined).
    pub fn semantic(line: usize, col: usize, what: &str) -> Self {
        let what = ErrorType::SemanticError(what.to_string());
        Error { what, line, col }
    }

    /// `type_not_defined` returns a `Error` where `what` was declared
    /// as a type but wasn't defined within the `:types` section of the
    /// PDDL domain.
    pub fn type_not_defined(line: usize, col: usize, what: &str) -> Self {
        let what = ErrorType::TypeNotDefined(what.to_string());
        Error { what, line, col }
    }
}

impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: error: {}", self.line, self.col, self.what)
    }
}

/// `ErrorType` are the different type of `Error`s that
/// can occur during parsing a PDDL domain.
#[derive(Debug, PartialEq)]
pub enum ErrorType {
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

impl fmt::Display for ErrorType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorType::Expect { have, expect } => {
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
            ErrorType::ExtraInput(s) => write!(f, "Extra input detected: {}", s),
            ErrorType::SemanticError(what) => write!(f, "{}", what),
            ErrorType::MissingRequirement { req, what } => write!(
                f,
                "{} requires {} declaration in :requirements section",
                what, req
            ),
            ErrorType::TypeNotDefined(t) => write!(f, "Type, {}, is not defined within :types", t),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::pddl::scanner::{self, TokenType};

    #[test]
    fn iterates() {
        const TEST: &'static str = "(define (domain foo))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);

        let ttypes = &[
            TokenType::LParen,
            TokenType::Ident,
            TokenType::LParen,
            TokenType::Ident,
            TokenType::Ident,
            TokenType::RParen,
            TokenType::RParen,
        ];

        for &tt in ttypes {
            let t = parser.next();
            assert!(t.is_some());
            assert_eq!(t.unwrap().what, tt);
        }
    }

    #[test]
    fn consumes() -> Result<(), Error> {
        const TEST: &'static str = "(define (domain foo))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);

        assert!(parser.consume(TokenType::LParen).is_ok());
        assert!(parser.consume(TokenType::Ident).is_ok());
        assert!(parser.consume(TokenType::LParen).is_ok());
        assert!(parser.consume(TokenType::Ident).is_ok());
        assert!(parser.consume(TokenType::Ident).is_ok());
        assert!(parser.consume(TokenType::RParen).is_ok());

        let t = parser.consume(TokenType::RParen)?;
        assert_eq!(t.what, TokenType::RParen);
        assert_eq!(t.col, 21);
        assert_eq!(t.line, 1);

        Ok(())
    }

    #[test]
    fn consume_fails_with_end_of_input() {
        const TEST: &'static str = "(define ";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);

        assert!(parser.consume(TokenType::LParen).is_ok());
        assert!(parser.consume(TokenType::Ident).is_ok());

        let last = parser.consume(TokenType::Ident);
        assert!(last.is_err());
        assert_eq!(
            last,
            Err(Error {
                what: ErrorType::Expect {
                    have: "end of input".to_string(),
                    expect: vec!["identifier".to_string()],
                },
                line: 1,
                col: 2,
            })
        );
    }

    #[test]
    fn parse_ident() {
        const TEST: &'static str = "(define (DoMain";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);

        assert!(parser.consume(TokenType::LParen).is_ok());
        assert!(parser.ident("define").is_ok());
        assert!(parser.consume(TokenType::LParen).is_ok());
        assert!(parser.ident("domain").is_ok());
    }

    #[test]
    fn can_next_is() {
        const TEST: &'static str = ":REQUIREMENTS ( :action)";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);

        assert!(parser.keyword_is(":requirements").is_ok());
        assert!(parser.next_is(TokenType::LParen).is_ok());
        assert!(parser.keyword_is(":action").is_ok());
        assert!(parser.next_is(TokenType::RParen).is_ok());
    }

    #[test]
    fn parse_requirements() -> Result<(), Error> {
        const TEST: &'static str = ":Typing :equality)";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let reqs = parser.requirements()?;

        assert!(reqs.has(Requirement::Typing));
        assert!(reqs.has(Requirement::Equality));
        assert!(!reqs.has(Requirement::Strips));
        Ok(())
    }

    #[test]
    fn can_parse_types() -> Result<(), Error> {
        const TEST: &'static str = "car truck motorcycle - vehicle
             bicycle - object
             moped - (either motorcycle bicycle)))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let types = parser.parse_types()?;

        assert_eq!(types.get("object"), Some(0));
        assert_eq!(types.get("car"), Some(1));
        assert_eq!(types.get("truck"), Some(2));
        assert_eq!(types.get("motorcycle"), Some(3));
        assert_eq!(types.get("vehicle"), Some(4));
        assert_eq!(types.get("bicycle"), Some(5));
        assert_eq!(types.get("moped"), Some(6));

        let object = types.get("object").unwrap();
        let car = types.get("car").unwrap();
        let truck = types.get("truck").unwrap();
        let motorcycle = types.get("motorcycle").unwrap();
        let vehicle = types.get("vehicle").unwrap();
        let bicycle = types.get("bicycle").unwrap();
        let moped = types.get("moped").unwrap();

        assert!(types.is_child_an_ancestor_of(car, vehicle));
        assert!(types.is_child_an_ancestor_of(truck, vehicle));
        assert!(types.is_child_an_ancestor_of(motorcycle, vehicle));
        assert!(types.is_child_an_ancestor_of(bicycle, object));
        assert!(types.is_child_an_ancestor_of(moped, motorcycle));
        assert!(types.is_child_an_ancestor_of(moped, bicycle));
        assert!(types.is_child_an_ancestor_of(moped, object));
        assert!(types.is_child_an_ancestor_of(moped, vehicle));

        Ok(())
    }

    #[test]
    fn unbalanced_parens_in_constants() {
        const TEST: &'static str = "(define (domain foo)
           (:requirements :strips :typing)
           (:types item)
           (:constants foo bar - item";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let result = parser.domain_top();

        if let Err(e) = result {
            match e.what {
                ErrorType::Expect { have: _, expect: _ } => return,
                _ => panic!("Invalid ErrorType -- have {:?}, want Expect", e.what),
            }
        } else {
            panic!("Received successful parse when error should have occurred.");
        }
    }

    #[test]
    fn correct_constants_position() -> Result<(), Error> {
        const TEST: &'static str = "(define (domain d) (:constants a b))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let result = parser.domain_top()?;

        assert_eq!(result.const_pos, 8);
        Ok(())
    }

    #[test]
    fn correct_predicates_position() -> Result<(), Error> {
        const TEST: &'static str = "(define (domain d) (:constants a b) (:predicates (a)))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let result = parser.domain_top()?;

        assert_eq!(result.pred_pos, 13);
        Ok(())
    }

    #[test]
    fn correct_functions_position() -> Result<(), Error> {
        const TEST: &'static str = "(define (domain d)
           (:requirements :numeric-fluents)
           (:functions (a)))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let result = parser.domain_top()?;

        assert_eq!(result.func_pos, 12);
        Ok(())
    }

    #[test]
    fn correct_constraints_position() -> Result<(), Error> {
        const TEST: &'static str = "(define (domain d)
           (:requirements :constraints)
           (:constraints (and)))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let result = parser.domain_top()?;

        assert_eq!(result.constraints_pos, 12);
        Ok(())
    }

    #[test]
    fn correct_action_positions() -> Result<(), Error> {
        const TEST: &'static str = "(define (domain d)
           (:action a :parameters ())
           (:action b :parameters ()))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let result = parser.domain_top()?;

        assert_eq!(result.action_pos, vec![8, 15]);
        Ok(())
    }

    #[test]
    fn correct_durative_action_positions() -> Result<(), Error> {
        const TEST: &'static str = "(define (domain d)
           (:requirements :durative-actions)
           (:durative-action a :parameters () :duration () :condition () :effect ())
           (:durative-action b :parameters () :duration () :condition () :effect ()))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let result = parser.domain_top()?;

        assert_eq!(result.daction_pos, vec![12, 28]);
        Ok(())
    }

    #[test]
    fn correct_derived_predicate_positions() -> Result<(), Error> {
        const TEST: &'static str = "(define (domain d)
           (:requirements :derived-predicates)
           (:derived (a) (and))
           (:derived (b) (and)))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let result = parser.domain_top()?;

        assert_eq!(result.derived_pos, vec![12, 21]);
        Ok(())
    }

    #[test]
    fn durative_action_missing_requirement() {
        const TEST: &'static str = "(define (domain d)
           (:requirements :strips)
           (:durative-action a :parameters () :duration () :condition () :effect ()))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);

        if let Err(e) = parser.domain_top() {
            if let ErrorType::MissingRequirement { req, what: _ } = e.what {
                assert_eq!(req, Requirement::DurativeActions);
                return;
            }
        }
        panic!("Missing durative-actions requirement error not returned.");
    }

    #[test]
    fn derived_predicate_missing_requirement() {
        const TEST: &'static str = "(define (domain foo)
           (:requirements :strips)
           (:derived (a) (and)))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);

        if let Err(e) = parser.domain_top() {
            if let ErrorType::MissingRequirement { req, what: _ } = e.what {
                assert_eq!(req, Requirement::DerivedPredicates);
                return;
            }
        }
        panic!("Missing derived-predicates requirement error not returned.");
    }

    #[test]
    fn constraints_section_missing_requirement() {
        const TEST: &'static str =
            "(define (domain d) (:requirements :strips) (:constraints (and)))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);

        if let Err(e) = parser.domain_top() {
            if let ErrorType::MissingRequirement { req, what: _ } = e.what {
                assert_eq!(req, Requirement::Constraints);
                return;
            }
        }
        panic!("Missing constraints requirement error not returned.");
    }

    #[test]
    fn detect_empty_construct() {
        let test = "()";
        let tokens = scanner::scan(test);
        let parser = Parser::new(test, &tokens);
        assert!(parser.is_empty_construct());

        let test = "(and)";
        let tokens = scanner::scan(test);
        let parser = Parser::new(test, &tokens);
        assert!(!parser.is_empty_construct());

        let test = "(";
        let tokens = scanner::scan(test);
        let parser = Parser::new(test, &tokens);
        assert!(!parser.is_empty_construct());

        let test = "";
        let tokens = scanner::scan(test);
        let parser = Parser::new(test, &tokens);
        assert!(!parser.is_empty_construct());
    }

    #[test]
    fn pre_goal_empty_and() -> Result<(), Error> {
        const TEST: &'static str = "(and)";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();
        let goal = parser.pre_goal(&mut stack)?;

        assert_eq!(goal, Goal::And(vec![]));

        Ok(())
    }

    #[test]
    fn pre_goal_and() -> Result<(), Error> {
        const TEST: &'static str = "(and (and))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();
        let goal = parser.pre_goal(&mut stack)?;

        assert_eq!(goal, Goal::And(vec![Goal::And(vec![])]));

        Ok(())
    }

    #[test]
    fn pre_goal_preference_no_name() -> Result<(), Error> {
        const TEST: &'static str = "(preference (and))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();

        parser.reqs.add(Requirement::Preferences);

        let goal = parser.pre_goal(&mut stack)?;
        assert_eq!(
            goal,
            Goal::Preference("".to_string(), Box::new(Goal::And(vec![])))
        );

        Ok(())
    }

    #[test]
    fn pre_goal_preference_with_name() -> Result<(), Error> {
        const TEST: &'static str = "(preference foo (and))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();

        parser.reqs.add(Requirement::Preferences);

        let goal = parser.pre_goal(&mut stack)?;
        assert_eq!(
            goal,
            Goal::Preference("foo".to_string(), Box::new(Goal::And(vec![])))
        );

        Ok(())
    }

    #[test]
    fn pre_goal_preference_fails_without_requirement() {
        const TEST: &'static str = "(preference foo (and))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();

        if let Err(e) = parser.pre_goal(&mut stack) {
            if let ErrorType::MissingRequirement { req, what: _ } = e.what {
                assert_eq!(req, Requirement::Preferences);
                return;
            }
        }
        panic!("Missing preferences requirement error not returned.");
    }

    #[test]
    fn pre_goal_forall() -> Result<(), Error> {
        const TEST: &'static str = "(forall (?a) (and))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();

        parser.reqs.add(Requirement::UniversalPreconditions);
        let goal = parser.pre_goal(&mut stack)?;
        let p1 = Param {
            types: vec![],
            start: 9,
            end: 11,
        };
        assert_eq!(goal, Goal::Forall(vec![p1], Box::new(Goal::And(vec![]))));

        Ok(())
    }

    #[test]
    fn pre_goal_forall_fails_without_requirement() {
        const TEST: &'static str = "(forall (?a) (and))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();

        if let Err(e) = parser.pre_goal(&mut stack) {
            if let ErrorType::MissingRequirement { req, what: _ } = e.what {
                assert_eq!(req, Requirement::UniversalPreconditions);
                return;
            }
        }
        panic!("Missing  universal preconditions requirement error not returned.");
    }

    #[test]
    fn pre_goal_forwards_other_goals() -> Result<(), Error> {
        const TEST: &'static str = "(exists (?a) (and))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();

        parser.reqs.add(Requirement::ExistentialPreconditions);
        let goal = parser.pre_goal(&mut stack)?;
        let p1 = Param {
            types: vec![],
            start: 9,
            end: 11,
        };
        assert_eq!(goal, Goal::Exists(vec![p1], Box::new(Goal::And(vec![]))));

        Ok(())
    }

    #[test]
    fn goal_empty_and() -> Result<(), Error> {
        const TEST: &'static str = "(and)";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();
        let goal = parser.goal(&mut stack)?;

        assert_eq!(goal, Goal::And(vec![]));

        Ok(())
    }

    #[test]
    fn goal_and() -> Result<(), Error> {
        const TEST: &'static str = "(and (and))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();
        let goal = parser.goal(&mut stack)?;

        assert_eq!(goal, Goal::And(vec![Goal::And(vec![])]));

        Ok(())
    }

    #[test]
    fn goal_forall() -> Result<(), Error> {
        const TEST: &'static str = "(forall (?a) (and))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();

        parser.reqs.add(Requirement::UniversalPreconditions);
        let goal = parser.goal(&mut stack)?;
        let p1 = Param {
            types: vec![],
            start: 9,
            end: 11,
        };
        assert_eq!(goal, Goal::Forall(vec![p1], Box::new(Goal::And(vec![]))));

        Ok(())
    }

    #[test]
    fn goal_forall_fails_without_requirement() {
        const TEST: &'static str = "(forall (?a) (and))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();

        if let Err(e) = parser.goal(&mut stack) {
            if let ErrorType::MissingRequirement { req, what: _ } = e.what {
                assert_eq!(req, Requirement::UniversalPreconditions);
                return;
            }
        }
        panic!("Missing  universal preconditions requirement error not returned.");
    }

    #[test]
    fn goal_exists() -> Result<(), Error> {
        const TEST: &'static str = "(exists (?a) (and))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();

        parser.reqs.add(Requirement::ExistentialPreconditions);
        let goal = parser.goal(&mut stack)?;
        let p1 = Param {
            types: vec![],
            start: 9,
            end: 11,
        };
        assert_eq!(goal, Goal::Exists(vec![p1], Box::new(Goal::And(vec![]))));

        Ok(())
    }

    #[test]
    fn goal_exists_fails_without_requirement() {
        const TEST: &'static str = "(exists (?a) (and))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();

        if let Err(e) = parser.goal(&mut stack) {
            if let ErrorType::MissingRequirement { req, what: _ } = e.what {
                assert_eq!(req, Requirement::ExistentialPreconditions);
                return;
            }
        }
        panic!("Missing  existential preconditions requirement error not returned.");
    }

    #[test]
    fn goal_imply() -> Result<(), Error> {
        const TEST: &'static str = "(imply (and) (and))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();

        parser.reqs.add(Requirement::DisjunctivePreconditions);
        let goal = parser.goal(&mut stack)?;

        assert_eq!(
            goal,
            Goal::Imply(Box::new(Goal::And(vec![])), Box::new(Goal::And(vec![])))
        );

        Ok(())
    }

    #[test]
    fn goal_imply_fails_without_requirement() {
        const TEST: &'static str = "(imply (and) (and))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();

        if let Err(e) = parser.goal(&mut stack) {
            if let ErrorType::MissingRequirement { req, what: _ } = e.what {
                assert_eq!(req, Requirement::DisjunctivePreconditions);
                return;
            }
        }
        panic!("Missing disjunctive preconditions requirement error not returned.");
    }

    #[test]
    fn goal_empty_or() -> Result<(), Error> {
        const TEST: &'static str = "(or)";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();

        parser.reqs.add(Requirement::DisjunctivePreconditions);
        let goal = parser.goal(&mut stack)?;

        assert_eq!(goal, Goal::Or(vec![]));

        Ok(())
    }

    #[test]
    fn goal_or() -> Result<(), Error> {
        const TEST: &'static str = "(or (and) (and))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();

        parser.reqs.add(Requirement::DisjunctivePreconditions);
        let goal = parser.goal(&mut stack)?;

        assert_eq!(goal, Goal::Or(vec![Goal::And(vec![]), Goal::And(vec![])]));

        Ok(())
    }

    #[test]
    fn goal_or_fails_without_requirement() {
        const TEST: &'static str = "(or (and) (and))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();

        if let Err(e) = parser.goal(&mut stack) {
            if let ErrorType::MissingRequirement { req, what: _ } = e.what {
                assert_eq!(req, Requirement::DisjunctivePreconditions);
                return;
            }
        }
        panic!("Missing disjunctive preconditions requirement error not returned.");
    }

    #[test]
    fn goal_not() -> Result<(), Error> {
        const TEST: &'static str = "(not (and))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();

        parser.reqs.add(Requirement::DisjunctivePreconditions);
        let goal = parser.goal(&mut stack)?;

        assert_eq!(goal, Goal::Not(Box::new(Goal::And(vec![]))));

        Ok(())
    }

    #[test]
    fn goal_not_fails_without_requirement() {
        const TEST: &'static str = "(not (and))";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);
        let mut stack = ParamStack::new();

        if let Err(e) = parser.goal(&mut stack) {
            if let ErrorType::MissingRequirement { req, what: _ } = e.what {
                assert_eq!(req, Requirement::DisjunctivePreconditions);
                return;
            }
        }
        panic!("Missing disjunctive preconditions requirement error not returned.");
    }
}
