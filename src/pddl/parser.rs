use std::{collections::HashMap, error, fmt, iter::Iterator};

use super::{
    reqs::{Reqs, Requirement},
    scanner::{Token, TokenType},
    types::{TypeId, Types},
    Action, ConstId, Constant, FuncId, Function, Param, PredId, Predicate,
};

pub struct Parser<'a> {
    pub src: &'a str,             // Original source that was scanned.
    pub tokens: &'a [Token],      // Scanned tokens to be parsed.
    pub tokpos: usize,            // Current index into `tokens`.
    pub col: usize,               // Current column of parse.
    pub line: usize,              // Current line of parse.
    pub what: ParsingWhat,        // What is specifically being parsed.
    pub reqs: Reqs,               // Known requirements.
    pub types: Option<&'a Types>, // Collected type declarations.
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
        }
    }

    pub fn domain_top(&mut self) -> Result<Parse, Error> {
        self.consume(TokenType::LParen)?;
        self.ident("define")?;
        self.consume(TokenType::LParen)?;
        self.ident("domain")?;

        let domain_name = self.consume(TokenType::Ident)?.to_str(self.src);
        self.consume(TokenType::RParen)?;

        const TOP_LEVEL_KEYWORDS: [TokenType; 9] = [
            TokenType::Derived,
            TokenType::DurativeAction,
            TokenType::Action,
            TokenType::Constraints,
            TokenType::Functions,
            TokenType::Predicates,
            TokenType::Constants,
            TokenType::Types,
            TokenType::Requirements,
        ];
        let mut top_count = 9;
        let mut parse = Parse::default();

        parse.name = domain_name;

        loop {
            if let Ok(_) = self.next_is(TokenType::RParen) {
                break;
            }
            if let Err(have) = self.next_is(TokenType::LParen) {
                return Err(Error::expect(self.line, self.col, have, &["(", ")"]));
            }
            let last_count = top_count;

            if top_count == 9 {
                top_count -= 1;
                if let Ok(_) = self.next_is(TokenType::Requirements) {
                    parse.reqs = self.requirements()?;
                    self.reqs = parse.reqs;
                    continue;
                }
            }

            if top_count == 8 {
                top_count -= 1;
                if let Ok(_) = self.next_is(TokenType::Types) {
                    if !self.reqs.has(Requirement::Typing) {
                        return Err(self.missing(Requirement::Typing, ":types"));
                    }
                    parse.types = self.parse_types()?;
                    continue;
                }
            }

            if top_count == 7 {
                top_count -= 1;
                if let Ok(_) = self.next_is(TokenType::Constants) {
                    parse.const_pos = self.tokpos;
                    self.balance_parens();
                    continue;
                }
            }

            if top_count == 6 {
                top_count -= 1;
                if let Ok(_) = self.next_is(TokenType::Predicates) {
                    parse.pred_pos = self.tokpos;
                    self.balance_parens();
                    continue;
                }
            }

            if top_count == 5 {
                top_count -= 1;
                if let Ok(_) = self.next_is(TokenType::Functions) {
                    parse.func_pos = self.tokpos;
                    self.balance_parens();
                    continue;
                }
            }

            if top_count == 4 {
                top_count -= 1;
                if let Ok(_) = self.next_is(TokenType::Constraints) {
                    if !self.reqs.has(Requirement::Constraints) {
                        return Err(self.missing(Requirement::Constraints, ":constraints section"));
                    }
                    parse.constraints_pos = self.tokpos;
                    self.balance_parens();
                    continue;
                }
            }

            if let Ok(_) = self.next_is(TokenType::Action) {
                parse.action_pos.push(self.tokpos);
                self.balance_parens();
                continue;
            }

            if let Ok(_) = self.next_is(TokenType::DurativeAction) {
                if !self.reqs.has(Requirement::DurativeActions) {
                    return Err(self.missing(Requirement::DurativeActions, ":durative-action"));
                }
                parse.daction_pos.push(self.tokpos);
                self.balance_parens();
                continue;
            }

            if let Ok(_) = self.next_is(TokenType::Derived) {
                if !self.reqs.has(Requirement::DerivedPredicates) {
                    return Err(self.missing(Requirement::DerivedPredicates, ":derived predicate"));
                }
                parse.derived_pos.push(self.tokpos);
                self.balance_parens();
                continue;
            }

            return Err(self.expect(&TOP_LEVEL_KEYWORDS[0..last_count]));
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

        if let Some(t) = self.next() {
            let have = t.to_str(self.src);
            return Error::expect(t.line, t.col, have, &what);
        } else {
            return Error::expect(self.line, self.col, "end of input", &what);
        }
    }

    /// `consume` consumes and returns the next token whose `TokenType` is
    /// is equal to `what`. If that is not the case then a `ParseError` is
    /// returned that expects `what`.
    fn consume(&mut self, what: TokenType) -> Result<&Token, Error> {
        let tok = self
            .next()
            .ok_or_else(|| Error::expect(self.line, self.col, "end of input", &[what.as_str()]))?;

        if tok.what != what {
            let have = tok.to_str(self.src);
            return Err(Error::expect(self.line, self.col, have, &[what.as_str()]));
        }
        Ok(tok)
    }

    /// `ident` consumes the next input if the next token is an identifier
    /// that matches `what`.
    fn ident(&mut self, what: &str) -> Result<&Token, Error> {
        let tok = self
            .next()
            .ok_or_else(|| Error::expect(self.line, self.col, "end of input", &[what]))?;

        let have = tok.to_str(self.src);
        if tok.what != TokenType::Ident || !have.eq_ignore_ascii_case(what) {
            return Err(Error::expect(self.line, self.col, have, &[what]));
        }
        Ok(tok)
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

    // /// `ident_is` returns true if the next token in the stream is an identifier
    // /// and whose string contents are case insensitive match to `what`.  If false
    // /// then the token is not consumed.
    // fn ident_is(&mut self, what: &str) -> Option<&Token> {
    //     let src = self.src;
    //     self.next_is_and(TokenType::Ident, |t| {
    //         t.to_str(src).eq_ignore_ascii_case(what)
    //     })
    // }

    /// `peek` return the next token without consuming it from the stream.
    fn peek(&self) -> Option<&Token> {
        if self.tokpos >= self.tokens.len() {
            None
        } else {
            Some(&self.tokens[self.tokpos])
        }
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
        const ALL: &[TokenType] = &[
            TokenType::RParen,
            TokenType::Strips,
            TokenType::Typing,
            TokenType::Equality,
            TokenType::NegativePreconditions,
            TokenType::DisjunctivePreconditions,
            TokenType::ExistentialPreconditions,
            TokenType::UniversalPreconditions,
            TokenType::QuantifiedPreconditions,
            TokenType::ConditionalEffects,
            TokenType::Fluents,
            TokenType::NumericFluents,
            TokenType::ObjectFluents,
            TokenType::Adl,
            TokenType::DurativeActions,
            TokenType::DurationInequalities,
            TokenType::ContinuousEffects,
            TokenType::DerivedPredicates,
            TokenType::TimedInitialLiterals,
            TokenType::Preferences,
            TokenType::Constraints,
            TokenType::ActionCosts,
        ];
        // Parse the first requirement where it is expected to be at
        // least one requriement.
        let mut reqs = Reqs::default();
        reqs.add(self.parse_requirement(ALL)?);

        loop {
            if let Ok(_) = self.next_is(TokenType::RParen) {
                return Ok(reqs);
            }
            reqs.add(self.parse_requirement(ALL)?);
        }
    }

    /// `parse_requirement` is helper for `requirements`.
    fn parse_requirement(&mut self, all: &[TokenType]) -> Result<Requirement, Error> {
        for &r in all {
            if let Ok(_) = self.next_is(r) {
                return Ok(r.to_requirement());
            }
        }
        Err(self.expect(all))
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

            if let Ok(_) = self.next_is(TokenType::RParen) {
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
                if let Ok(_) = self.next_is(TokenType::RParen) {
                    return Ok(types);
                } else if let Ok(tok) = self.next_is(TokenType::Ident) {
                    let s = tok.to_str(src);
                    if s.eq_ignore_ascii_case("object") {
                        return Err(self.semantic("object declared as a derived type"));
                    }
                    siblings.push((types.insert(s), *tok));
                } else if let Ok(_) = self.next_is(TokenType::Minus) {
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
        } else if let Ok(_) = self.next_is(TokenType::LParen) {
            self.ident("either")?;

            // Must have at least one either type.
            let first = self.consume(TokenType::Ident)?;
            on_type(first)?;

            // Get the rest of the either parent types.
            loop {
                if let Ok(_) = self.next_is(TokenType::RParen) {
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
            if let Ok(_) = self.next_is(TokenType::RParen) {
                break;
            } else if let Err(_) = self.next_is(TokenType::LParen) {
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
            if let Ok(_) = self.next_is(TokenType::RParen) {
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
            } else if let Ok(_) = self.next_is(TokenType::LParen) {
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
            } else if let Ok(_) = self.next_is(TokenType::Minus) {
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
        if let Ok(_) = self.next_is(TokenType::RParen) {
            return Ok(sig);
        } else if let Ok(tok) = self.next_is(TokenType::Variable) {
            var_names.push(tok.to_str(self.src));
            sig.params.push(Param::default());
        } else {
            return Err(self.expect(&[TokenType::Variable, TokenType::RParen]));
        }

        // Get the rest of the variables and their types if they have some.
        loop {
            if let Ok(_) = self.next_is(TokenType::RParen) {
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
            } else if let Ok(_) = self.next_is(TokenType::Minus) {
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
            } else if let Ok(_) = self.next_is(TokenType::Minus) {
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

        action.line = act_token.line;
        action.col = act_token.col;

        self.consume(TokenType::Parameters)?;
        action.params = self.typed_list_variable()?;

        result.what = ParsingWhat::Action;
        result.action = Some(action);

        Ok(result)
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

/// `Signature` encapsulates the parsed result of a predicate or
/// function declaration (i.e. '(foo ?a ?b - object ?c - (either bar baz))' ).
struct Signature {
    name: String,       // Name of the predicate or function (e.g. 'foo').
    params: Vec<Param>, // Parameters of the declaration (e.g. '?a', '?b', etc.).
}

impl Signature {
    /// `lookup_key` returns a key that can be used to see if the Signature
    /// has already been declared.  The key will be a combination of the formula's
    /// name along with its parameter arity and is composed of characters that is
    /// impossible to be a valid identifier.
    fn lookup_key(&self) -> String {
        format!("{}-**-{}-**-", self.name, self.params.len())
    }
}

impl TokenType {
    /// `to_requirement` transforms the `TokenType` to its equivilant Requirement.
    /// This method will panic if there is no such equivilant.
    fn to_requirement(self) -> Requirement {
        match self {
            TokenType::Strips => Requirement::Strips,
            TokenType::Typing => Requirement::Typing,
            TokenType::Equality => Requirement::Equality,
            TokenType::NegativePreconditions => Requirement::NegativePreconditions,
            TokenType::DisjunctivePreconditions => Requirement::DisjunctivePreconditions,
            TokenType::ExistentialPreconditions => Requirement::ExistentialPreconditions,
            TokenType::UniversalPreconditions => Requirement::UniversalPreconditions,
            TokenType::QuantifiedPreconditions => Requirement::QuantifiedPreconditions,
            TokenType::ConditionalEffects => Requirement::ConditionalEffects,
            TokenType::Fluents => Requirement::Fluents,
            TokenType::NumericFluents => Requirement::NumericFluents,
            TokenType::ObjectFluents => Requirement::ObjectFluents,
            TokenType::Adl => Requirement::Adl,
            TokenType::DurativeActions => Requirement::DurativeActions,
            TokenType::DurationInequalities => Requirement::DurationInequalities,
            TokenType::ContinuousEffects => Requirement::ContinuousEffects,
            TokenType::DerivedPredicates => Requirement::DerivedPredicates,
            TokenType::TimedInitialLiterals => Requirement::TimedInitialLiterals,
            TokenType::Preferences => Requirement::Preferences,
            TokenType::Constraints => Requirement::Constraints,
            TokenType::ActionCosts => Requirement::ActionCosts,
            _ => panic!("no such Requirement for TokenType {:?}", self),
        }
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

        assert!(parser.next_is(TokenType::Requirements).is_ok());
        assert!(parser.next_is(TokenType::LParen).is_ok());
        assert!(parser.next_is(TokenType::Action).is_ok());
        assert!(parser.next_is(TokenType::RParen).is_ok());
    }

    #[test]
    fn parse_requirements() -> Result<(), Error> {
        const TEST: &'static str = ":typing :equality)";

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
}
