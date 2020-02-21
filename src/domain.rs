use std::collections::{HashMap, HashSet};
use std::{error, fmt};

use crate::tokens::{Token, TokenError, TokenType, Tokenizer};

type TypeId = usize;

/// `Domain` represents the final output from parsing the contents
/// representing some PDDL domain.
pub struct Domain<'a> {
    /// The parsed domain name.
    pub name: &'a str,

    reqs: u32,    // Parsed (:requirements) as a bit vector.
    types: Types, // Parsed (:types).
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
    pub fn parse(contents: &str) -> Result<Domain, ParseError> {
        let mut dp = DomainParser::new(contents);
        dp.top_level().map(|pr| Domain {
            name: pr.name,
            reqs: pr.reqs,
            types: pr.types,
        })
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

/// `expect!` provides a concise way of returning a `ParseError` from
/// a given `Token` and arbitrary number of arguments that represent the
/// expected tokens.
macro_rules! expect {
    ($dp:tt, $tok:tt, $($arg:tt)*) => {
        {
            let s = $dp.token_str(&$tok);
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

/// `DomainParser` maintains the state necessary to parse a portion of
/// of a PDDL domain.
struct DomainParser<'a> {
    contents: &'a str,         // Source contents that will be parsed.
    tokenizer: Tokenizer<'a>,  // Scans contents.
    last_token: Option<Token>, // Last scanned token that hasn't been consumed.
}

impl<'a> DomainParser<'a> {
    /// Creates a new `DomainParser` where `source` entails the entire
    /// PDDL domain to be parsed.
    fn new(source: &'a str) -> DomainParser<'a> {
        return DomainParser {
            contents: source,
            tokenizer: Tokenizer::new(source),
            last_token: None,
        };
    }

    /// `token_str` returns the string form of the `Token`, `t`.
    fn token_str(&self, t: &Token) -> &'a str {
        t.what.to_string(self.contents)
    }

    /// `top_level` parses the top level forms of a PDDL domain.
    ///
    /// While the entire contents of the `DomainParser` are scanned only the
    /// `:requirements` and `:typing` section of the domain, if they exist,
    /// are parsed.  All other constructs are partially scanned to just
    /// determine their starting location within the contents of the
    /// `DomainParser` and that they form a balance construct (i.e. have
    /// balanced parenthesis.
    fn top_level(&mut self) -> Result<ParseResult<'a>, ParseError<'a>> {
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
                    result.constants = self.balance_parens()?;
                    self.check_next_token_is_one_of(&PARENS)?;
                    continue;
                }
            }

            if top_keys.len() == 6 {
                top_keys = &top_keys[0..5];
                if self.next_keyword_is(TOP_LEVEL_KEYWORDS[5]) {
                    result.predicates = self.balance_parens()?;
                    self.check_next_token_is_one_of(&PARENS)?;
                    continue;
                }
            }

            if top_keys.len() == 5 {
                top_keys = &top_keys[0..4];
                if self.next_keyword_is(TOP_LEVEL_KEYWORDS[4]) {
                    result.functions = self.balance_parens()?;
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
                result.actions.push(self.balance_parens()?);
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
                let s = te.to_string(self.contents);
                Err(ParseError {
                    what: ParseErrorType::ExtraInput(s),
                    col: te.col,
                    line: te.line,
                })
            }
            Ok(t) => {
                let s = t.what.to_string(self.contents);
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
    fn expect_next(&mut self, what: &'a str) -> Result<Token, ParseError<'a>> {
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

    /// `next_keyword_is` is like `next_token_is` but only applies if the
    /// previous unconsumed token is a `TokenType::Keyword` and its string
    /// form is case insensitive equal to `keyword`.
    fn next_keyword_is(&mut self, keyword: &str) -> bool {
        if let Some(t) = self.last_token {
            if let TokenType::Keyword(_, _) = t.what {
                let s = t.what.to_string(self.contents);
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
            if let TokenType::Keyword(_, _) = t.what {
                let s = self.token_str(&t);
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
    fn specific_ident(&mut self, what: &'a str) -> Result<Token, ParseError<'a>> {
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

    /// `consume` consumes and returns the next token whose `TokenType` is
    /// is equal to `what`. If that is not the case then a `ParseError` is
    /// returned that expects `what`.
    fn consume(&mut self, what: TokenType) -> Result<Token, ParseError<'a>> {
        self.expect_next(what.to_string(self.contents))
            .and_then(|tok| {
                if tok.what == what {
                    Ok(tok)
                } else {
                    expect!(self, tok, what.to_string(self.contents))
                }
            })
    }

    /// `consume_ident` consumes the next token that needs to be an
    /// identifier and returns the string form of that identifier.
    fn consume_ident(&mut self) -> Result<&'a str, ParseError<'a>> {
        self.expect_next("identifier").and_then(|tok| {
            if let TokenType::Ident(_, _) = tok.what {
                Ok(self.token_str(&tok))
            } else {
                expect!(self, tok, "identifier")
            }
        })
    }

    /// `check_next_token_is_one_of` checks to see if the next token is
    /// one of `ttypes`.  Note this does not consume the checked token as
    /// further decisions may be made depending on the value of the next
    /// token.
    fn check_next_token_is_one_of(&mut self, ttypes: &[TokenType]) -> Result<(), ParseError<'a>> {
        let tok: Token;

        if let Some(t) = self.last_token {
            tok = t
        } else {
            tok = self.tokenizer.next().or_else(|e| {
                let v = ttypes
                    .iter()
                    .map(|tt| tt.to_string(self.contents))
                    .collect();
                Err(ParseError::from_token_error(e, self.contents, v))
            })?;
            self.last_token = Some(tok);
        }

        for &tt in ttypes {
            if tok.what == tt {
                return Ok(());
            }
        }

        let mut v = Vec::new();
        for tt in ttypes {
            v.push(tt.to_string(self.contents));
        }
        let s = tok.what.to_string(self.contents);
        Err(ParseError::expect(tok.line, tok.col, s, v))
    }

    /// `check_next_is_one_of` is like `check_next_token_is_one_of` but
    /// checks if the string form of the next token is a case insensitive
    /// match to any of the elements of `words`.  Note, that like
    /// `check_next_token_is_one_of` this method does not consume the
    /// the next token.  The Ok result returned is the index of the match
    /// into the `words` slice.
    fn check_next_is_one_of(&mut self, words: &[&'a str]) -> Result<usize, ParseError<'a>> {
        let tok: Token;

        if let Some(t) = self.last_token {
            tok = t
        } else {
            tok = self.tokenizer.next().or_else(|e| {
                let mut v = Vec::new();
                for &w in words {
                    v.push(w);
                }
                Err(ParseError::from_token_error(e, self.contents, v))
            })?;
            self.last_token = Some(tok);
        }

        for i in 0..words.len() {
            let w = words[i];
            let s = tok.what.to_string(self.contents);
            if s.eq_ignore_ascii_case(w) {
                return Ok(i);
            }
        }

        let mut v = Vec::new();
        for &w in words {
            v.push(w);
        }
        let s = tok.what.to_string(self.contents);
        Err(ParseError::expect(tok.line, tok.col, s, v))
    }

    /// `next_is_one_of` is exactly like `check_next_is_one_of` but
    /// also consumes the token.
    fn next_is_one_of(&mut self, words: &[&'a str]) -> Result<usize, ParseError<'a>> {
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
    fn parse_requirements(&mut self) -> Result<u32, ParseError<'a>> {
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

    /// `parse_types` extracts all the `:types` out from a PDDL domain.  Aside
    /// from syntax errors, semantic errors are returned if `object` is
    /// attempted to be a derived type or a type has circular inheritance.
    fn parse_types(&mut self) -> Result<Types, ParseError<'a>> {
        let mut ptypes = Types::default();

        ptypes.insert("object");

        loop {
            let tok = next_token!(self, "identifier", ")")?;

            if tok.what == TokenType::RParen {
                return Ok(ptypes);
            } else if let TokenType::Ident(_, _) = tok.what {
                // Basic type declaration (:types vehicle).
                let name = self.token_str(&tok);
                let mut siblings: Vec<TypeId> = vec![ptypes.insert(name)];

                if name.eq_ignore_ascii_case("object") {
                    return Err(ParseError::semantic(
                        tok.line,
                        tok.col,
                        "object declared as a derived type".to_string(),
                    ));
                }

                // Have one type now collect more to get a set of types that
                // inherit from another (:types first second - parent).
                'inherit_types: loop {
                    let tok = next_token!(self, "identifier", "-", ")")?;

                    if let TokenType::Ident(_, _) = tok.what {
                        let s = self.token_str(&tok);
                        if s.eq_ignore_ascii_case("object") {
                            return Err(ParseError::semantic(
                                tok.line,
                                tok.col,
                                "object declared as a derived type".to_string(),
                            ));
                        }
                        siblings.push(ptypes.insert(s));
                    } else if tok.what == TokenType::RParen {
                        // No more types, we're done.
                        return Ok(ptypes);
                    } else if tok.what == TokenType::Minus {
                        // Reached inherintance, collect single parent or multiple
                        // (i.e. "either") types.
                        let tok = next_token!(self, "identifier", "(")?;

                        if let TokenType::Ident(_, _) = tok.what {
                            // Single parent case.
                            let name = self.token_str(&tok);
                            ptypes.insert_with_siblings(name, &siblings, tok.line, tok.col)?;
                            break 'inherit_types;
                        } else if tok.what == TokenType::LParen {
                            // Multiple parents case.
                            self.specific_ident("either")?;

                            // Must have at least one parent type.
                            let name = self.consume_ident()?;
                            ptypes.insert_with_siblings(name, &siblings, tok.line, tok.col)?;

                            // Get the rest of the either parent types.
                            'either_types: loop {
                                let t = next_token!(self, "identifier", ")")?;
                                if let TokenType::Ident(_, _) = t.what {
                                    let name = self.token_str(&t);
                                    ptypes.insert_with_siblings(name, &siblings, t.line, t.col)?;
                                } else if t.what == TokenType::RParen {
                                    break 'either_types;
                                } else {
                                    return expect!(self, tok, "identifier", ")");
                                }
                            }
                            break 'inherit_types;
                        } else {
                            return expect!(self, tok, "identifier", "(");
                        }
                    } else {
                        return expect!(self, tok, "identifier", "-", ")");
                    }
                }
            } else {
                return expect!(self, tok, "identifier", ")");
            }
        }
    }

    /// `balance_parens` consumes tokens until the current count of parenthesis
    /// reaches zero.  Initially, the count is one since it is expected that the
    /// first left paren has already been consumed.  On a successful balance then
    /// the first token that is consumed is returned.
    fn balance_parens(&mut self) -> Result<Token, ParseError<'a>> {
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
            if let TokenType::LParen = tok.what {
                count += 1;
            } else if let TokenType::RParen = tok.what {
                count -= 1;
                if count == 0 {
                    return Ok(first);
                }
            }
            tok = next()?;
        }
    }
}

/// `Types` is the collection of all types found from `:types` section
/// within a PDDL domain.
#[derive(Debug)]
struct Types {
    types: HashMap<String, TypeId>, // Lowercased type names to their assigned TypeId.
    parent_types: Vec<HashSet<TypeId>>, // Immediate parent TypeIds.  Vector is indexed by the child TypeId.
    child_types: Vec<HashSet<TypeId>>, // Immediate child TypeIds.  Vector is indexed by the parent TypeId.
    type_id: TypeId,                   // A TypeId counter.
}

impl Default for Types {
    fn default() -> Self {
        Types {
            types: HashMap::new(),
            type_id: 0,
            parent_types: vec![],
            child_types: vec![],
        }
    }
}

impl Types {
    /// `insert` inserts `s` and assigns it a `TypeId` if it hasn't already
    /// been seen.
    fn insert(&mut self, s: &str) -> TypeId {
        let id = s.to_ascii_lowercase();
        if self.types.contains_key(&id) {
            *self.types.get(&id).unwrap()
        } else {
            let tid = self.type_id;
            self.types.insert(id, tid);
            self.type_id += 1;
            self.parent_types.push(HashSet::new());
            self.child_types.push(HashSet::new());
            tid
        }
    }

    /// `insert_with_siblings` will call `insert` and then `insert_parent`
    /// and `insert_child` for every sibling in `siblings`.  Returns a
    /// semantic error if circular inherintance is detected.
    fn insert_with_siblings<'a>(
        &mut self,
        name: &'a str,
        siblings: &Vec<TypeId>,
        line: usize,
        col: usize,
    ) -> Result<(), ParseError<'a>> {
        let parent = self.insert(name);
        for &child in siblings {
            self.insert_parent(child, parent);
            self.insert_child(parent, child);
            if self.has_circular_types(child) {
                return Err(ParseError::semantic(
                    line,
                    col,
                    format!("{} has circular inherintance", name),
                ));
            }
        }
        Ok(())
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
}

/// `ParseResult` encompasses a result returned from of the different
/// methods of a `DomainParser`.
#[derive(Debug)]
struct ParseResult<'a> {
    name: &'a str,         // Name of a domain.
    reqs: u32,             // Requirements of the domain represented as bit vector.
    types: Types,          // Types extracted from the domain.
    constants: Token,      // Token within the PDDL source where constants are located.
    predicates: Token,     // Token within the PDDL source where predicates are located.
    functions: Token,      // Token within the PDDL source where functions are located.
    constraints: Token,    // Token within the PDDL source where constraints are located.
    actions: Vec<Token>,   // Tokens where :actions begin in the PDDL source.
    duratives: Vec<Token>, // Tokens where :durative-actions begin in the PDDL source.
    deriveds: Vec<Token>,  // Tokens where :derived functions begin in the PDDL source.
}

impl<'a> ParseResult<'a> {
    /// `with_name` returns a ParseResult that has a name of `name`.  All
    /// other fields have their zero value.
    fn with_name(name: &'a str) -> ParseResult<'a> {
        ParseResult {
            name,
            reqs: 0,
            types: Types::default(),
            constants: Token::new(TokenType::LParen, 0, 0, 0),
            predicates: Token::new(TokenType::LParen, 0, 0, 0),
            functions: Token::new(TokenType::LParen, 0, 0, 0),
            constraints: Token::new(TokenType::LParen, 0, 0, 0),
            actions: vec![],
            duratives: vec![],
            deriveds: vec![],
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
pub struct ParseError<'a> {
    /// The specific parse error that occurred.
    pub what: ParseErrorType<'a>,
    /// The line number the error occurred on.
    pub line: usize,
    /// The column number the error occurred on.
    pub col: usize,
}

impl<'a> ParseError<'a> {
    /// `expect` returns a `ParseError` for an error that occurred
    /// on line, `line`, column, `col`, and has a value of `have` where
    /// `expect` are the expected values at the time of parse.
    fn expect(line: usize, col: usize, have: &'a str, expect: Vec<&'a str>) -> ParseError<'a> {
        ParseError {
            what: ParseErrorType::Expect { have, expect },
            line,
            col,
        }
    }

    /// `from_token_error` converts a `TokenError` into a `ParseError`.  `contents`
    /// are the original source contents of the `DomainParser` and `expecting` is
    /// are the values that were expected at the time of the parse.
    fn from_token_error(
        e: TokenError,
        contents: &'a str,
        expecting: Vec<&'a str>,
    ) -> ParseError<'a> {
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
    fn missing(line: usize, col: usize, req: Requirement, what: &'a str) -> ParseError<'a> {
        ParseError {
            what: ParseErrorType::MissingRequirement { req, what },
            line: line,
            col: col,
        }
    }

    /// `semantic` returns a `ParseError` that represents some semantic
    /// error in the PDDL language (i.e. predicate not defined).
    fn semantic(line: usize, col: usize, what: String) -> ParseError<'a> {
        ParseError {
            what: ParseErrorType::SemanticError(what),
            line,
            col,
        }
    }
}

impl<'a> error::Error for ParseError<'a> {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

impl<'a> fmt::Display for ParseError<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: error: {}", self.line, self.col, self.what)
    }
}

/// `ParseErrorType` are the different type of `ParseError`s that
/// can occur during parsing a PDDL domain.
#[derive(Debug, PartialEq)]
pub enum ParseErrorType<'a> {
    /// Where the parser expected a specific token but received something else.
    Expect { have: &'a str, expect: Vec<&'a str> },
    /// Signals that extra input was detected at the end of the PDDL domain.
    ExtraInput(&'a str),
    /// Signals that a `Requirement` is missing for a specific construct which
    /// is described by the second parameter.
    MissingRequirement { req: Requirement, what: &'a str },
    /// Signals a semantic error that has occurred.
    SemanticError(String),
}

impl<'a> fmt::Display for ParseErrorType<'a> {
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
        }
    }
}

#[cfg(test)]
#[path = "domain_test.rs"]
mod test;
