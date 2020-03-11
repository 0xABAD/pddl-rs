use std::{error, fmt, iter::Iterator};

use super::{
    reqs::{Reqs, Requirement},
    scanner::{Token, TokenType},
    types::{TypeId, Types},
};

pub struct Parser<'a> {
    src: &'a str,        // Original source that was scanned.
    tokens: &'a [Token], // Scanned tokens to be parsed.
    tokpos: usize,       // Current index into `tokens`.
    col: usize,          // Current column of parse.
    line: usize,         // Current line of parse.
    reqs: Reqs,          // Known requirements.
                         // types: Option<&'a Types>, // Collected type declarations.
}

macro_rules! try_next {
    ($parser:tt, $($arg:tt)*) => {
        {
            $parser.next()
                .ok_or_else(|| Error::expect($parser.line, $parser.col, "end of input", &[$($arg)*]))
        }
    }
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
        let mut top_keys = &TOP_LEVEL_KEYWORDS[0..9];
        let mut parse = Parse::default();

        parse.name = domain_name;

        loop {
            let paren = self.expect(&[TokenType::LParen, TokenType::RParen], &[])?;
            if paren.what == TokenType::RParen {
                break;
            }

            let top_key = self.expect(top_keys, &[])?;

            if top_keys.len() == 9 {
                top_keys = &top_keys[0..8];
                if top_key.what == TokenType::Requirements {
                    parse.reqs = self.requirements()?;
                    self.reqs = parse.reqs;
                    continue;
                }
            }

            if top_keys.len() == 8 {
                top_keys = &top_keys[0..7];
                if top_key.what == TokenType::Types {
                    if !self.reqs.has(Requirement::Typing) {
                        return Err(self.missing(Requirement::Typing, ":types"));
                    }
                    parse.types = self.parse_types()?;
                    continue;
                }
            }

            if top_keys.len() == 7 {
                top_keys = &top_keys[0..6];
                if top_key.what == TokenType::Constants {
                    parse.const_pos = self.tokpos;
                    self.balance_parens();
                    continue;
                }
            }

            if top_keys.len() == 6 {
                top_keys = &top_keys[0..5];
                if top_key.what == TokenType::Predicates {
                    parse.pred_pos = self.tokpos;
                    self.balance_parens();
                    continue;
                }
            }

            if top_keys.len() == 5 {
                top_keys = &top_keys[0..4];
                if top_key.what == TokenType::Functions {
                    parse.func_pos = self.tokpos;
                    self.balance_parens();
                    continue;
                }
            }

            if top_keys.len() == 4 {
                top_keys = &top_keys[0..3];
                if top_key.what == TokenType::Constraints {
                    if !self.reqs.has(Requirement::Constraints) {
                        return Err(self.missing(Requirement::Constraints, ":constraints section"));
                    }
                    parse.constraints_pos = self.tokpos;
                    self.balance_parens();
                    continue;
                }
            }

            if top_key.what == TokenType::Action {
                parse.action_pos.push(self.tokpos);
                self.balance_parens();
                continue;
            }

            if top_key.what == TokenType::DurativeAction {
                if !self.reqs.has(Requirement::DurativeActions) {
                    return Err(self.missing(Requirement::DurativeActions, ":durative-action"));
                }
                parse.daction_pos.push(self.tokpos);
                self.balance_parens();
                continue;
            }

            if top_key.what == TokenType::Derived {
                if !self.reqs.has(Requirement::DerivedPredicates) {
                    return Err(self.missing(Requirement::DerivedPredicates, ":derived predicate"));
                }
                parse.derived_pos.push(self.tokpos);
                self.balance_parens();
                continue;
            }
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

    /// `consume` consumes and returns the next token whose `TokenType` is
    /// is equal to `what`. If that is not the case then a `ParseError` is
    /// returned that expects `what`.
    fn consume(&mut self, what: TokenType) -> Result<&Token, Error> {
        let tok = try_next!(self, what.as_str())?;
        if tok.what != what {
            let have = tok.to_str(self.src);
            return Err(Error::expect(self.line, self.col, have, &[what.as_str()]));
        }
        Ok(tok)
    }

    /// `ident` consumes the next input if the next token is an identifier
    /// that matches `what`.
    fn ident(&mut self, what: &str) -> Result<&Token, Error> {
        let tok = try_next!(self, what)?;
        let have = tok.to_str(self.src);
        if tok.what != TokenType::Ident || !have.eq_ignore_ascii_case(what) {
            return Err(Error::expect(self.line, self.col, have, &[what]));
        }
        Ok(tok)
    }

    /// `next_is_and` returns true if the next token in the stream has
    /// a `TokenType` of `what` and fulfills the predicate of `and`.  If
    /// false then the token is not consumed.
    fn next_is_and<F>(&mut self, what: TokenType, and: F) -> bool
    where
        F: FnOnce(&Token) -> bool,
    {
        if self.tokpos >= self.tokens.len() {
            return false;
        }
        let t = &self.tokens[self.tokpos];
        if t.what == what && and(t) {
            self.tokpos += 1;
            self.col = t.col;
            self.line = t.line;
            true
        } else {
            false
        }
    }

    /// `next_is` is like calling `next_is_and` where `and` is a tautology.
    fn next_is(&mut self, what: TokenType) -> bool {
        self.next_is_and(what, |_| true)
    }

    // /// `ident_is` returns true if the next token in the stream is an identifier
    // /// and whose string contents are case insensitive match to `what`.  If false
    // /// then the token is not consumed.
    // fn ident_is(&mut self, what: &str) -> bool {
    //     let src = self.src;
    //     self.next_is_and(TokenType::Ident, |t| {
    //         t.to_str(src).eq_ignore_ascii_case(what)
    //     })
    // }

    fn expect(&mut self, ttypes: &[TokenType], idents: &[&str]) -> Result<&Token, Error> {
        let token = self.next();

        if token.is_none() {
            let mut v: Vec<&str> = ttypes.iter().map(|tt| tt.as_str()).collect();
            v.extend_from_slice(idents);
            return Err(Error::expect(self.line, self.col, "end of input", &v));
        }
        let tok = token.unwrap();

        let mut is_one_of = ttypes
            .iter()
            .skip_while(|&&tt| tok.what != tt)
            .next()
            .is_some();

        let name = tok.to_str(self.src);
        let is_ident = tok.what == TokenType::Ident;

        is_one_of = is_one_of
            || idents
                .iter()
                .skip_while(|s| !is_ident || name.eq_ignore_ascii_case(s))
                .next()
                .is_some();

        if !is_one_of {
            let have = tok.to_str(self.src);
            let mut v: Vec<&str> = ttypes.iter().map(|tt| tt.as_str()).collect();
            v.extend_from_slice(idents);
            return Err(Error::expect(self.line, self.col, have, &v));
        }
        Ok(tok)
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
        let tok = self.expect(&ALL[1..], &[])?;
        reqs.add(tok.what.to_requirement());

        loop {
            let tok = self.expect(ALL, &[])?;
            if tok.what == TokenType::RParen {
                return Ok(reqs);
            }
            reqs.add(tok.what.to_requirement());
        }
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
            let src = self.src;
            let tok = self.expect(&[TokenType::Ident, TokenType::RParen], &[])?;

            if tok.what == TokenType::RParen {
                return Ok(types);
            }

            // Basic type declaration (:types vehicle).
            let name = tok.to_str(src);
            let mut siblings: Vec<(TypeId, Token)> = vec![(types.insert(name), *tok)];

            if name.eq_ignore_ascii_case("object") {
                return Err(self.semantic("object declared as a derived type"));
            }

            // Have one type now collect more to get a set of types that
            // inherit from another (:types first second - parent).
            'more_types: loop {
                let tok = self.expect(
                    &[TokenType::Ident, TokenType::Minus, TokenType::RParen],
                    &[],
                )?;

                if tok.what == TokenType::RParen {
                    return Ok(types);
                }
                if tok.what == TokenType::Ident {
                    let s = tok.to_str(src);
                    if s.eq_ignore_ascii_case("object") {
                        return Err(self.semantic("object declared as a derived type"));
                    }
                    siblings.push((types.insert(s), *tok));
                } else {
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
        let tok = self.expect(&[TokenType::Ident, TokenType::LParen], &[])?;

        if tok.what == TokenType::Ident {
            on_type(tok)?;
        } else if tok.what == TokenType::LParen {
            self.ident("either")?;

            // Must have at least one either type.
            let first = self.consume(TokenType::Ident)?;
            on_type(first)?;

            // Get the rest of the either parent types.
            loop {
                let tok = self.expect(&[TokenType::Ident, TokenType::RParen], &[])?;
                if tok.what == TokenType::RParen {
                    return Ok(());
                }
                on_type(tok)?;
            }
        }
        Ok(())
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
    // what: ParsingWhat,          // What was parsed by this result.
    pub name: &'a str,           // Name of a domain.
    pub reqs: Reqs,              // Requirements of the domain represented as bit vector.
    pub types: Types,            // Types extracted from the domain.
    pub const_pos: usize, // Token position within the PDDL source where constants are located.
    pub pred_pos: usize,  // Token position within the PDDL source where predicates are located.
    pub func_pos: usize,  // Token position within the PDDL source where functions are located.
    pub constraints_pos: usize, // Token position within the PDDL source where constraints are located.
    pub action_pos: Vec<usize>, // Token positions where :actions begin in the PDDL source.
    pub daction_pos: Vec<usize>, // Token positions where :durative-actions begin in the PDDL source.
    pub derived_pos: Vec<usize>, // Token positions where :derived functions begin in the PDDL source.
                                 // predicates: Vec<Predicate>, // Parsed predicate declarations.
                                 // functions: Vec<Function>,   // Parsed function declarations.
                                 // constants: Vec<Constant>,   // Parsed constant declarations.
                                 // action: Option<Action>,     // Parsed action definition.
}

impl<'a> Default for Parse<'a> {
    fn default() -> Self {
        Parse {
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
    fn next_is() {
        const TEST: &'static str = ":REQUIREMENTS ( :action)";

        let tokens = scanner::scan(TEST);
        let mut parser = Parser::new(TEST, &tokens);

        assert!(parser.next_is(TokenType::Requirements));
        assert!(parser.next_is(TokenType::LParen));
        assert!(parser.next_is(TokenType::Action));
        assert!(parser.next_is(TokenType::RParen));
    }

    #[test]
    fn requirements() -> Result<(), Error> {
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
