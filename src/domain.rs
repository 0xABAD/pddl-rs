use std::{error, fmt};

use crate::tokens::{Token, TokenError, TokenType, Tokenizer};

pub struct Domain<'a> {
    pub name: &'a str,
    reqs: u32,
}

impl<'a> Domain<'a> {
    pub fn is_domain(contents: &str) -> bool {
        let mut dp = DomainParser::new(contents);
        dp.consume(TokenType::LParen)
            .and_then(|_| dp.specific_ident("define"))
            .and_then(|_| dp.consume(TokenType::LParen))
            .and_then(|_| dp.specific_ident("domain"))
            .is_ok()
    }

    pub fn parse(contents: &str) -> Result<Domain, ParseError> {
        let mut dp = DomainParser::new(contents);
        dp.top_level().map(|pr| Domain {
            name: pr.name,
            reqs: pr.reqs,
        })
    }

    pub fn has_requirement(&self, r: Requirement) -> bool {
        let b = self.reqs & (1 << r.index());
        if r == Requirement::Strips {
            return self.reqs == 0 || b > 0;
        }
        b > 0
    }
}

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
    fn index(self) -> usize {
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

    fn from_index(index: usize) -> Requirement {
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

macro_rules! expect {
    ($dp:tt, $tok:tt, $($arg:tt)*) => {
        {
            let s = $dp.token_str(&$tok);
            let v = vec![$($arg)*];
            (Err(ParseError::expect($tok.line, $tok.col, s, v)))
        }
    }
}

macro_rules! token_error {
    ($dp:tt, $err:tt, $($arg:tt)*) => {
        {
            let v = vec![$($arg)*];
            (Err(ParseError::from_token_error($err, $dp.contents, v)))
        }
    }
}

struct DomainParser<'a> {
    contents: &'a str,
    tokenizer: Tokenizer<'a>,
    last_token: Option<Token>,
}

impl<'a> DomainParser<'a> {
    fn new(s: &'a str) -> DomainParser<'a> {
        return DomainParser {
            contents: s,
            tokenizer: Tokenizer::new(s),
            last_token: None,
        };
    }

    fn token_str(&self, t: &Token) -> &'a str {
        t.what.to_string(self.contents)
    }

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
            ":typing",
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
                if self.next_keyword_is(TOP_LEVEL_KEYWORDS[7]) {
                    // TODO: PARSE TYPES
                    self.check_next_token_is_one_of(&PARENS)?;
                    continue;
                }
            }

            if top_keys.len() == 7 {
                top_keys = &top_keys[0..6];
                if self.next_keyword_is(TOP_LEVEL_KEYWORDS[6]) {
                    // TODO: Check constants.
                    self.check_next_token_is_one_of(&PARENS)?;
                    continue;
                }
            }

            if top_keys.len() == 6 {
                top_keys = &top_keys[0..5];
                if self.next_keyword_is(TOP_LEVEL_KEYWORDS[5]) {
                    // TODO: Check predicates.
                    self.check_next_token_is_one_of(&PARENS)?;
                    continue;
                }
            }

            if top_keys.len() == 5 {
                top_keys = &top_keys[0..4];
                if self.next_keyword_is(TOP_LEVEL_KEYWORDS[4]) {
                    // TODO: Check functions.
                    self.check_next_token_is_one_of(&PARENS)?;
                    continue;
                }
            }

            if top_keys.len() == 4 {
                top_keys = &top_keys[0..3];
                if self.next_keyword_is(TOP_LEVEL_KEYWORDS[3]) {
                    // TODO: Check constraints.
                    self.check_next_token_is_one_of(&PARENS)?;
                    continue;
                }
            }

            if self.next_keyword_is(TOP_LEVEL_KEYWORDS[2]) {
                // TODO: Mark :action.
                self.check_next_token_is_one_of(&PARENS)?;
                continue;
            }

            if self.next_keyword_is(TOP_LEVEL_KEYWORDS[1]) {
                // TODO: Mark :durative-action.
                self.check_next_token_is_one_of(&PARENS)?;
                continue;
            }

            if self.next_keyword_is(TOP_LEVEL_KEYWORDS[0]) {
                // TODO: Mark :derived.
                self.check_next_token_is_one_of(&PARENS)?;
                continue;
            }
        }

        self.consume(TokenType::RParen)?;
        match self.tokenizer.next() {
            Err(TokenError::EndOfInput(_, _)) => Ok(result),
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

    fn next_token(&mut self) -> Result<Token, TokenError> {
        if let Some(t) = self.last_token {
            self.last_token = None;
            Ok(t)
        } else {
            self.tokenizer.next()
        }
    }

    fn expect_next(&mut self, what: &'a str) -> Result<Token, ParseError<'a>> {
        self.next_token().or_else(|e| token_error!(self, e, what))
    }

    fn next_token_is(&mut self, what: TokenType) -> bool {
        if let Some(t) = self.last_token {
            if t.what == what {
                self.last_token = None;
                return true;
            }
        }
        false
    }

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

    fn consume_ident(&mut self) -> Result<&'a str, ParseError<'a>> {
        self.expect_next("identifier").and_then(|tok| {
            if let TokenType::Ident(_, _) = tok.what {
                Ok(self.token_str(&tok))
            } else {
                expect!(self, tok, "identifier")
            }
        })
    }

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

    fn next_is_one_of(&mut self, words: &[&'a str]) -> Result<usize, ParseError<'a>> {
        let idx = self.check_next_is_one_of(words)?;
        self.last_token = None;
        Ok(idx)
    }

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
}

#[derive(Debug)]
struct ParseResult<'a> {
    name: &'a str,
    reqs: u32,
}

impl<'a> ParseResult<'a> {
    fn with_name(name: &'a str) -> ParseResult<'a> {
        ParseResult { name, reqs: 0 }
    }

    fn add_requirements(&mut self, reqs: u32) {
        self.reqs = self.reqs | reqs
    }
}

#[derive(Debug, PartialEq)]
pub struct ParseError<'a> {
    pub what: ParseErrorType<'a>,
    pub line: usize,
    pub col: usize,
}

impl<'a> ParseError<'a> {
    fn expect(line: usize, col: usize, have: &'a str, expecting: Vec<&'a str>) -> ParseError<'a> {
        let et = ExpectToken {
            have,
            expect: expecting,
        };
        ParseError {
            what: ParseErrorType::Expect(et),
            line,
            col,
        }
    }

    fn from_token_error(
        e: TokenError,
        contents: &'a str,
        expecting: Vec<&'a str>,
    ) -> ParseError<'a> {
        match e {
            TokenError::EndOfInput(line, col) => {
                ParseError::expect(line, col, "end of input", expecting)
            }
            TokenError::InvalidInput(te) => {
                let s = te.to_string(contents);
                ParseError::expect(te.line, te.col, s, expecting)
            }
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

#[derive(Debug, PartialEq)]
pub enum ParseErrorType<'a> {
    Expect(ExpectToken<'a>),
    ExtraInput(&'a str),
}

impl<'a> fmt::Display for ParseErrorType<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseErrorType::Expect(et) => write!(f, "{}", et),
            ParseErrorType::ExtraInput(s) => write!(f, "Extra input detected: {}", s),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct ExpectToken<'a> {
    pub have: &'a str,
    pub expect: Vec<&'a str>,
}

impl<'a> fmt::Display for ExpectToken<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Expecting ")?;

        if self.expect.len() == 1 {
            write!(f, "{}, found {}", self.expect[0], self.have)
        } else {
            f.write_str("either ")?;

            let end = self.expect.len() - 1;
            for i in 0..end {
                write!(f, "{}, ", self.expect[i])?;
            }
            write!(f, "or {}, found {}", self.expect[end], self.have)
        }
    }
}

#[cfg(test)]
#[path = "domain_test.rs"]
mod test;
