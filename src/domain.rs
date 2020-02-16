use std::{error, fmt};

use crate::tokens::{Token, TokenError, TokenType, Tokenizer};

pub struct Domain<'a> {
    pub name: &'a str,
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
        dp.top_level().map(|pr| Domain { name: pr.name })
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

    fn next_keyword_is(&mut self, _keyword: &str) -> bool {
        false
    }

    fn check_next_is_one_of(&mut self, ttypes: &[TokenType]) -> Result<(), ParseError<'a>> {
        let tok: Token;

        if let Some(t) = self.last_token {
            tok = t
        } else {
            tok = self.tokenizer.next().or_else(|e| {
                let mut v = Vec::new();
                for tt in ttypes {
                    v.push(tt.to_string(self.contents));
                }
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

    fn check_keyword_is_one_of(&mut self, keywords: &[&'a str]) -> Result<(), ParseError<'a>> {
        let tok: Token;

        if let Some(t) = self.last_token {
            tok = t
        } else {
            tok = self.tokenizer.next().or_else(|e| {
                let mut v = Vec::new();
                for &kw in keywords {
                    v.push(kw);
                }
                Err(ParseError::from_token_error(e, self.contents, v))
            })?;
            self.last_token = Some(tok);
        }

        if let TokenType::Keyword(_, _) = tok.what {
            for &kw in keywords {
                let s = tok.what.to_string(self.contents);
                if s.eq_ignore_ascii_case(kw) {
                    return Ok(());
                }
            }
        }

        let mut v = Vec::new();
        for &kw in keywords {
            v.push(kw);
        }
        let s = tok.what.to_string(self.contents);
        Err(ParseError::expect(tok.line, tok.col, s, v))
    }

    fn top_level(&mut self) -> Result<ParseResult<'a>, ParseError<'a>> {
        self.consume(TokenType::LParen)?;
        self.specific_ident("define")?;
        self.consume(TokenType::LParen)?;
        self.specific_ident("domain")?;

        let mut pr = self.consume_ident().map(ParseResult::with_name)?;
        self.consume(TokenType::RParen)?;

        let parens = &[TokenType::LParen, TokenType::RParen];
        let top_level_keywords = [
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
        let mut top_keys = &top_level_keywords[0..9];

        self.check_next_is_one_of(parens)?;
        while self.next_token_is(TokenType::LParen) {
            self.check_keyword_is_one_of(top_keys)?;

            if top_keys.len() == 9 {
                top_keys = &top_keys[0..8];
                if self.next_keyword_is(top_level_keywords[8]) {
                    pr.add_reqs(self.parse_requirements()?);
                    self.check_next_is_one_of(parens)?;
                    continue;
                }
            }

            if top_keys.len() == 8 {
                top_keys = &top_keys[0..7];
                if self.next_keyword_is(top_level_keywords[7]) {
                    // TODO: PARSE TYPES
                    self.check_next_is_one_of(parens)?;
                    continue;
                }
            }

            if top_keys.len() == 7 {
                top_keys = &top_keys[0..6];
                if self.next_keyword_is(top_level_keywords[6]) {
                    // TODO: Check constants.
                    self.check_next_is_one_of(parens)?;
                    continue;
                }
            }

            if top_keys.len() == 6 {
                top_keys = &top_keys[0..5];
                if self.next_keyword_is(top_level_keywords[5]) {
                    // TODO: Check predicates.
                    self.check_next_is_one_of(parens)?;
                    continue;
                }
            }

            if top_keys.len() == 5 {
                top_keys = &top_keys[0..4];
                if self.next_keyword_is(top_level_keywords[4]) {
                    // TODO: Check functions.
                    self.check_next_is_one_of(parens)?;
                    continue;
                }
            }

            if top_keys.len() == 4 {
                top_keys = &top_keys[0..3];
                if self.next_keyword_is(top_level_keywords[3]) {
                    // TODO: Check constraints.
                    self.check_next_is_one_of(parens)?;
                    continue;
                }
            }

            if self.next_keyword_is(top_level_keywords[2]) {
                // TODO: Mark :action.
                self.check_next_is_one_of(parens)?;
                continue;
            }

            if self.next_keyword_is(top_level_keywords[1]) {
                // TODO: Mark :durative-action.
                self.check_next_is_one_of(parens)?;
                continue;
            }

            if self.next_keyword_is(top_level_keywords[0]) {
                // TODO: Mark :derived.
                self.check_next_is_one_of(parens)?;
                continue;
            }
        }

        self.consume(TokenType::RParen)?;
        match self.tokenizer.next() {
            Err(TokenError::EndOfInput(_, _)) => Ok(pr),
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

    fn parse_requirements(&mut self) -> Result<u32, ParseError<'a>> {
        Ok(0)
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

    fn add_reqs(&mut self, reqs: u32) {
        self.reqs = reqs
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
mod test {
    use super::*;

    #[test]
    fn check_if_domain() {
        const DOMAIN: &'static str = "(define (domain foo))";
        assert!(Domain::is_domain(DOMAIN));
    }

    #[test]
    fn check_if_not_domain() {
        const DOMAIN: &'static str = "(define (problem foo-p1))";
        assert!(!Domain::is_domain(DOMAIN));
    }

    #[test]
    fn parse_top_level_name() -> Result<(), ParseError<'static>> {
        let dom = Domain::parse("(define (domain foo))")?;
        assert_eq!(dom.name, "foo");
        Ok(())
    }

    #[test]
    fn unexpected_top_level_end_of_input() {
        if let Err(pe) = Domain::parse("(define (domain foo)") {
            match pe.what {
                ParseErrorType::Expect(et) => assert_eq!(et.expect, vec!["(", ")"]),
                _ => panic!("Invalid ParseErrorType -- have {:?}, want Expect", pe.what),
            }
        } else {
            panic!("Expected error but received successful domain parse");
        }
    }

    #[test]
    fn invalid_top_level_extra_right_paren() {
        if let Err(pe) = Domain::parse("(define (domain foo)))") {
            match pe.what {
                ParseErrorType::ExtraInput(s) => assert_eq!(s, ")"),
                _ => panic!("Invalid ParseErrorType -- have {:?}, want Expect", pe.what),
            }
        } else {
            panic!("Expected error but received successful domain parse");
        }
    }

    #[test]
    fn invalid_token_at_top_level() {
        if let Err(pe) = Domain::parse("(define (domain foo) %)") {
            match pe.what {
                ParseErrorType::Expect(et) => assert_eq!(et.expect, vec!["(", ")"]),
                _ => panic!(
                    "Invalid ParseErrorType -- have {:?}, want Expect('(', ')')",
                    pe.what
                ),
            }
        } else {
            panic!("Expected error but received successful domain parse");
        }
    }

    #[test]
    fn invalid_top_level_keyword() {
        if let Err(pe) = Domain::parse("(define (domain foo) (:foo))") {
            match pe.what {
                ParseErrorType::Expect(et) => assert_eq!(
                    et.expect,
                    vec![
                        ":derived",
                        ":durative-action",
                        ":action",
                        ":constraints",
                        ":functions",
                        ":predicates",
                        ":constants",
                        ":typing",
                        ":requirements",
                    ]
                ),
                _ => panic!("Invalid ParseErrorType -- have {:?}, want Expect", pe.what),
            }
        } else {
            panic!("Expected error but received successful domain parse");
        }
    }
}
