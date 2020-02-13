use std::{error, fmt};

use crate::tokens::{Token, TokenError, TokenType, Tokenizer};

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

struct DomainParser<'a> {
    contents: &'a str,
    tokenizer: Tokenizer<'a>,
}

impl<'a> DomainParser<'a> {
    fn new(s: &'a str) -> DomainParser<'a> {
        return DomainParser {
            contents: s,
            tokenizer: Tokenizer::new(s),
        };
    }

    fn token_str(&self, t: &Token) -> &'a str {
        t.what.to_string(self.contents)
    }

    fn top_level(&mut self) -> Result<ParseResult<'a>, ParseError<'a>> {
        self.consume(TokenType::LParen)
            .and_then(|_| self.specific_ident("define"))
            .and_then(|_| self.consume(TokenType::LParen))
            .and_then(|_| self.specific_ident("domain"))
            .and_then(|_| self.consume_ident().map(|name| ParseResult { name }))
            .and_then(|pr| self.consume(TokenType::RParen).map(|_| pr))
            .and_then(|pr| self.consume(TokenType::RParen).map(|_| pr))
    }

    fn specific_ident(&mut self, what: &'a str) -> Result<Token, ParseError<'a>> {
        self.tokenizer
            .next()
            .or_else(|err| token_error!(self, err, what))
            .and_then(|tok| {
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
        self.tokenizer
            .next()
            .or_else(|err| token_error!(self, err, what.to_string(self.contents)))
            .and_then(|tok| {
                if tok.what == what {
                    Ok(tok)
                } else {
                    expect!(self, tok, what.to_string(self.contents))
                }
            })
    }

    fn consume_ident(&mut self) -> Result<&'a str, ParseError<'a>> {
        self.tokenizer
            .next()
            .or_else(|err| token_error!(self, err, "identifier"))
            .and_then(|tok| {
                if let TokenType::Ident(_, _) = tok.what {
                    Ok(self.token_str(&tok))
                } else {
                    expect!(self, tok, "identifier")
                }
            })
    }
}

#[derive(Debug)]
pub struct ParseResult<'a> {
    name: &'a str,
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
                let p = te.pos;
                let s = &contents[p..p + 1];
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
}

impl<'a> fmt::Display for ParseErrorType<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseErrorType::Expect(et) => write!(f, "{}", et),
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
mod domain_tests {
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
        const DOMAIN: &'static str = "(define (domain foo))";

        let dom = Domain::parse(DOMAIN)?;
        assert_eq!(dom.name, "foo");

        Ok(())
    }
}
