use std::{error, fmt};

use crate::tokens::{Token, TokenType, Tokenizer};

pub struct DomainParser<'a> {
    contents: &'a str,
}

impl<'a> DomainParser<'a> {
    pub fn new(s: &'a str) -> DomainParser<'a> {
        return DomainParser { contents: s };
    }

    pub fn is_domain(&self) -> bool {
        let mut tz = Tokenizer::new(self.contents);
        self.consume(&mut tz, TokenType::LParen)
            .and_then(|_| self.consume_ident(&mut tz, "define"))
            .and_then(|_| self.consume(&mut tz, TokenType::LParen))
            .and_then(|_| self.consume_ident(&mut tz, "domain"))
            .is_ok()
    }

    fn consume(&self, tz: &mut Tokenizer, what: TokenType) -> Result<Token, ParseError> {
        match tz.next() {
            Ok(t) => {
                if t.what == what {
                    Ok(t)
                } else {
                    Err(ParseError {})
                }
            }
            Err(_) => Err(ParseError {}),
        }
    }

    fn consume_ident(&self, tz: &mut Tokenizer, what: &str) -> Result<Token, ParseError> {
        match tz.next() {
            Ok(t) => {
                if let TokenType::Ident(s, e) = t.what {
                    let ident = &self.contents[s..e];
                    if ident.eq_ignore_ascii_case(what) {
                        Ok(t)
                    } else {
                        Err(ParseError {})
                    }
                } else {
                    Err(ParseError {})
                }
            }
            Err(_) => Err(ParseError {}),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct ParseError {}

impl error::Error for ParseError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "parse error")
    }
}

#[cfg(test)]
mod domain_tests {
    use super::*;

    #[test]
    fn check_if_domain() {
        const TEST_STRING: &'static str = "(define (domain foo))";
        let dp = DomainParser::new(TEST_STRING);
        assert!(dp.is_domain());
    }

    #[test]
    fn check_if_not_domain() {
        const TEST_STRING: &'static str = "(define (problem foo-p1))";
        let dp = DomainParser::new(TEST_STRING);
        assert!(!dp.is_domain());
    }
}
