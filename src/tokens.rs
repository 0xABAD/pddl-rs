use std::{error, fmt};

type TokenTypeFn = fn(usize, usize) -> TokenType;
type ResultToken = Result<Token, TokenError>;

pub struct Tokenizer<'a> {
    source: &'a str,
    next_char: Option<(usize, char)>,
    chars: std::str::CharIndices<'a>,
    col: usize,
    line: usize,
}

impl<'a> Tokenizer<'a> {
    pub fn new(s: &'a str) -> Tokenizer<'a> {
        Tokenizer {
            source: s,
            next_char: None,
            chars: s.char_indices(),
            col: 1,
            line: 1,
        }
    }

    pub fn next(&mut self) -> ResultToken {
        loop {
            let mut next = self.next_char;

            self.next_char = None;
            if let None = next {
                next = self.chars.next();
            }

            if let Some((pos, ch)) = next {
                if ch == ' ' || ch == '\t' || ch == '\r' {
                    self.col += 1;
                } else if ch == '\n' {
                    self.col = 1;
                    self.line += 1;
                } else if ch == '(' {
                    return self.simple_token(TokenType::LParen, pos);
                } else if ch == ')' {
                    return self.simple_token(TokenType::RParen, pos);
                } else if ch == ';' {
                    self.comment();
                } else if ch.is_ascii_alphabetic() {
                    return Ok(self.ident(pos, ch));
                } else if ch == '?' {
                    return self.special(ch, pos, |s, e| TokenType::Variable(s, e));
                } else if ch == ':' {
                    return self.special(ch, pos, |s, e| TokenType::Keyword(s, e));
                } else if ch == '*' {
                    return self.simple_token(TokenType::Mult, pos);
                } else if ch == '/' {
                    return self.simple_token(TokenType::Div, pos);
                } else if ch == '+' {
                    return self.simple_token(TokenType::Plus, pos);
                } else if ch == '-' {
                    return self.simple_token(TokenType::Minus, pos);
                } else if ch == '=' {
                    return self.simple_token(TokenType::Equal, pos);
                } else if ch == '<' {
                    return self.maybe(TokenType::Less, pos, '=', TokenType::LessEq);
                } else if ch == '>' {
                    return self.maybe(TokenType::Greater, pos, '=', TokenType::GreaterEq);
                } else if ch.is_ascii_digit() {
                    return self.number(ch, pos);
                } else if ch == '#' {
                    return self.time_token(pos);
                } else {
                    let te = TokenInputError::new(ch, pos, self.line, self.col);
                    return Err(TokenError::InvalidInput(te));
                }
            } else {
                return Err(TokenError::EndOfInput(self.line, self.col));
            }
        }
    }

    fn simple_token(&mut self, t: TokenType, pos: usize) -> ResultToken {
        let col = self.col;
        self.col += 1;
        return Ok(Token::new(t, pos, col, self.line));
    }

    fn time_token(&mut self, pos: usize) -> ResultToken {
        if let Some((_, c)) = self.chars.next() {
            if c == 't' {
                let col = self.col;
                self.col += 2;
                return Ok(Token::new(TokenType::Time, pos, col, self.line));
            } else {
                let te = TokenInputError::new('#', pos, self.line, self.col);
                return Err(TokenError::InvalidInput(te));
            }
        } else {
            let te = TokenInputError::new('#', pos, self.line, self.col);
            return Err(TokenError::InvalidInput(te));
        }
    }

    fn number(&mut self, ch: char, start: usize) -> ResultToken {
        let col = self.col;
        let mut end = start;
        let mut dot = 0;
        let mut last = ch;

        self.col += 1;

        loop {
            let next = self.chars.next();

            if let Some((p, c)) = next {
                if c.is_ascii_digit() {
                    end = p;
                    last = c;

                    self.col += 1;
                } else if c == '.' {
                    end = p;
                    last = c;

                    self.col += 1;
                    dot += 1;
                    if dot > 1 {
                        let te = TokenInputError::new('.', p, self.line, self.col - 1);
                        return Err(TokenError::InvalidInput(te));
                    }
                } else {
                    self.next_char = next;
                    break;
                }
            } else {
                self.next_char = next;
                break;
            }
        }

        if dot == 1 && last == '.' {
            let te = TokenInputError::new('.', end, self.line, self.col - 1);
            return Err(TokenError::InvalidInput(te));
        }

        end += 1;

        let s = &self.source[start..end];
        let n: f64 = s.parse().unwrap();

        return Ok(Token::new(
            TokenType::Number(n, start, end),
            start,
            col,
            self.line,
        ));
    }

    fn maybe(
        &mut self,
        tok: TokenType,
        pos: usize,
        maybe: char,
        maybe_t: TokenType,
    ) -> ResultToken {
        if let Some((p, c)) = self.chars.next() {
            if c == maybe {
                let result = self.simple_token(maybe_t, pos);
                self.col += 1;
                return result;
            } else {
                self.next_char = Some((p, c));
                return self.simple_token(tok, pos);
            }
        } else {
            return self.simple_token(tok, pos);
        }
    }

    fn comment(&mut self) {
        self.col += 1;
        loop {
            let next = self.chars.next();
            if let Some((_, ch)) = next {
                if ch == '\n' {
                    self.next_char = next;
                    return;
                }
                self.col += 1;
            } else {
                return;
            }
        }
    }

    fn ident(&mut self, first_pos: usize, first_char: char) -> Token {
        let mut last_pos = first_pos;
        let mut last_char = first_char;
        let start_col = self.col;

        self.col += 1;

        loop {
            let next = self.chars.next();
            if let Some((pos, ch)) = next {
                if ch.is_ascii_alphanumeric() || ch == '_' || ch == '-' {
                    last_pos = pos;
                    last_char = ch;
                    self.col += 1;
                } else {
                    self.next_char = next;
                    last_pos += last_char.len_utf8();

                    let tt = TokenType::Ident(first_pos, last_pos);
                    return Token::new(tt, first_pos, start_col, self.line);
                }
            } else {
                last_pos += last_char.len_utf8();

                let tt = TokenType::Ident(first_pos, last_pos);
                return Token::new(tt, first_pos, start_col, self.line);
            }
        }
    }

    fn special(&mut self, ch: char, pos: usize, ttype: TokenTypeFn) -> ResultToken {
        let col = self.col;

        self.col += 1;

        if let Some((p, ch)) = self.chars.next() {
            if ch.is_ascii_alphabetic() {
                let t = self.ident(p, ch);
                match t.what {
                    TokenType::Ident(s, e) => {
                        return Ok(Token::new(ttype(s - 1, e), pos, col, self.line));
                    }
                    tt => panic!(
                        "Tokenizer::ident didn't return an identifier, returned {:#?} instead",
                        tt
                    ),
                }
            } else {
                let te = TokenInputError::new(ch, pos, self.line, col);
                return Err(TokenError::InvalidInput(te));
            }
        } else {
            let te = TokenInputError::new(ch, pos, self.line, col);
            return Err(TokenError::InvalidInput(te));
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Token {
    pub what: TokenType,
    pub pos: usize,
    pub col: usize,
    pub line: usize,
}

impl Token {
    pub fn new(what: TokenType, pos: usize, col: usize, line: usize) -> Token {
        Token {
            what,
            pos,
            col,
            line,
        }
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum TokenType {
    LParen,
    RParen,
    Plus,
    Mult,
    Div,
    Minus,
    Equal,
    Less,
    LessEq,
    Greater,
    GreaterEq,
    Time,
    Ident(usize, usize),
    Variable(usize, usize),
    Keyword(usize, usize),
    Number(f64, usize, usize),
}

impl<'a> TokenType {
    pub fn to_string(self, contents: &'a str) -> &'a str {
        match self {
            TokenType::LParen => "(",
            TokenType::RParen => ")",
            TokenType::Plus => "+",
            TokenType::Mult => "*",
            TokenType::Div => "/",
            TokenType::Minus => "-",
            TokenType::Equal => "=",
            TokenType::Less => "<",
            TokenType::LessEq => "<=",
            TokenType::Greater => ">",
            TokenType::GreaterEq => ">=",
            TokenType::Time => "#t",
            TokenType::Ident(s, e) => &contents[s..e],
            TokenType::Variable(s, e) => &contents[s..e],
            TokenType::Keyword(s, e) => &contents[s..e],
            TokenType::Number(_, s, e) => &contents[s..e],
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum TokenError {
    EndOfInput(usize, usize),
    InvalidInput(TokenInputError),
}

#[derive(Debug, PartialEq)]
pub struct TokenInputError {
    pub what: char,
    pub pos: usize,
    pub col: usize,
    pub line: usize,
}

impl TokenInputError {
    pub fn new(what: char, pos: usize, line: usize, col: usize) -> TokenInputError {
        TokenInputError {
            what,
            pos,
            col,
            line,
        }
    }
}

impl error::Error for TokenError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

impl fmt::Display for TokenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenError::EndOfInput(line, col) => write!(f, "{}:{}: end of input found", line, col),
            TokenError::InvalidInput(e) => {
                write!(f, "{}:{} -- invalid input '{}'", e.line, e.col, e.what)
            }
        }
    }
}

#[cfg(test)]
mod token_tests {
    use super::*;

    #[test]
    fn can_create() {
        let t = Tokenizer::new("");
        assert_eq!(t.col, 1, "col not properly initialized");
        assert_eq!(t.line, 1, "line not properly initialized");
    }

    #[test]
    fn tokenize_basics() -> Result<(), TokenError> {
        const TEST_STRING: &'static str = "
;; a comment
 (
   (foo ;; another comment ₳
    a42bar- )
    q_ux-baz)
 )
bar";

        let mut tz = Tokenizer::new(TEST_STRING);

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::LParen);
        assert_eq!(t.pos, 15, "invalid position");
        assert_eq!(t.col, 2, "invalid column");
        assert_eq!(t.line, 3, "invalid line");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::LParen);
        assert_eq!(t.pos, 20, "invalid position");
        assert_eq!(t.col, 4, "invalid column");
        assert_eq!(t.line, 4, "invalid line");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Ident(21, 24));
        assert_eq!(t.pos, 21, "invalid position");
        assert_eq!(t.col, 5, "invalid column");
        assert_eq!(t.line, 4, "invalid line");
        assert_eq!(&TEST_STRING[21..24], "foo");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Ident(52, 59));
        assert_eq!(t.pos, 52, "invalid position");
        assert_eq!(t.col, 5, "invalid column");
        assert_eq!(t.line, 5, "invalid line");
        assert_eq!(&TEST_STRING[52..59], "a42bar-");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::RParen);
        assert_eq!(t.pos, 60, "invalid position");
        assert_eq!(t.col, 13, "invalid column");
        assert_eq!(t.line, 5, "invalid line");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Ident(66, 74));
        assert_eq!(t.pos, 66, "invalid position");
        assert_eq!(t.col, 5, "invalid column");
        assert_eq!(t.line, 6, "invalid line");
        assert_eq!(&TEST_STRING[66..74], "q_ux-baz");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::RParen);
        assert_eq!(t.pos, 74, "invalid position");
        assert_eq!(t.col, 13, "invalid column");
        assert_eq!(t.line, 6, "invalid line");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::RParen);
        assert_eq!(t.pos, 77, "invalid position");
        assert_eq!(t.col, 2, "invalid column");
        assert_eq!(t.line, 7, "invalid line");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Ident(79, 82));
        assert_eq!(t.pos, 79, "invalid position");
        assert_eq!(t.col, 1, "invalid column");
        assert_eq!(t.line, 8, "invalid line");
        assert_eq!(&TEST_STRING[79..82], "bar");

        Ok(())
    }

    #[test]
    fn tokenize_variables() -> Result<(), TokenError> {
        const TEST_STRING: &'static str = " )  ?foo  ?bar";

        let mut tz = Tokenizer::new(TEST_STRING);

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::RParen);
        assert_eq!(t.pos, 1, "invalid position");
        assert_eq!(t.col, 2, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Variable(4, 8));
        assert_eq!(t.pos, 4, "invalid position");
        assert_eq!(t.col, 5, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(&TEST_STRING[4..8], "?foo");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Variable(10, 14));
        assert_eq!(t.pos, 10, "invalid position");
        assert_eq!(t.col, 11, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(&TEST_STRING[10..14], "?bar");

        Ok(())
    }

    #[test]
    fn tokenize_keywords() -> Result<(), TokenError> {
        const TEST_STRING: &'static str = " (  :foo  :bar_baz";

        let mut tz = Tokenizer::new(TEST_STRING);

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::LParen);
        assert_eq!(t.pos, 1, "invalid position");
        assert_eq!(t.col, 2, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Keyword(4, 8));
        assert_eq!(t.pos, 4, "invalid position");
        assert_eq!(t.col, 5, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(&TEST_STRING[4..8], ":foo");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Keyword(10, 18));
        assert_eq!(t.pos, 10, "invalid position");
        assert_eq!(t.col, 11, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(&TEST_STRING[10..18], ":bar_baz");

        Ok(())
    }

    #[test]
    fn tokenize_operators() -> Result<(), TokenError> {
        const TEST_STRING: &'static str = "+ - * /";

        let mut tz = Tokenizer::new(TEST_STRING);

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Plus);
        assert_eq!(t.pos, 0, "invalid position");
        assert_eq!(t.col, 1, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Minus);
        assert_eq!(t.pos, 2, "invalid position");
        assert_eq!(t.col, 3, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Mult);
        assert_eq!(t.pos, 4, "invalid position");
        assert_eq!(t.col, 5, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Div);
        assert_eq!(t.pos, 6, "invalid position");
        assert_eq!(t.col, 7, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        Ok(())
    }

    #[test]
    fn tokenize_equality() -> Result<(), TokenError> {
        const TEST_STRING: &'static str = "< <= > >= =";

        let mut tz = Tokenizer::new(TEST_STRING);

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Less);
        assert_eq!(t.pos, 0, "invalid position");
        assert_eq!(t.col, 1, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::LessEq);
        assert_eq!(t.pos, 2, "invalid position");
        assert_eq!(t.col, 3, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Greater);
        assert_eq!(t.pos, 5, "invalid position");
        assert_eq!(t.col, 6, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::GreaterEq);
        assert_eq!(t.pos, 7, "invalid position");
        assert_eq!(t.col, 8, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Equal);
        assert_eq!(t.pos, 10, "invalid position");
        assert_eq!(t.col, 11, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        Ok(())
    }

    #[test]
    fn tokenize_time() -> Result<(), TokenError> {
        const TEST_STRING: &'static str = "(#t)";

        let mut tz = Tokenizer::new(TEST_STRING);

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::LParen);
        assert_eq!(t.pos, 0, "invalid position");
        assert_eq!(t.col, 1, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Time);
        assert_eq!(t.pos, 1, "invalid position");
        assert_eq!(t.col, 2, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::RParen);
        assert_eq!(t.pos, 3, "invalid position");
        assert_eq!(t.col, 4, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        Ok(())
    }

    #[test]
    fn tokenize_number() -> Result<(), TokenError> {
        const TEST_STRING: &'static str = "42 13.25foo 0012";

        let mut tz = Tokenizer::new(TEST_STRING);

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Number(42.0, 0, 2));
        assert_eq!(t.pos, 0, "invalid position");
        assert_eq!(t.col, 1, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(&TEST_STRING[0..2], "42");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Number(13.25, 3, 8));
        assert_eq!(t.pos, 3, "invalid position");
        assert_eq!(t.col, 4, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(&TEST_STRING[3..8], "13.25");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Ident(8, 11));
        assert_eq!(t.pos, 8, "invalid position");
        assert_eq!(t.col, 9, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = tz.next()?;
        assert_eq!(t.what, TokenType::Number(12.0, 12, 16));
        assert_eq!(t.pos, 12, "invalid position");
        assert_eq!(t.col, 13, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(&TEST_STRING[12..16], "0012");

        Ok(())
    }
}
