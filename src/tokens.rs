use std::{error, fmt};

type TokenTypeFn = fn(usize, usize) -> TokenType;
type ResultToken = Result<Token, TokenError>;

/// Tokenizer that recognizes PDDL tokens.
///
/// Tokenizer works off some source contents and the returned tokens refer
/// to positions within that source.  This means that no strings are created
/// or copied -- everything is based off the positions of the Tokenizer's
/// source.
///
/// Legal tokens are derived from the PDDL 3.1 specification found from
/// (here)[http://www.plg.inf.uc3m.es/ipc2011-deterministic/attachments/OtherContributions/kovacs-pddl-3.1-2011.pdf].
/// Since that document does not precisely specify lexical conventions this
/// tokenizer only accepts ASCII characters to form valid tokens.  Comments,
/// however, may contain any valid UTF-8 text as those lexemes are ignored by
/// the tokenizer.
pub struct Tokenizer<'a> {
    source: &'a str,                  // Source content to extract tokens from.
    next_char: Option<(usize, char)>, // Next character extracted from source but not yet consumed.
    chars: std::str::CharIndices<'a>, // Iterator over source.
    col: usize,                       // Current column tokenized within source.
    line: usize,                      // Current line tokenized within source.
}

impl<'a> Tokenizer<'a> {
    /// New returns a Tokenizer that scans source for tokens.  The column and
    /// line number of the Tokenizer both begin at one.
    pub fn new(source: &'a str) -> Tokenizer<'a> {
        Tokenizer {
            source,
            next_char: None,
            chars: source.char_indices(),
            col: 1,
            line: 1,
        }
    }

    /// With_offset returns a Tokenizer that scans source.  Tokens returned will be
    /// based off the positions of the column and line.  This allows creating
    /// a specific Tokenizer that begins at some offset of the full source
    /// contents but stil report the correct column and line numbers of scanned
    /// tokens.
    pub fn with_offset(source: &'a str, column: usize, line: usize) -> Tokenizer<'a> {
        Tokenizer {
            source,
            next_char: None,
            chars: source.char_indices(),
            col: column,
            line,
        }
    }

    /// Next returns the next scanned token from its source input.  Returns a TokenError
    /// if the scanned input is not recognized as a valid PDDL token.
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
                return Err(TokenError::EndOfInput {
                    line: self.line,
                    col: self.col,
                });
            }
        }
    }

    /// Simple_token simply returns a Token whose TokenType is t while also
    /// incrementing the column number of the Tokenizer.
    fn simple_token(&mut self, t: TokenType, pos: usize) -> ResultToken {
        let col = self.col;
        self.col += 1;
        return Ok(Token::new(t, pos, col, self.line));
    }

    /// Time_token attempts to return the token representation of a PDDL time
    /// construct (i.e. "#t").
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

    /// Number attempts to return the token representation of a PDDL number.
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

    /// Maybe attempts to return the token with the TokenType of `maybe_t`
    /// if and only if the next scanned character in the input is equal to
    /// to `maybe_c`.  If that doesn't hold the next scanned character is
    /// not consumed and the Token with the TokenType of `tok` is returned.
    fn maybe(
        &mut self,
        tok: TokenType,
        pos: usize,
        maybe_c: char,
        maybe_t: TokenType,
    ) -> ResultToken {
        if let Some((p, c)) = self.chars.next() {
            if c == maybe_c {
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

    /// Comment continues scanning until a newline (i.e. "\n") is encountered,
    /// which is not consumed by the scanner.
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

    /// Ident returns a Token that represents a legal PDDL identifier, which is
    /// text that begins with a letter (i.e. 'a..z' or 'A..Z') is followed by
    /// zero or more letters, digits, '-', or '_' characters.
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

    /// Special is like `Tokenizer::ident` but the Token returned has a
    /// TokenType that is the result of calling `ttype` with the start
    /// and end positions of the token.  Since the character that forms
    /// the special TokenType has already been consumed then it is possible
    /// to return a TokenError if the next character does not begin a
    /// valid identifier.
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

/// Token is primary object that is returned from calling `Tokenizer::next`.
#[derive(Debug, PartialEq, Clone, Copy)]
pub struct Token {
    /// What type of token this one is.
    pub what: TokenType,
    /// Position of where the token was found from Tokenizer's source contents.
    pub pos: usize,
    /// Column number of where the token was found.
    pub col: usize,
    /// Line number of where the token was found.
    pub line: usize,
}

impl Default for Token {
    fn default() -> Self {
        Token::new(TokenType::LParen, 0, 0, 0)
    }
}

impl Token {
    /// New returns a new Token.
    pub fn new(what: TokenType, pos: usize, col: usize, line: usize) -> Token {
        Token {
            what,
            pos,
            col,
            line,
        }
    }
}

/// TokenType specifies what kind of token was scanned.
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
    /// First parameter is the start position from the source while the
    /// second is the position from the source immediately after last
    /// character of the scanned identifier.
    Ident(usize, usize),
    /// First parameter is the start position from the source while the
    /// second is the position from the source immediately after last
    /// character of the scanned variable.
    Variable(usize, usize),
    /// First parameter is the start position from the source while the
    /// second is the position from the source immediately after last
    /// character of the scanned keyword.
    Keyword(usize, usize),
    /// The first parameter is final parsed number.  The second parameter is
    /// the start position from the source while the third is the position
    /// from the source immediately after last character of the scanned
    /// number.
    Number(f64, usize, usize),
}

impl<'a> TokenType {
    /// To_string returns the string representation of the scanned
    /// TokenType.  `contents` should be the exact source contents
    /// that was passed to the `Tokenizer` on its construction.
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

/// TokenError is the error type returned when the Tokenizer
/// does not recognize the next scanned character from the
/// source or the end of input has been reached.
#[derive(Debug, PartialEq)]
pub enum TokenError {
    /// EndOfInput is not necessarily an error despite being returned as
    /// one.
    EndOfInput { line: usize, col: usize },
    /// InvalidInput represents a scanned character that was not
    /// recognized by the Tokenizer.  The TokenInputError contains
    /// all information of the invalid scanned input.
    InvalidInput(TokenInputError),
}

/// TokenInputError provides the specifics for a `TokenError::InvalidInput`.
#[derive(Debug, PartialEq)]
pub struct TokenInputError {
    /// Character scanned that caused the error.
    pub what: char,
    /// The position within the `Tokenizer`s source of where `what` was scanned.
    pub pos: usize,
    /// Column number of where the error occurred.
    pub col: usize,
    /// Line number of where the error occurred.
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

    /// To_string returns the string form of the scanned character from
    /// the `TokenInputError`.  `contents` should be the exact source that
    /// was passed into the construction of `Tokenizer`.
    pub fn to_string<'a>(&self, contents: &'a str) -> &'a str {
        let p = self.pos;
        let n = self.what.len_utf8();
        &contents[p..p + n]
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
            TokenError::EndOfInput { line, col } => {
                write!(f, "{}:{}: end of input found", line, col)
            }
            TokenError::InvalidInput(e) => {
                write!(f, "{}:{} -- invalid input '{}'", e.line, e.col, e.what)
            }
        }
    }
}

#[cfg(test)]
mod test {
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
