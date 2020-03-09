use std::{collections::HashMap, iter::Iterator, str::CharIndices};

/// `scan` builds a `Scanner` and scans `src` for every possible token.
pub fn scan(src: &str) -> Vec<Token> {
    Scanner::new(src).collect()
}

/// `Scanner` that recognizes PDDL tokens.
///
/// `Scanner` works off some source contents and the returned tokens refer
/// to positions within that source.  This means that no strings are created
/// or copied -- everything is based off the positions of the `Scanner`'s
/// source.
///
/// Legal tokens are derived from the PDDL 3.1 specification found from
/// (here)[http://www.plg.inf.uc3m.es/ipc2011-deterministic/attachments/OtherContributions/kovacs-pddl-3.1-2011.pdf].
/// Since that document does not precisely specify lexical conventions this
/// tokenizer only accepts ASCII characters to form valid tokens.  Comments,
/// however, may contain any valid UTF-8 text as those lexemes are ignored by
/// the tokenizer.
pub struct Scanner<'a> {
    next: Option<(usize, char)>, // Next character extracted from source but not yet consumed.
    chars: CharIndices<'a>,      // Iterator over source.
    col: usize,                  // Current column tokenized within source.
    line: usize,                 // Current line tokenized within source.
    pending: Option<Token>,      // A scanned token that hasn't been consumed.
    keywords: HashMap<&'static str, TokenType>, // Mapping of PDDL keywords to their TokenType equivilant.
    src: &'a str,                               // The source contents to be scanned.
}

impl<'a> Scanner<'a> {
    pub fn new(src: &'a str) -> Self {
        let keywords = [
            (":strips", TokenType::Strips),
            (":typing", TokenType::Typing),
            (":equality", TokenType::Equality),
            (":negative-preconditions", TokenType::NegativePreconditions),
            (
                ":disjunctive-preconditions",
                TokenType::DisjunctivePreconditions,
            ),
            (
                ":existential-preconditions",
                TokenType::ExistentialPreconditions,
            ),
            (
                ":universal-preconditions",
                TokenType::UniversalPreconditions,
            ),
            (
                ":quantified-preconditions",
                TokenType::QuantifiedPreconditions,
            ),
            (":conditional-effects", TokenType::ConditionalEffects),
            (":fluents", TokenType::Fluents),
            (":numeric-fluents", TokenType::NumericFluents),
            (":object-fluents", TokenType::ObjectFluents),
            (":adl", TokenType::Adl),
            (":durative-actions", TokenType::DurativeActions),
            (":duration-inequalities", TokenType::DurationInequalities),
            (":continuous-effects", TokenType::ContinuousEffects),
            (":derived-predicates", TokenType::DerivedPredicates),
            (":timed-initial-literals", TokenType::TimedInitialLiterals),
            (":preferences", TokenType::Preferences),
            (":constraints", TokenType::Constraints),
            (":action-costs", TokenType::ActionCosts),
            (":types", TokenType::Types),
            (":constants", TokenType::Constants),
            (":predicates", TokenType::Predicates),
            (":functions", TokenType::Functions),
            (":action", TokenType::Action),
            (":durative-action", TokenType::DurativeAction),
            (":precondition", TokenType::Precondition),
            (":effect", TokenType::Effect),
            (":parameters", TokenType::Parameters),
            (":condition", TokenType::Condition),
            (":duration", TokenType::Duration),
            (":derived", TokenType::Derived),
            (":domain", TokenType::Domain),
            (":objects", TokenType::Objects),
            (":init", TokenType::Init),
            (":goal", TokenType::Goal),
            (":metric", TokenType::Metric),
        ]
        .iter()
        .cloned()
        .collect();

        Scanner {
            next: None,
            pending: None,
            chars: src.char_indices(),
            col: 1,
            line: 1,
            keywords,
            src,
        }
    }

    /// `next` returns the next possible token.

    /// `single` simply returns a Token whose TokenType is t while also
    /// incrementing the column number of the Tokenizer.
    fn single(&mut self, what: TokenType, pos: usize) -> Token {
        let col = self.col;
        self.col += 1;
        return Token {
            what,
            pos,
            end: pos + 1,
            col,
            line: self.line,
        };
    }

    /// `comment` continues scanning until a newline (i.e. "\n") is encountered,
    /// which is not consumed by the scanner.
    fn comment(&mut self) {
        self.col += 1;
        loop {
            let next = self.chars.next();
            if let Some((_, ch)) = next {
                if ch == '\n' {
                    self.next = next;
                    return;
                }
                self.col += 1;
            } else {
                return;
            }
        }
    }

    /// `ident` returns a Token that represents a legal PDDL identifier, which is
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
                    self.next = next;
                    last_pos += last_char.len_utf8();
                    break;
                }
            } else {
                last_pos += last_char.len_utf8();
                break;
            }
        }
        Token {
            what: TokenType::Ident,
            pos: first_pos,
            end: last_pos,
            col: start_col,
            line: self.line,
        }
    }

    /// `special` is like `Scanner::ident` but the Token returned has a
    /// TokenType of `what`.  Since the character that forms the special
    /// `TokenType` has already been consumed then it is possible to
    /// return a `Token` with a `TokenType` of `TokenType::Invalid` if the
    /// next character does not begin a valid identifier.
    fn special(&mut self, pos: usize, what: TokenType) -> Token {
        let col = self.col;

        self.col += 1;

        let next = self.chars.next();
        if let &Some((p, ch)) = &next {
            if ch.is_ascii_alphabetic() {
                let t = self.ident(p, ch);
                return Token {
                    pos,
                    col,
                    what: what,
                    end: t.end,
                    line: self.line,
                };
            }
        }

        self.next = next;
        return Token {
            pos,
            col,
            what: TokenType::Invalid,
            end: pos + 1,
            line: self.line,
        };
    }

    /// `maybe` attempts to return the token with the `TokenType` of `maybe_t`
    /// if and only if the next scanned character in the input is equal to
    /// to `maybe_c`.  If that doesn't hold the next scanned character is
    /// not consumed and the `Token` with the `TokenType` of `what` is returned.
    fn maybe(&mut self, what: TokenType, pos: usize, maybe_c: char, maybe_t: TokenType) -> Token {
        if let Some((p, c)) = self.chars.next() {
            if c == maybe_c {
                let col = self.col;
                self.col += 2;
                return Token {
                    pos,
                    col,
                    what: maybe_t,
                    end: pos + 2,
                    line: self.line,
                };
            } else {
                self.next = Some((p, c));
            }
        }
        self.single(what, pos)
    }

    /// `time_token` attempts to return the token representation of a PDDL time
    /// construct (i.e. "#t").
    fn time_token(&mut self, pos: usize) -> Token {
        if let Some((_, c)) = self.chars.next() {
            if c == 't' {
                let col = self.col;
                self.col += 2;
                return Token {
                    pos,
                    col,
                    what: TokenType::Time,
                    end: pos + 2,
                    line: self.line,
                };
            }
        }
        self.col += 1;
        return Token {
            pos,
            what: TokenType::Invalid,
            end: pos + 1,
            col: self.col - 1,
            line: self.line,
        };
    }

    /// `digits` continues scanning until no more digit characters
    /// are encountered.  Returns the position one past the last scanned
    /// digit.
    fn digits(&mut self, start: usize) -> usize {
        let mut end = start;
        loop {
            let next = self.chars.next();

            if let Some((_, c)) = next {
                if !c.is_ascii_digit() {
                    self.next = next;
                    return end;
                }
                self.col += 1;
            } else {
                return end;
            }
            end += 1;
        }
    }

    /// `number` attempts to return the token representation of a PDDL number.
    fn number(&mut self, start: usize) -> Token {
        let col = self.col;
        self.col += 1;

        // This function, number, assumes the first digit has already
        // been scanned so now we look for remaining digits if they exist.
        let mut end = self.digits(start + 1);

        if let Some((dot_start, '.')) = self.next {
            let dot_col = self.col;

            self.next = None;
            self.col += 1;

            let num_start = dot_start + 1;
            let num_end = self.digits(num_start);

            if num_start != num_end {
                end = num_end;
            } else {
                // There were no more scanned digits.
                self.pending = Some(Token {
                    what: TokenType::Invalid,
                    pos: dot_start,
                    end: dot_start + 1,
                    col: dot_col,
                    line: self.line,
                });
            }
        }
        Token {
            what: TokenType::Number,
            pos: start,
            line: self.line,
            end,
            col,
        }
    }

    /// `keyword` returns the next token that resembels a valid keyword.
    fn keyword(&mut self, start: usize) -> Token {
        let mut tok = self.special(start, TokenType::Strips);
        if tok.what == TokenType::Strips {
            let kw = &self.src[tok.pos..tok.end];
            if let Some(tt) = self.keywords.get(kw) {
                tok.what = *tt
            } else {
                tok.what = TokenType::Invalid
            }
        }
        tok
    }
}

impl Iterator for Scanner<'_> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        // Previous calls to next can produce upto two tokens where
        // the second is stored in pending.
        if let Some(t) = self.pending {
            self.pending = None;
            return Some(t);
        }

        loop {
            let mut next = self.next;
            self.next = None;
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
                    return Some(self.single(TokenType::LParen, pos));
                } else if ch == ')' {
                    return Some(self.single(TokenType::RParen, pos));
                } else if ch == ';' {
                    self.comment();
                } else if ch.is_ascii_alphabetic() {
                    return Some(self.ident(pos, ch));
                } else if ch == '?' {
                    return Some(self.special(pos, TokenType::Variable));
                } else if ch == ':' {
                    return Some(self.keyword(pos));
                } else if ch == '*' {
                    return Some(self.single(TokenType::Mult, pos));
                } else if ch == '/' {
                    return Some(self.single(TokenType::Div, pos));
                } else if ch == '+' {
                    return Some(self.single(TokenType::Plus, pos));
                } else if ch == '-' {
                    return Some(self.single(TokenType::Minus, pos));
                } else if ch == '=' {
                    return Some(self.single(TokenType::Equal, pos));
                } else if ch == '<' {
                    return Some(self.maybe(TokenType::Less, pos, '=', TokenType::LessEq));
                } else if ch == '>' {
                    return Some(self.maybe(TokenType::Greater, pos, '=', TokenType::GreaterEq));
                } else if ch == '#' {
                    return Some(self.time_token(pos));
                } else if ch.is_ascii_digit() {
                    return Some(self.number(pos));
                } else {
                    return Some(self.single(TokenType::Invalid, pos));
                }
            } else {
                return None;
            }
        }
    }
}

/// Token is primary object that is returned from calling `Scanner::scan`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Token {
    /// What type of token this one is.
    pub what: TokenType,
    /// Position of where the token was found from scanner's source contents.
    pub pos: usize,
    /// Position that is one past the last character of the scanned token.  If
    /// the token is one character in length then `end = pos + 1`.
    pub end: usize,
    /// Column number of where the token was found.
    pub col: usize,
    /// Line number of where the token was found.
    pub line: usize,
}

impl<'a> Token {
    /// `to_str` returns the string representation of the scanned
    /// TokenType.  `src` should be the exact source contents that was
    /// passed to the `Scanner::scan`.
    pub fn to_str(self, src: &'a str) -> &'a str {
        match self.what {
            TokenType::Invalid | TokenType::Ident | TokenType::Variable | TokenType::Number => {
                &src[self.pos..self.end]
            }
            _ => self.what.as_str(),
        }
    }
}

/// TokenType specifies what kind of token was scanned.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TokenType {
    Invalid,
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
    Ident,
    Variable,
    Number,
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
    Types,
    Constants,
    Predicates,
    Functions,
    Action,
    DurativeAction,
    Parameters,
    Precondition,
    Effect,
    Condition,
    Duration,
    Derived,
    Domain,
    Objects,
    Init,
    Goal,
    Metric,
}

impl TokenType {
    pub fn as_str(self) -> &'static str {
        match self {
            TokenType::Invalid => "invalid",
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
            TokenType::Ident => "identifier",
            TokenType::Variable => "variable",
            TokenType::Number => "number",
            TokenType::Strips => ":strips",
            TokenType::Typing => ":typing",
            TokenType::Equality => ":equality",
            TokenType::NegativePreconditions => ":negative-preconditions",
            TokenType::DisjunctivePreconditions => ":disjunctive-preconditions",
            TokenType::ExistentialPreconditions => ":existential-preconditions",
            TokenType::UniversalPreconditions => ":universal-preconditions",
            TokenType::QuantifiedPreconditions => ":quantified-preconditions",
            TokenType::ConditionalEffects => ":conditional-effects",
            TokenType::Fluents => ":fluents",
            TokenType::NumericFluents => ":numeric-fluents",
            TokenType::ObjectFluents => ":object-fluents",
            TokenType::Adl => ":adl",
            TokenType::DurativeActions => ":durative-actions",
            TokenType::DurationInequalities => ":duration-inequalities",
            TokenType::ContinuousEffects => ":continuous-effects",
            TokenType::DerivedPredicates => ":derived-predicates",
            TokenType::TimedInitialLiterals => ":timed-initial-literals",
            TokenType::Preferences => ":preferences",
            TokenType::Constraints => ":constraints",
            TokenType::ActionCosts => ":action-costs",
            TokenType::Types => ":types",
            TokenType::Constants => ":constants",
            TokenType::Predicates => ":predicates",
            TokenType::Functions => ":functions",
            TokenType::Action => ":action",
            TokenType::DurativeAction => ":durative-action",
            TokenType::Precondition => ":precondition",
            TokenType::Effect => ":effect",
            TokenType::Parameters => ":parameters",
            TokenType::Condition => ":condition",
            TokenType::Duration => ":duration",
            TokenType::Derived => ":derived",
            TokenType::Domain => ":domain",
            TokenType::Objects => ":objects",
            TokenType::Init => ":init",
            TokenType::Goal => ":goal",
            TokenType::Metric => ":metric",
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn basic_scan() {
        const TEST_STRING: &'static str = "
;; a comment
 (
   (foo ;; another comment ₳
    a42bar- )
    q_ux-baz)
 )
bar";

        let tokens = scan(TEST_STRING);

        assert_eq!(tokens.len(), 9);

        let t = &tokens[0];
        assert_eq!(t.what, TokenType::LParen);
        assert_eq!(t.pos, 15, "invalid position");
        assert_eq!(t.end, 16, "invalid end position");
        assert_eq!(t.col, 2, "invalid column");
        assert_eq!(t.line, 3, "invalid line");

        let t = &tokens[1];
        assert_eq!(t.what, TokenType::LParen);
        assert_eq!(t.pos, 20, "invalid position");
        assert_eq!(t.end, 21, "invalid end position");
        assert_eq!(t.col, 4, "invalid column");
        assert_eq!(t.line, 4, "invalid line");

        let t = &tokens[2];
        assert_eq!(t.what, TokenType::Ident);
        assert_eq!(t.pos, 21, "invalid position");
        assert_eq!(t.end, 24, "invalid end position");
        assert_eq!(t.col, 5, "invalid column");
        assert_eq!(t.line, 4, "invalid line");
        assert_eq!(&TEST_STRING[21..24], "foo");

        let t = &tokens[3];
        assert_eq!(t.what, TokenType::Ident);
        assert_eq!(t.pos, 52, "invalid position");
        assert_eq!(t.end, 59, "invalid end position");
        assert_eq!(t.col, 5, "invalid column");
        assert_eq!(t.line, 5, "invalid line");
        assert_eq!(&TEST_STRING[52..59], "a42bar-");

        let t = &tokens[4];
        assert_eq!(t.what, TokenType::RParen);
        assert_eq!(t.pos, 60, "invalid position");
        assert_eq!(t.end, 61, "invalid end position");
        assert_eq!(t.col, 13, "invalid column");
        assert_eq!(t.line, 5, "invalid line");

        let t = &tokens[5];
        assert_eq!(t.what, TokenType::Ident);
        assert_eq!(t.pos, 66, "invalid position");
        assert_eq!(t.end, 74, "invalid end position");
        assert_eq!(t.col, 5, "invalid column");
        assert_eq!(t.line, 6, "invalid line");
        assert_eq!(&TEST_STRING[66..74], "q_ux-baz");

        let t = &tokens[6];
        assert_eq!(t.what, TokenType::RParen);
        assert_eq!(t.pos, 74, "invalid position");
        assert_eq!(t.end, 75, "invalid end position");
        assert_eq!(t.col, 13, "invalid column");
        assert_eq!(t.line, 6, "invalid line");

        let t = &tokens[7];
        assert_eq!(t.what, TokenType::RParen);
        assert_eq!(t.pos, 77, "invalid position");
        assert_eq!(t.end, 78, "invalid end position");
        assert_eq!(t.col, 2, "invalid column");
        assert_eq!(t.line, 7, "invalid line");

        let t = &tokens[8];
        assert_eq!(t.what, TokenType::Ident);
        assert_eq!(t.pos, 79, "invalid position");
        assert_eq!(t.end, 82, "invalid end position");
        assert_eq!(t.col, 1, "invalid column");
        assert_eq!(t.line, 8, "invalid line");
        assert_eq!(&TEST_STRING[79..82], "bar");
    }

    #[test]
    fn variables() {
        const TEST_STRING: &'static str = " )  ?foo  ?bar";

        let tokens = scan(TEST_STRING);

        assert_eq!(tokens.len(), 3);

        let t = &tokens[0];
        assert_eq!(t.what, TokenType::RParen);
        assert_eq!(t.pos, 1, "invalid position");
        assert_eq!(t.end, 2, "invalid position");
        assert_eq!(t.col, 2, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = &tokens[1];
        assert_eq!(t.what, TokenType::Variable);
        assert_eq!(t.pos, 4, "invalid position");
        assert_eq!(t.end, 8, "invalid end position");
        assert_eq!(t.col, 5, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(t.to_str(TEST_STRING), "?foo");

        let t = &tokens[2];
        assert_eq!(t.what, TokenType::Variable);
        assert_eq!(t.pos, 10, "invalid position");
        assert_eq!(t.end, 14, "invalid end position");
        assert_eq!(t.col, 11, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(t.to_str(TEST_STRING), "?bar");
    }

    #[test]
    fn operators() {
        let tokens = scan("+ - * /");

        assert_eq!(tokens.len(), 4);

        let t = &tokens[0];
        assert_eq!(t.what, TokenType::Plus);
        assert_eq!(t.pos, 0, "invalid position");
        assert_eq!(t.end, 1, "invalid end position");
        assert_eq!(t.col, 1, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = &tokens[1];
        assert_eq!(t.what, TokenType::Minus);
        assert_eq!(t.pos, 2, "invalid position");
        assert_eq!(t.end, 3, "invalid end position");
        assert_eq!(t.col, 3, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = &tokens[2];
        assert_eq!(t.what, TokenType::Mult);
        assert_eq!(t.pos, 4, "invalid position");
        assert_eq!(t.end, 5, "invalid end position");
        assert_eq!(t.col, 5, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = &tokens[3];
        assert_eq!(t.what, TokenType::Div);
        assert_eq!(t.pos, 6, "invalid position");
        assert_eq!(t.end, 7, "invalid end position");
        assert_eq!(t.col, 7, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = &tokens[3];
        assert_eq!(t.what, TokenType::Div);
        assert_eq!(t.pos, 6, "invalid position");
        assert_eq!(t.end, 7, "invalid end position");
        assert_eq!(t.col, 7, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
    }

    #[test]
    fn comparisons() {
        const TEST_STRING: &'static str = "< <= > >= =";

        let tokens = scan(TEST_STRING);

        assert_eq!(tokens.len(), 5);

        let t = &tokens[0];
        assert_eq!(t.what, TokenType::Less);
        assert_eq!(t.pos, 0, "invalid position");
        assert_eq!(t.end, 1, "invalid end position");
        assert_eq!(t.col, 1, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = &tokens[1];
        assert_eq!(t.what, TokenType::LessEq);
        assert_eq!(t.pos, 2, "invalid position");
        assert_eq!(t.end, 4, "invalid end position");
        assert_eq!(t.col, 3, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(t.to_str(TEST_STRING), "<=");

        let t = &tokens[2];
        assert_eq!(t.what, TokenType::Greater);
        assert_eq!(t.pos, 5, "invalid position");
        assert_eq!(t.end, 6, "invalid end position");
        assert_eq!(t.col, 6, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = &tokens[3];
        assert_eq!(t.what, TokenType::GreaterEq);
        assert_eq!(t.pos, 7, "invalid position");
        assert_eq!(t.end, 9, "invalid end position");
        assert_eq!(t.col, 8, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(t.to_str(TEST_STRING), ">=");

        let t = &tokens[4];
        assert_eq!(t.what, TokenType::Equal);
        assert_eq!(t.pos, 10, "invalid position");
        assert_eq!(t.end, 11, "invalid end position");
        assert_eq!(t.col, 11, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
    }

    #[test]
    fn time() {
        const TEST_STRING: &'static str = "(#t)";

        let tokens = scan(TEST_STRING);

        assert_eq!(tokens.len(), 3);

        let t = &tokens[0];
        assert_eq!(t.what, TokenType::LParen);
        assert_eq!(t.pos, 0, "invalid position");
        assert_eq!(t.end, 1, "invalid end position");
        assert_eq!(t.col, 1, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = &tokens[1];
        assert_eq!(t.what, TokenType::Time);
        assert_eq!(t.pos, 1, "invalid position");
        assert_eq!(t.end, 3, "invalid end position");
        assert_eq!(t.col, 2, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = &tokens[2];
        assert_eq!(t.what, TokenType::RParen);
        assert_eq!(t.pos, 3, "invalid position");
        assert_eq!(t.end, 4, "invalid end position");
        assert_eq!(t.col, 4, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
    }

    #[test]
    fn numbers() {
        const TEST_STRING: &'static str = "42 13.25foo 0012";

        let tokens = scan(TEST_STRING);

        assert_eq!(tokens.len(), 4);

        let t = &tokens[0];
        assert_eq!(t.what, TokenType::Number);
        assert_eq!(t.pos, 0, "invalid position");
        assert_eq!(t.end, 2, "invalid end position");
        assert_eq!(t.col, 1, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(t.to_str(TEST_STRING), "42");

        let t = &tokens[1];
        assert_eq!(t.what, TokenType::Number);
        assert_eq!(t.pos, 3, "invalid position");
        assert_eq!(t.end, 8, "invalid end position");
        assert_eq!(t.col, 4, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(t.to_str(TEST_STRING), "13.25");

        let t = &tokens[2];
        assert_eq!(t.what, TokenType::Ident);
        assert_eq!(t.pos, 8, "invalid position");
        assert_eq!(t.end, 11, "invalid end position");
        assert_eq!(t.col, 9, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(t.to_str(TEST_STRING), "foo");

        let t = &tokens[3];
        assert_eq!(t.what, TokenType::Number);
        assert_eq!(t.pos, 12, "invalid position");
        assert_eq!(t.end, 16, "invalid end position");
        assert_eq!(t.col, 13, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(t.to_str(TEST_STRING), "0012");
    }

    #[test]
    fn invalid_number() {
        const TEST_STRING: &'static str = "13.foo";

        let tokens = scan(TEST_STRING);

        assert_eq!(tokens.len(), 3);

        let t = &tokens[0];
        assert_eq!(t.what, TokenType::Number);
        assert_eq!(t.pos, 0, "invalid position");
        assert_eq!(t.end, 2, "invalid end position");
        assert_eq!(t.col, 1, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(t.to_str(TEST_STRING), "13");

        let t = &tokens[1];
        assert_eq!(t.what, TokenType::Invalid);
        assert_eq!(t.pos, 2, "invalid position");
        assert_eq!(t.end, 3, "invalid end position");
        assert_eq!(t.col, 3, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(t.to_str(TEST_STRING), ".");

        let t = &tokens[2];
        assert_eq!(t.what, TokenType::Ident);
        assert_eq!(t.pos, 3, "invalid position");
        assert_eq!(t.end, 6, "invalid end position");
        assert_eq!(t.col, 4, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(t.to_str(TEST_STRING), "foo");
    }

    #[test]
    fn keywords() {
        const TEST_STRING: &'static str = " (  :typing  :action :durative-action";

        let tokens = scan(TEST_STRING);

        assert_eq!(tokens.len(), 4);

        let t = &tokens[0];
        assert_eq!(t.what, TokenType::LParen);
        assert_eq!(t.pos, 1, "invalid position");
        assert_eq!(t.end, 2, "invalid end position");
        assert_eq!(t.col, 2, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = &tokens[1];
        assert_eq!(t.what, TokenType::Typing);
        assert_eq!(t.pos, 4, "invalid position");
        assert_eq!(t.end, 11, "invalid end position");
        assert_eq!(t.col, 5, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(t.to_str(TEST_STRING), ":typing");

        let t = &tokens[2];
        assert_eq!(t.what, TokenType::Action);
        assert_eq!(t.pos, 13, "invalid position");
        assert_eq!(t.end, 20, "invalid end position");
        assert_eq!(t.col, 14, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(t.to_str(TEST_STRING), ":action");

        let t = &tokens[3];
        assert_eq!(t.what, TokenType::DurativeAction);
        assert_eq!(t.pos, 21, "invalid position");
        assert_eq!(t.end, 37, "invalid end position");
        assert_eq!(t.col, 22, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(t.to_str(TEST_STRING), ":durative-action");
    }

    #[test]
    fn invalid_keywords() {
        const TEST_STRING: &'static str = ":strips:typin:action :";

        let tokens = scan(TEST_STRING);

        assert_eq!(tokens.len(), 4);

        let t = &tokens[0];
        assert_eq!(t.what, TokenType::Strips);
        assert_eq!(t.pos, 0, "invalid position");
        assert_eq!(t.end, 7, "invalid end position");
        assert_eq!(t.col, 1, "invalid column");
        assert_eq!(t.line, 1, "invalid line");

        let t = &tokens[1];
        assert_eq!(t.what, TokenType::Invalid);
        assert_eq!(t.pos, 7, "invalid position");
        assert_eq!(t.end, 13, "invalid end position");
        assert_eq!(t.col, 8, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(t.to_str(TEST_STRING), ":typin");

        let t = &tokens[2];
        assert_eq!(t.what, TokenType::Action);
        assert_eq!(t.pos, 13, "invalid position");
        assert_eq!(t.end, 20, "invalid end position");
        assert_eq!(t.col, 14, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(t.to_str(TEST_STRING), ":action");

        let t = &tokens[3];
        assert_eq!(t.what, TokenType::Invalid);
        assert_eq!(t.pos, 21, "invalid position");
        assert_eq!(t.end, 22, "invalid end position");
        assert_eq!(t.col, 22, "invalid column");
        assert_eq!(t.line, 1, "invalid line");
        assert_eq!(t.to_str(TEST_STRING), ":");
    }
}
