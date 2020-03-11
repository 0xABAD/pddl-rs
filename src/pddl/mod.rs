pub mod scanner;
pub mod types;

mod parser;
mod reqs;
#[cfg(test)]
mod test;

use self::{
    parser::{Parse, Parser},
    reqs::Reqs,
    scanner::{Scanner, Token, TokenType},
    types::{Types, TypeId},
};

pub use self::{
    parser::{Error, ErrorType},
    reqs::Requirement,
};

pub type Errors = Vec<Error>;

/// `Domain` represents the final output from parsing the contents
/// representing some PDDL domain.
pub struct Domain {
    /// The parsed domain name.
    pub name: String,

    types: Types, // Parsed (:types).
    reqs: Reqs,   // Parsed (:requirements).

                  // predicates: Vec<Predicate>, // Parsed (:predicates) ordered by PredId.
                  // functions: Vec<Function>,   // Parsed (:functions) ordered by FuncId.
                  // constants: Vec<Constant>,   // Parsed (:constants) ordered by ConstId.
                  // actions: Vec<Action>,       // Parsed (:action ...) definitions.
}

impl Domain {
    /// `is_domain` return true if `contents` represents a PDDL domain.
    /// Only the first few tokens of `cotents` is paresed to make this
    /// determination.
    pub fn is_domain(src: &str) -> bool {
        let mut lex = Scanner::new(src);

        let is_ident = |t: &Token, ident| {
            t.what == TokenType::Ident && t.to_str(src).eq_ignore_ascii_case(ident)
        };

        lex.next()
            .filter(|t| t.what == TokenType::LParen)
            .and_then(|_| lex.next())
            .filter(|t| is_ident(t, "define"))
            .and_then(|_| lex.next())
            .filter(|t| t.what == TokenType::LParen)
            .and_then(|_| lex.next())
            .filter(|t| is_ident(t, "domain"))
            .is_some()
    }

    /// `parse` returns a complete domain represented by the PDDL domain
    /// within `src.`  Returns one or many `Error`s if any syntax or semantic
    /// error are encountered.
    pub fn parse(src: &str) -> Result<Self, Errors> {
        let tokens = scanner::scan(src);
        let mut top = Parser::new(src, &tokens);

        let result: Parse;
        match top.domain_top() {
            Ok(pr) => result = pr,
            Err(e) => return Err(vec![e]),
        }

        let dom = Domain {
            name: result.name.to_string(),
            reqs: result.reqs,
            types: result.types,
        };

        Ok(dom)
    }

    /// `has_requirement` returns true if this `Domain` has the requirement of `r`.
    pub fn has_requirement(&self, r: Requirement) -> bool {
        self.reqs.has(r)
    }

    /// `type_id` returns the TypeId associated with `name`, is it exists.
    pub fn type_id(&self, name: &str) -> Option<TypeId> {
        self.types.get(name)
    }

    /// `is_child_type_an_ancestor_of` returns true if `child` is an ancestor of `parent`.
    pub fn is_child_type_an_ancestor_of(&self, child: TypeId, parent: TypeId) -> bool {
        self.types.is_child_an_ancestor_of(child, parent)
    }
}
