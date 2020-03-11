pub mod scanner;
pub mod types;

mod parser;
mod reqs;
#[cfg(test)]
mod test;

use self::{
    parser::{Parse, Parser, ParsingWhat},
    reqs::Reqs,
    scanner::{Scanner, Token, TokenType},
    types::{TypeId, Types},
};

pub use self::{
    parser::{Error, ErrorType},
    reqs::Requirement,
};

use rayon::prelude::*;

pub type Errors = Vec<Error>;

/// `Domain` represents the final output from parsing the contents
/// representing some PDDL domain.
pub struct Domain {
    /// The parsed domain name.
    pub name: String,

    types: Types, // Parsed (:types).
    reqs: Reqs,   // Parsed (:requirements).
    predicates: Vec<Predicate>, // Parsed (:predicates) ordered by PredId.
                  // functions: Vec<Function>,   // Parsed (:functions) ordered by FuncId.
                  // constants: Vec<Constant>,   // Parsed (:constants) ordered by ConstId.
                  // actions: Vec<Action>,       // Parsed (:action ...) definitions.
}

impl Default for Domain {
    fn default() -> Self {
        Domain {
            name: "".to_string(),
            reqs: Reqs::default(),
            types: Types::default(),
            predicates: vec![],
            // functions: vec![],
            // constants: vec![],
            // actions: vec![],
        }
    }
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

        let mut dom = Domain::default();
        dom.name = result.name.to_string();
        dom.reqs = result.reqs;
        dom.types = result.types;

        let mut parsers: Vec<Parser> = vec![];

        if result.pred_pos != 0 {
            let mut p = Parser::new(src, &tokens);

            p.tokpos = result.pred_pos;
            p.reqs = result.reqs;
            p.what = ParsingWhat::Predicates;
            p.types = Some(&dom.types);

            parsers.push(p);
        }

        let results: Vec<Result<Parse, Error>> = parsers
            .par_iter_mut()
            .map(|p| match p.what {
                ParsingWhat::Predicates => p.predicates(),
                // ParsingWhat::Functions => dp.functions(types),
                // ParsingWhat::Constants => dp.constants(types),
                // ParsingWhat::Action => dp.action(types),
                _ => panic!("Parsing incorrect contents: {:?}", p.what),
            })
            .collect();

        let mut errors: Vec<Error> = vec![];

        for result in results {
            let parse = match result {
                Ok(r) => r,
                Err(e) => {
                    errors.push(e);
                    Parse::default()
                }
            };
            if errors.len() > 0 {
                continue;
            }
            match parse.what {
                ParsingWhat::Predicates => dom.predicates = parse.predicates,
                // ParsingWhat::Functions => dom.functions = pr.functions,
                // ParsingWhat::Constants => dom.constants = pr.constants,
                // ParsingWhat::Action => {
                //     let mut act = pr.action.expect("did not receive a parsed :action");

                //     if act_names.contains(&act.name) {
                //         let s = format!("action, {}, is already defined", &act.name);
                //         errors.push(ParseError {
                //             what: ParseErrorType::SemanticError(s),
                //             line: act.line,
                //             col: act.col,
                //         });
                //     } else {
                //         act.id = act_id;
                //         act_id += 1;
                //         act_names.insert(act.name.clone());
                //         dom.actions.push(act);
                //     }
                // }
                _ => continue,
            }
        }

        if errors.len() > 0 {
            return Err(errors);
        }

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

pub type PredId = usize;
pub type FuncId = usize;
pub type ConstId = usize;
pub type ActionId = usize;

/// `Predicate` represents a predicate definition that is found
/// within the `:predicates` section of a PDDL domain.
#[derive(Debug)]
pub struct Predicate {
    /// A unique assigned ID for the predicate.
    pub id: PredId,
    /// Predicate's name in lowercase form.
    pub name: String,
    /// Predicate's parameters.
    pub params: Vec<Param>,
}

/// `Function` represents a predicate definition that is found
/// within the `:predicates` section of a PDDL domain.
#[derive(Debug)]
pub struct Function {
    /// A unique assigned ID for the predicate.
    pub id: FuncId,
    /// Function's name in lowercase form.
    pub name: String,
    /// The function's parameters.
    pub params: Vec<Param>,
    /// Return types of the function.
    pub return_types: Vec<TypeId>,
    /// True if the function returns a number.
    pub returns_number: bool,
}

/// `Param` is a parsed parameter that can be found within various
/// constructs of a PDDL domain (e.g. within a predicate or function
/// definition, or within an :action or :durative-action).  The
/// parameter maintains its list of immediate `TypeId`s, that the
/// parameter may be.
#[derive(Debug, PartialEq)]
pub struct Param {
    pub types: Vec<TypeId>,

    // Need to track the token positions of the parameter as
    // there is a need to check if a parameter has been previously
    // defined while also being able to shadow previously defined
    // parameters.
    start: usize, // Token start position of the param.
    end: usize,   // Token end position of the param.
}

impl Default for Param {
    fn default() -> Self {
        Param {
            types: vec![],
            start: 0,
            end: 0,
        }
    }
}

/// `Constant` is a PDDL declared constant object that is declared
/// within a domain description.
#[derive(Debug)]
pub struct Constant {
    /// A unique assigned ID for the constant.
    pub id: ConstId,
    /// Constant's name.
    pub name: String,
    /// The types that this constant derives from.
    pub types: Vec<TypeId>,
}

/// `Action` is a basic :strips PDDL action that is declared within
/// a domain description.
#[derive(Debug)]
pub struct Action {
    /// A unique assigned ID for the action.
    pub id: ActionId,
    /// Action's name in lowercase form.
    pub name: String,
    /// Parameters of the action.
    pub params: Vec<Param>,

    line: usize, // Line number where the action is defined.
    col: usize,  // Column number where the action is defined.
}

impl Action {
    pub fn new(name: &str) -> Action {
        Action {
            name: name.to_ascii_lowercase(),
            id: 0,
            params: vec![],
            line: 0,
            col: 0,
        }
    }
}
