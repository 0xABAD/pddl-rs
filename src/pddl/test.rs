use super::*;

#[test]
fn check_if_domain() {
    assert!(Domain::is_domain("(define (domain foo))"));
}

#[test]
fn check_if_not_domain() {
    assert!(!Domain::is_domain("(define (problem foo-p1))"));
}

#[test]
fn parse_domain_name() -> Result<(), Errors> {
    let dom = Domain::parse("(define (domain foo))")?;
    assert_eq!(dom.name, "foo");
    Ok(())
}

#[test]
fn unexpected_end_of_input() {
    if let Err(e) = Domain::parse("(define (domain foo)") {
        let pe = &e[0];
        match &pe.what {
            ErrorType::Expect { have, expect } => {
                assert_eq!(have, "end of input");
                assert_eq!(*expect, vec!["(", ")"]);
            }
            _ => panic!("Invalid ErrorType -- have {:?}, want Expect", pe.what),
        }
    } else {
        panic!("Expected error but received successful domain parse");
    }
}

#[test]
fn detects_extra_input() {
    // Text contains an extra right paren.
    if let Err(e) = Domain::parse("(define (domain foo)))") {
        let pe = &e[0];
        match &pe.what {
            ErrorType::ExtraInput(s) => assert_eq!(*s, ")"),
            _ => panic!("Invalid ErrorType -- have {:?}, want Expect", pe.what),
        }
    } else {
        panic!("Expected error but received successful domain parse");
    }
}

#[test]
fn detects_invalid_token() {
    if let Err(e) = Domain::parse("(define (domain foo) %)") {
        let pe = &e[0];
        match &pe.what {
            ErrorType::Expect { have: _, expect } => assert_eq!(*expect, vec!["(", ")"]),
            _ => panic!(
                "Invalid ErrorType -- have {:?}, want Expect('(', ')')",
                pe.what
            ),
        }
    } else {
        panic!("Expected error but received successful domain parse");
    }
}

#[test]
fn detects_invalid_top_level_keyword() {
    if let Err(e) = Domain::parse("(define (domain foo) (:foo))") {
        let pe = &e[0];
        match &pe.what {
            ErrorType::Expect { have: _, expect } => assert_eq!(
                *expect,
                vec![
                    ":derived",
                    ":durative-action",
                    ":action",
                    ":constraints",
                    ":functions",
                    ":predicates",
                    ":constants",
                    ":types",
                    ":requirements",
                ]
            ),
            _ => panic!("Invalid ErrorType -- have {:?}, want Expect", pe.what),
        }
    } else {
        panic!("Expected error but received successful domain parse");
    }
}

#[test]
fn can_parse_requirements() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips
                          :typing
                          :equality
                          :negative-preconditions
                          :disjunctive-preconditions
                          :existential-preconditions
                          :universal-preconditions
                          :quantified-preconditions
                          :conditional-effects
                          :fluents
                          :numeric-fluents
                          :object-fluents
                          :adl
                          :durative-actions
                          :duration-inequalities
                          :continuous-effects
                          :derived-predicates
                          :timed-initial-literals
                          :preferences
                          :constraints
                          :action-costs
           ))",
    )?;
    assert!(d.has_requirement(Requirement::Strips));
    assert!(d.has_requirement(Requirement::Typing));
    assert!(d.has_requirement(Requirement::Equality));
    assert!(d.has_requirement(Requirement::NegativePreconditions));
    assert!(d.has_requirement(Requirement::DisjunctivePreconditions));
    assert!(d.has_requirement(Requirement::ExistentialPreconditions));
    assert!(d.has_requirement(Requirement::UniversalPreconditions));
    assert!(d.has_requirement(Requirement::QuantifiedPreconditions));
    assert!(d.has_requirement(Requirement::ConditionalEffects));
    assert!(d.has_requirement(Requirement::Fluents));
    assert!(d.has_requirement(Requirement::NumericFluents));
    assert!(d.has_requirement(Requirement::ObjectFluents));
    assert!(d.has_requirement(Requirement::Adl));
    assert!(d.has_requirement(Requirement::DurativeActions));
    assert!(d.has_requirement(Requirement::DurationInequalities));
    assert!(d.has_requirement(Requirement::ContinuousEffects));
    assert!(d.has_requirement(Requirement::DerivedPredicates));
    assert!(d.has_requirement(Requirement::TimedInitialLiterals));
    assert!(d.has_requirement(Requirement::Preferences));
    assert!(d.has_requirement(Requirement::Constraints));
    assert!(d.has_requirement(Requirement::ActionCosts));
    Ok(())
}

#[test]
fn no_requirements_implies_strips() -> Result<(), Errors> {
    let d = Domain::parse("(define (domain foo))")?;
    assert!(d.has_requirement(Requirement::Strips));
    Ok(())
}

#[test]
fn parse_requirements_allows_duplicates() -> Result<(), Errors> {
    let d = Domain::parse("(define (domain foo) (:requirements :strips :typing :strips :typing))")?;
    assert!(d.has_requirement(Requirement::Strips));
    assert!(d.has_requirement(Requirement::Typing));
    assert!(!d.has_requirement(Requirement::Equality));
    Ok(())
}

#[test]
fn quantified_preconditions_implies_others() -> Result<(), Errors> {
    let d = Domain::parse("(define (domain foo) (:requirements :quantified-preconditions))")?;
    assert!(d.has_requirement(Requirement::QuantifiedPreconditions));
    assert!(d.has_requirement(Requirement::ExistentialPreconditions));
    assert!(d.has_requirement(Requirement::UniversalPreconditions));
    Ok(())
}

#[test]
fn fluents_implies_others() -> Result<(), Errors> {
    let d = Domain::parse("(define (domain foo) (:requirements :fluents))")?;
    assert!(d.has_requirement(Requirement::Fluents));
    assert!(d.has_requirement(Requirement::NumericFluents));
    assert!(d.has_requirement(Requirement::ObjectFluents));
    Ok(())
}

#[test]
fn adl_implies_others() -> Result<(), Errors> {
    let d = Domain::parse("(define (domain foo) (:requirements :adl))")?;
    assert!(d.has_requirement(Requirement::Adl));
    assert!(d.has_requirement(Requirement::Strips));
    assert!(d.has_requirement(Requirement::Typing));
    assert!(d.has_requirement(Requirement::Equality));
    assert!(d.has_requirement(Requirement::NegativePreconditions));
    assert!(d.has_requirement(Requirement::DisjunctivePreconditions));
    assert!(d.has_requirement(Requirement::QuantifiedPreconditions));
    assert!(d.has_requirement(Requirement::ExistentialPreconditions));
    assert!(d.has_requirement(Requirement::UniversalPreconditions));
    assert!(d.has_requirement(Requirement::ConditionalEffects));
    Ok(())
}

#[test]
fn timed_initial_literals_implies_others() -> Result<(), Errors> {
    let d = Domain::parse("(define (domain foo) (:requirements :timed-initial-literals))")?;
    assert!(d.has_requirement(Requirement::TimedInitialLiterals));
    assert!(d.has_requirement(Requirement::DurativeActions));
    Ok(())
}

#[test]
fn parse_requirements_fails_with_invalid_requirement() {
    const DOMAIN: &'static str = "(define (domain foo) (:requirements :strips :strip :typing))";

    if let Err(e) = Domain::parse(DOMAIN) {
        let pe = &e[0];
        match &pe.what {
            ErrorType::Expect { have: _, expect } => {
                let v: Vec<&str> = vec![
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
                ]
                .iter()
                .map(|tt| tt.as_str())
                .collect();
                assert_eq!(*expect, v)
            }
            _ => panic!("Invalid ErrorType -- have {:?}, want Expect", pe.what),
        }
    } else {
        panic!("Expected error but received successful domain parse");
    }
}

#[test]
fn parse_requirements_fails_with_invalid_token() {
    const DOMAIN: &'static str = "(define (domain foo) (:requirements :strips $))";

    if let Err(e) = Domain::parse(DOMAIN) {
        let pe = &e[0];
        match &pe.what {
            ErrorType::Expect { have: _, expect } => {
                let v: Vec<&str> = vec![
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
                ]
                .iter()
                .map(|tt| tt.as_str())
                .collect();
                assert_eq!(*expect, v)
            }
            _ => panic!("Invalid ErrorType -- have {:?}, want Expect", pe.what),
        }
    } else {
        panic!("Expected error but received successful domain parse");
    }
}
