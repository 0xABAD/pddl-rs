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

#[test]
fn can_parse_types() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types car truck motorcycle - vehicle
                   bicycle - object
                   moped - (either motorcycle bicycle)))",
    )?;

    assert_eq!(d.type_id("object"), Some(0));
    assert_eq!(d.type_id("car"), Some(1));
    assert_eq!(d.type_id("truck"), Some(2));
    assert_eq!(d.type_id("motorcycle"), Some(3));
    assert_eq!(d.type_id("vehicle"), Some(4));
    assert_eq!(d.type_id("bicycle"), Some(5));
    assert_eq!(d.type_id("moped"), Some(6));

    let object = d.type_id("object").unwrap();
    let car = d.type_id("car").unwrap();
    let truck = d.type_id("truck").unwrap();
    let motorcycle = d.type_id("motorcycle").unwrap();
    let vehicle = d.type_id("vehicle").unwrap();
    let bicycle = d.type_id("bicycle").unwrap();
    let moped = d.type_id("moped").unwrap();

    assert!(d.is_child_type_an_ancestor_of(car, vehicle));
    assert!(d.is_child_type_an_ancestor_of(truck, vehicle));
    assert!(d.is_child_type_an_ancestor_of(motorcycle, vehicle));
    assert!(d.is_child_type_an_ancestor_of(bicycle, object));
    assert!(d.is_child_type_an_ancestor_of(moped, motorcycle));
    assert!(d.is_child_type_an_ancestor_of(moped, bicycle));
    assert!(d.is_child_type_an_ancestor_of(moped, object));
    assert!(d.is_child_type_an_ancestor_of(moped, vehicle));

    Ok(())
}

#[test]
fn has_default_object() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types))",
    )?;
    assert_eq!(d.type_id("object"), Some(0));
    Ok(())
}

#[test]
fn object_can_not_be_a_new_type() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types object))",
    );
    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(s, "object declared as a derived type");
            return;
        }
    }
    panic!("object was allowed to be a derived type");
}

#[test]
fn object_can_not_be_a_new_type_after_first_type() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types car object))",
    );
    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(s, "object declared as a derived type");
            return;
        }
    }
    panic!("object was allowed to be a derived type");
}

#[test]
fn circular_inheritance_detected_1() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types shape - object
                   square - (either rectangle shape)
                   rectangle - square))",
    );
    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(s, "rectangle has circular inherintance with square");
            return;
        }
    }
    panic!("circular inheritance was not detected");
}

#[test]
fn circular_inheritance_detected_2() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types shape - rectangle
                   square - shape
                   rectangle - (either square box)))",
    );
    // Circular inheritance from either type.
    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(s, "rectangle has circular inherintance with square");
            return;
        }
    }
    panic!("circular inheritance was not detected");
}

#[test]
fn circular_inheritance_detected_3() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types shape - rectangle
                   square - shape
                   rectangle - (either box square)))",
    );
    // Circular inheritance from either type.
    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(s, "rectangle has circular inherintance with square");
            return;
        }
    }
    panic!("circular inheritance was not detected");
}
