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
                    ":types",
                    ":requirements",
                ]
            ),
            _ => panic!("Invalid ParseErrorType -- have {:?}, want Expect", pe.what),
        }
    } else {
        panic!("Expected error but received successful domain parse");
    }
}

#[test]
fn can_parse_requirements() -> Result<(), ParseError<'static>> {
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
fn no_requirements_implies_strips() -> Result<(), ParseError<'static>> {
    let d = Domain::parse("(define (domain foo))")?;
    assert!(d.has_requirement(Requirement::Strips));
    Ok(())
}

#[test]
fn parse_requirements_allows_duplicates() -> Result<(), ParseError<'static>> {
    let d = Domain::parse("(define (domain foo) (:requirements :strips :typing :strips :typing))")?;
    assert!(d.has_requirement(Requirement::Strips));
    assert!(d.has_requirement(Requirement::Typing));
    Ok(())
}

#[test]
fn quantified_preconditions_implies_others() -> Result<(), ParseError<'static>> {
    let d = Domain::parse("(define (domain foo) (:requirements :quantified-preconditions))")?;
    assert!(d.has_requirement(Requirement::QuantifiedPreconditions));
    assert!(d.has_requirement(Requirement::ExistentialPreconditions));
    assert!(d.has_requirement(Requirement::UniversalPreconditions));
    Ok(())
}

#[test]
fn fluents_implies_others() -> Result<(), ParseError<'static>> {
    let d = Domain::parse("(define (domain foo) (:requirements :fluents))")?;
    assert!(d.has_requirement(Requirement::Fluents));
    assert!(d.has_requirement(Requirement::NumericFluents));
    assert!(d.has_requirement(Requirement::ObjectFluents));
    Ok(())
}

#[test]
fn adl_implies_others() -> Result<(), ParseError<'static>> {
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
fn timed_initial_literals_implies_others() -> Result<(), ParseError<'static>> {
    let d = Domain::parse("(define (domain foo) (:requirements :timed-initial-literals))")?;
    assert!(d.has_requirement(Requirement::TimedInitialLiterals));
    assert!(d.has_requirement(Requirement::DurativeActions));
    Ok(())
}

#[test]
fn parse_requirements_fails_with_invalid_requirement() {
    const DOMAIN: &'static str = "(define (domain foo) (:requirements :strips :strip :typing))";

    if let Err(pe) = Domain::parse(DOMAIN) {
        match pe.what {
            ParseErrorType::Expect(et) => {
                let mut v = REQUIREMENTS.to_vec();
                v.push(")");
                assert_eq!(et.expect, v)
            }
            _ => panic!("Invalid ParseErrorType -- have {:?}, want Expect", pe.what),
        }
    } else {
        panic!("Expected error but received successful domain parse");
    }
}

#[test]
fn parse_requirements_fails_with_invalid_token() {
    const DOMAIN: &'static str = "(define (domain foo) (:requirements :strips $))";

    if let Err(pe) = Domain::parse(DOMAIN) {
        match pe.what {
            ParseErrorType::Expect(et) => {
                let mut v = REQUIREMENTS.to_vec();
                v.push(")");
                assert_eq!(et.expect, v)
            }
            _ => panic!("Invalid ParseErrorType -- have {:?}, want Expect", pe.what),
        }
    } else {
        panic!("Expected error but received successful domain parse");
    }
}

#[test]
fn can_parse_types() -> Result<(), ParseError<'static>> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types car truck motorcycle - vehicle
                   bicycle - object
                   moped - (either motorcycle bicycle)))",
    )?;

    assert_eq!(d.id_for_type("object"), Some(&0));
    assert_eq!(d.id_for_type("car"), Some(&1));
    assert_eq!(d.id_for_type("truck"), Some(&2));
    assert_eq!(d.id_for_type("motorcycle"), Some(&3));
    assert_eq!(d.id_for_type("vehicle"), Some(&4));
    assert_eq!(d.id_for_type("bicycle"), Some(&5));
    assert_eq!(d.id_for_type("moped"), Some(&6));

    let veh: HashSet<_> = [4].iter().cloned().collect();
    assert!(d.parent_type_ids(1).is_subset(&veh));
    assert!(d.parent_type_ids(1).is_superset(&veh));

    assert!(d.parent_type_ids(2).is_subset(&veh));
    assert!(d.parent_type_ids(2).is_superset(&veh));

    assert!(d.parent_type_ids(3).is_subset(&veh));
    assert!(d.parent_type_ids(3).is_superset(&veh));

    assert!(d.parent_type_ids(4).is_empty());

    let obj: HashSet<_> = [0].iter().cloned().collect();
    assert!(d.parent_type_ids(5).is_subset(&obj));
    assert!(d.parent_type_ids(5).is_superset(&obj));

    let many: HashSet<_> = [3, 5].iter().cloned().collect();
    assert!(d.parent_type_ids(6).is_subset(&many));
    assert!(d.parent_type_ids(6).is_superset(&many));

    Ok(())
}

#[test]
fn has_default_object() -> Result<(), ParseError<'static>> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types))",
    )?;
    assert_eq!(d.id_for_type("object"), Some(&0));
    Ok(())
}

#[test]
fn object_can_not_be_a_new_type() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types object))",
    );
    if let Ok(_) = d {
        panic!("Received successful parse when error should have occurred.");
    }
}

#[test]
fn object_can_not_be_a_new_type_2() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types car object))",
    );
    if let Ok(_) = d {
        panic!("Received successful parse when error should have occurred.");
    }
}

#[test]
fn circular_inheritance_causes_error() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types shape - object
                   square - (either rectangle shape)
                   rectangle - square))",
    );
    // Circular inheritance from single parent.
    if let Ok(_) = d {
        panic!("Received successful parse when error should have occurred.");
    }
}

#[test]
fn circular_inheritance_causes_error_2() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types shape - rectangle
                   square - shape
                   rectangle - (either square box)))",
    );
    // Circular inheritance from either type.
    if let Ok(_) = d {
        panic!("Received successful parse when error should have occurred.");
    }
}

#[test]
fn circular_inheritance_causes_error_3() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types shape - rectangle
                   square - shape
                   rectangle - (either box square)))",
    );
    // Circular inheritance from either type.
    if let Ok(_) = d {
        panic!("Received successful parse when error should have occurred.");
    }
}

#[test]
fn correct_constants_from_top_level() -> Result<(), ParseError<'static>> {
    let mut dp = DomainParser::new(
        "(define (domain foo)
(:requirements :strips :typing)
(:types item)
(:constants foo bar - item))",
    );
    let pr = dp.top_level()?;
    assert_eq!(pr.constants.line, 4);
    assert_eq!(pr.constants.col, 13);
    assert_eq!(pr.constants.pos, 79);
    Ok(())
}

#[test]
fn unbalanced_parens_in_constants() {
    let mut dp = DomainParser::new(
        "(define (domain foo)
(:requirements :strips :typing)
(:types item)
(:constants foo bar - item",
    );
    let pr = dp.top_level();
    if let Err(pe) = pr {
        match pe.what {
            ParseErrorType::Expect(_) => return,
            _ => panic!("Invalid ParseErrorType -- have {:?}, want Expect", pe.what),
        }
    } else {
        panic!("Received successful parse when error should have occurred.");
    }
}
