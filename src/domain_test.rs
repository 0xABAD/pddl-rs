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
                    ":typing",
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
            },
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
            },
            _ => panic!("Invalid ParseErrorType -- have {:?}, want Expect", pe.what),
        }
    } else {
        panic!("Expected error but received successful domain parse");
    }
}
