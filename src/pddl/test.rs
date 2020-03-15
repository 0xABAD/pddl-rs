use super::*;

macro_rules! param {
    ($($arg:tt)*) => {
        {
            Param {
                types: vec![$($arg)*],
                start: 0,
                end: 0,
            }
        }
    }
}

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
                let v = &[
                    "(",
                    ":strips",
                    ":typing",
                    ":equality",
                    ":negative-preconditions",
                    ":disjunctive-preconditions",
                    ":existential-preconditions",
                    ":universal-preconditions",
                    ":quantified-preconditions",
                    ":conditional-effects",
                    ":fluents",
                    ":numeric-fluents",
                    ":object-fluents",
                    ":adl",
                    ":durative-actions",
                    ":duration-inequalities",
                    ":continuous-effects",
                    ":derived-predicates",
                    ":timed-initial-literals",
                    ":preferences",
                    ":constraints",
                    ":action-costs",
                ];
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
                let v = &[
                    "(",
                    ":strips",
                    ":typing",
                    ":equality",
                    ":negative-preconditions",
                    ":disjunctive-preconditions",
                    ":existential-preconditions",
                    ":universal-preconditions",
                    ":quantified-preconditions",
                    ":conditional-effects",
                    ":fluents",
                    ":numeric-fluents",
                    ":object-fluents",
                    ":adl",
                    ":durative-actions",
                    ":duration-inequalities",
                    ":continuous-effects",
                    ":derived-predicates",
                    ":timed-initial-literals",
                    ":preferences",
                    ":constraints",
                    ":action-costs",
                ];
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
           (:requirements :strips :typing))",
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

#[test]
fn can_parse_predicates_without_typing() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips)
           (:predicates (bar) (baz) (quux)))",
    )?;

    let bar = &d.predicates[0];
    assert_eq!(bar.id, 0);
    assert_eq!(bar.name, "bar");
    assert_eq!(bar.params, vec![]);

    let baz = &d.predicates[1];
    assert_eq!(baz.id, 1);
    assert_eq!(baz.name, "baz");
    assert_eq!(baz.params, vec![]);

    let quux = &d.predicates[2];
    assert_eq!(quux.id, 2);
    assert_eq!(quux.name, "quux");
    assert_eq!(quux.params, vec![]);

    Ok(())
}

#[test]
fn can_parse_predicates() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:predicates (bar ?a - object)
                        (baz ?a ?b - Sphere ?c -block)
                        (quux?a - square?b?c - (either Block square))))",
    )?;

    let bar = &d.predicates[0];
    assert_eq!(bar.id, 0);
    assert_eq!(bar.name, "bar");
    assert_eq!(bar.params, vec![param![0]]);

    let baz = &d.predicates[1];
    assert_eq!(baz.id, 1);
    assert_eq!(baz.name, "baz");
    assert_eq!(baz.params, vec![param![3], param![3], param![1]]);

    let quux = &d.predicates[2];
    assert_eq!(quux.id, 2);
    assert_eq!(quux.name, "quux");
    assert_eq!(quux.params, vec![param![2], param![1, 2], param![1, 2]]);

    Ok(())
}

#[test]
fn predicates_collates_either_types() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:predicates (bar ?a - object ?b - sphere)
                        (bar ?a - square ?b - square)
                        (fub ?a ?b - object ?c - sphere)
                        (bar ?a - block ?b - sphere)
                        (fub ?a - sphere ?b - block ?c - square)))",
    )?;

    let bar = &d.predicates[0];
    assert_eq!(bar.id, 0);
    assert_eq!(bar.name, "bar");
    assert_eq!(bar.params, vec![param![0, 1, 2], param![2, 3]]);

    let fub = &d.predicates[1];
    assert_eq!(fub.id, 1);
    assert_eq!(fub.name, "fub");
    assert_eq!(fub.params, vec![param![0, 3], param![0, 1], param![2, 3]]);

    Ok(())
}

#[test]
fn parse_predicates_allow_mismatching_arity() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:predicates (bar ?a - object)
                        (bar ?a - block ?b - sphere)))",
    )?;

    let bar = &d.predicates[0];
    assert_eq!(bar.id, 0);
    assert_eq!(bar.name, "bar");
    assert_eq!(bar.params, vec![param![0]]);

    let bar = &d.predicates[1];
    assert_eq!(bar.id, 1);
    assert_eq!(bar.name, "bar");
    assert_eq!(bar.params, vec![param![1], param![3]]);

    Ok(())
}

#[test]
fn parse_predicates_fails_with_duplicated_parameter() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:predicates (bar ?a - Sphere ?A)))",
    );

    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(s, "?A is a duplicated parameter");
            return;
        }
    }
    panic!("Duplicated parameter error not detected");
}

#[test]
fn parse_predicates_fails_with_type_not_defined() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:predicates (bar ?a - object)
                        (baz ?a ?b - sphere ?c - bloc)
                        (quux ?a - square ?b ?c - (either block square))))",
    );

    if let Err(e) = d {
        if let ErrorType::TypeNotDefined(t) = &e[0].what {
            assert_eq!(t, "bloc");
            return;
        }
    }
    panic!("Type defined error not returned");
}

#[test]
fn parse_predicates_fails_with_type_not_defined_2() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:predicates (bar ?a - object)
                        (baz ?a ?b - sphere ?c - block)
                        (quux ?a - square ?b ?c - (either block shape))))",
    );

    if let Err(e) = d {
        if let ErrorType::TypeNotDefined(t) = &e[0].what {
            assert_eq!(t, "shape");
            return;
        }
    }
    panic!("Type defined error not returned");
}

#[test]
fn parse_predicates_fails_when_typing_not_declared() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips)
           (:predicates (bar ?a - object)
                        (baz ?a ?b - sphere ?c - block)
                        (quux ?a - square ?b ?c - (either block square))))",
    );

    if let Err(e) = d {
        if let ErrorType::MissingRequirement { req, what: _ } = &e[0].what {
            assert_eq!(*req, Requirement::Typing);
            return;
        }
    }
    panic!("Missing :types requirement error not returned");
}

#[test]
fn can_parse_functions() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing :fluents)
           (:types block square sphere)
           (:functions (bar ?a - object)
                       (bar2 ?a - object) - number
                       (baz ?a ?b - sphere ?c -block) - (either sphere block)
                       (quux ?a - square ?b ?c - (either block square)) - object
                       (bar3)
                       (bar4)))",
    )?;

    let bar = &d.functions[0];
    assert_eq!(bar.id, 0);
    assert_eq!(bar.name, "bar");
    assert_eq!(bar.params, vec![param![0]]);
    assert_eq!(bar.return_types, vec![]);
    assert!(bar.returns_number);

    let bar2 = &d.functions[1];
    assert_eq!(bar2.id, 1);
    assert_eq!(bar2.name, "bar2");
    assert_eq!(bar2.params, vec![param![0]]);
    assert_eq!(bar2.return_types, vec![]);
    assert!(bar2.returns_number);

    let baz = &d.functions[2];
    assert_eq!(baz.id, 2);
    assert_eq!(baz.name, "baz");
    assert_eq!(baz.params, vec![param![3], param![3], param![1]]);
    assert_eq!(baz.return_types, vec![1, 3]);
    assert!(!baz.returns_number);

    let quux = &d.functions[3];
    assert_eq!(quux.id, 3);
    assert_eq!(quux.name, "quux");
    assert_eq!(quux.params, vec![param![2], param![1, 2], param![1, 2]]);
    assert_eq!(quux.return_types, vec![0]);
    assert!(!quux.returns_number);

    let bar3 = &d.functions[4];
    assert_eq!(bar3.id, 4);
    assert_eq!(bar3.name, "bar3");
    assert_eq!(bar3.params, vec![]);
    assert_eq!(bar3.return_types, vec![]);
    assert!(bar3.returns_number);

    let bar4 = &d.functions[5];
    assert_eq!(bar4.id, 5);
    assert_eq!(bar4.name, "bar4");
    assert_eq!(bar4.params, vec![]);
    assert_eq!(bar4.return_types, vec![]);
    assert!(bar4.returns_number);

    Ok(())
}

#[test]
fn parse_functions_allow_mismatching_arity() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing :fluents)
           (:types block square sphere)
           (:functions (bar ?a - object ?b - block)
                       (bar ?a - block ?b - square ?c - sphere)))",
    )?;

    let bar = &d.functions[0];
    assert_eq!(bar.id, 0);
    assert_eq!(bar.name, "bar");
    assert_eq!(bar.params, vec![param![0], param![1]]);

    let bar = &d.functions[1];
    assert_eq!(bar.id, 1);
    assert_eq!(bar.name, "bar");
    assert_eq!(bar.params, vec![param![1], param![2], param![3]]);

    Ok(())
}

#[test]
fn functions_collates_either_types() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing :fluents)
           (:types block square sphere)
           (:functions (bar ?a - object)
                       (fub ?a - object) - number
                       (baz ?a ?b - sphere ?c -block) - (either sphere block)
                       (quux ?a - square ?b ?c - (either block square)) - object
                       (quux ?a - square ?b ?c - (either block square)) - block
                       (bar ?a - (either sphere square))
                       (baz ?a ?b - sphere ?c - block)))",
    )?;

    let bar = &d.functions[0];
    assert_eq!(bar.id, 0);
    assert_eq!(bar.name, "bar");
    assert_eq!(bar.params, vec![param![0, 2, 3]]);
    assert_eq!(bar.return_types, vec![]);
    assert!(bar.returns_number);

    let fub = &d.functions[1];
    assert_eq!(fub.id, 1);
    assert_eq!(fub.name, "fub");
    assert_eq!(fub.params, vec![param![0]]);
    assert_eq!(fub.return_types, vec![]);
    assert!(fub.returns_number);

    let baz = &d.functions[2];
    assert_eq!(baz.id, 2);
    assert_eq!(baz.name, "baz");
    assert_eq!(baz.params, vec![param![3], param![3], param![1]]);
    assert_eq!(baz.return_types, vec![1, 3]);
    assert!(baz.returns_number);

    let quux = &d.functions[3];
    assert_eq!(quux.id, 3);
    assert_eq!(quux.name, "quux");
    assert_eq!(quux.params, vec![param![2], param![1, 2], param![1, 2]]);
    assert_eq!(quux.return_types, vec![0, 1]);
    assert!(!quux.returns_number);

    Ok(())
}

#[test]
fn parse_functions_fails_with_duplicated_parameter() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:functions (bar ?a - object ?A)))",
    );

    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(s, "?A is a duplicated parameter");
            return;
        }
    }
    panic!("Duplicated parameter error not detected");
}

#[test]
fn parse_functions_fails_when_typing_not_declared() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips)
           (:functions (baz ?a ?b - object)))",
    );

    if let Err(e) = d {
        if let ErrorType::MissingRequirement { req, what: _ } = e[0].what {
            assert_eq!(req, Requirement::Typing);
            return;
        }
    }
    panic!("Missing :types requirement error not returned");
}

#[test]
fn parse_functions_fails_when_typing_not_declared2() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips)
           (:functions (baz ?a ?b) - (either sphere block)))",
    );

    if let Err(e) = d {
        if let ErrorType::MissingRequirement { req, what: _ } = e[0].what {
            assert_eq!(req, Requirement::Typing);
            return;
        }
    }
    panic!("Missing :types requirement error not returned");
}

#[test]
fn parse_functions_fails_when_object_fluents_not_declared() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:functions (baz ?a ?b) - (either sphere block)))",
    );

    if let Err(e) = d {
        if let ErrorType::MissingRequirement { req, what: _ } = e[0].what {
            assert_eq!(req, Requirement::ObjectFluents);
            return;
        }
    }
    panic!("Missing :object-fluents requirement error not returned");
}

#[test]
fn parse_functions_fails_when_numeric_fluents_not_declared() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:functions (baz ?a ?b)))",
    );

    if let Err(e) = d {
        if let ErrorType::MissingRequirement { req, what: _ } = e[0].what {
            assert_eq!(req, Requirement::NumericFluents);
            return;
        }
    }
    panic!("Missing :numeric-fluents requirement error not returned");
}

#[test]
fn parse_functions_fails_when_numeric_fluents_not_declared_2() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:functions (baz ?a ?b) - number))",
    );

    if let Err(e) = d {
        if let ErrorType::MissingRequirement { req, what: _ } = e[0].what {
            assert_eq!(req, Requirement::NumericFluents);
            return;
        }
    }
    panic!("Missing :numeric-fluents requirement error not returned");
}

#[test]
fn parse_functions_fails_when_type_not_defined() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing :fluents)
           (:types block square sphere)
           (:functions (baz ?a ?b) - ball))",
    );

    if let Err(e) = d {
        if let ErrorType::TypeNotDefined(t) = &e[0].what {
            assert_eq!(*t, "ball");
            return;
        }
    }
    panic!("Type defined error not returned");
}

#[test]
fn can_parse_constants() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:constants bar fub - block
                       quux - (either object sphere)
                       baz))",
    )?;

    let bar = &d.constants[0];
    assert_eq!(bar.id, 0);
    assert_eq!(bar.name, "bar");
    assert_eq!(bar.types, vec![1]);

    let fub = &d.constants[1];
    assert_eq!(fub.id, 1);
    assert_eq!(fub.name, "fub");
    assert_eq!(fub.types, vec![1]);

    let quux = &d.constants[2];
    assert_eq!(quux.id, 2);
    assert_eq!(quux.name, "quux");
    assert_eq!(quux.types, vec![0, 3]);

    let baz = &d.constants[3];
    assert_eq!(baz.id, 3);
    assert_eq!(baz.name, "baz");
    assert_eq!(baz.types, vec![]);

    Ok(())
}

#[test]
fn allow_parsing_of_empty_constants() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:constants))",
    )?;
    assert_eq!(d.constants.len(), 0);
    Ok(())
}

#[test]
fn allow_parsing_constants_without_types() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips)
           (:constants bar baz))",
    )?;

    let bar = &d.constants[0];
    assert_eq!(bar.id, 0);
    assert_eq!(bar.name, "bar");
    assert_eq!(bar.types, vec![]);

    let baz = &d.constants[1];
    assert_eq!(baz.id, 1);
    assert_eq!(baz.name, "baz");
    assert_eq!(baz.types, vec![]);

    Ok(())
}

#[test]
fn constants_collates_either_types() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:constants bar - block
                       fub - sphere
                       bar - (either object sphere)
                       fub - square
                       bar))",
    )?;

    let bar = &d.constants[0];
    assert_eq!(bar.id, 0);
    assert_eq!(bar.name, "bar");
    assert_eq!(bar.types, vec![0, 1, 3]);

    let fub = &d.constants[1];
    assert_eq!(fub.id, 1);
    assert_eq!(fub.name, "fub");
    assert_eq!(fub.types, vec![2, 3]);

    Ok(())
}

#[test]
fn constants_return_error_when_typing_not_declared() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips )
           (:constants bar - block))",
    );

    if let Err(e) = d {
        if let ErrorType::MissingRequirement { req, what: _ } = e[0].what {
            assert_eq!(req, Requirement::Typing);
            return;
        }
    }
    panic!("Missing :types requirement error not returned");
}

#[test]
fn can_parse_action_params() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:action Bar :parameters())
           (:action FUB
             :parameters (?a - (either Sphere Square) ?b - BLOCK))
           (:action baz
             :parameters (?a - OBJECT ?b)))",
    )?;

    let bar = &d.actions[0];
    assert_eq!(bar.id, 0);
    assert_eq!(bar.name, "bar");
    assert_eq!(bar.params.len(), 0);

    let fub = &d.actions[1];
    assert_eq!(fub.id, 1);
    assert_eq!(fub.name, "fub");
    assert_eq!(fub.params[0].types, param!(2, 3).types);
    assert_eq!(fub.params[1].types, param!(1).types);

    let baz = &d.actions[2];
    assert_eq!(baz.id, 2);
    assert_eq!(baz.name, "baz");
    assert_eq!(baz.params[0].types, param!(0).types);
    assert_eq!(baz.params[1].types.len(), 0);

    Ok(())
}

#[test]
fn actions_collates_either_types() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:action bar :parameters (?a - square ?a - block)))",
    )?;

    let bar = &d.actions[0];
    assert_eq!(bar.id, 0);
    assert_eq!(bar.name, "bar");
    assert_eq!(bar.params.len(), 1);
    assert_eq!(bar.params[0].types, vec![1, 2]);

    Ok(())
}

#[test]
fn return_error_for_duplicate_action() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:action bar :parameters ())
           (:action Bar :parameters ()))",
    );

    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(s, "action, bar, is already defined");
            return;
        }
    }
    panic!("Duplicate action error not detected");
}

#[test]
fn can_parse_empty_action_precondition() -> Result<(), Errors> {
    let d = Domain::parse("(define (domain d) (:action bar :parameters () :precondition ()))")?;

    let bar = &d.actions[0];
    assert_eq!(bar.id, 0);
    assert_eq!(bar.name, "bar");
    assert_eq!(bar.params.len(), 0);
    assert_eq!(bar.precondition, None);

    Ok(())
}

#[test]
fn can_parse_precondition_predicate() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:predicates (foo))
           (:action a
             :parameters()
             :precondition (foo)))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);
    assert_eq!(a.precondition, Some(Goal::Pred(0, vec![])));

    Ok(())
}

#[test]
fn precondition_predicate_fails_with_predicate_not_defined() {
    let d = Domain::parse(
        "(define (domain d)
           (:predicates (foo))
           (:action a
             :parameters()
             :precondition (fo)))",
    );

    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(s, "predicate, fo, not defined");
            return;
        }
    }
    panic!("predicate not defined error not detected");
}

#[test]
fn can_parse_precondition_predicate_with_constant_term() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:constants wood-block metal-block - block)
           (:predicates (holding ?a - block))
           (:action a
             :parameters()
             :precondition (holding METAL-BLOCK)))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);
    assert_eq!(a.precondition, Some(Goal::Pred(0, vec![Term::Const(1)])));

    Ok(())
}

#[test]
fn precondition_predicate_fails_with_constant_not_defined() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:predicates (holding ?a - block))
           (:action a
             :parameters()
             :precondition (holding METAL-BLOCK)))",
    );

    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(s, "constant, metal-block, not defined");
            return;
        }
    }
    panic!("constant not defined error not detected");
}

#[test]
fn can_parse_precondition_predicate_with_variable_term() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:predicates (holding ?a - block))
           (:action a
             :parameters (?b - block)
             :precondition (holding ?B)))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);
    assert_eq!(
        a.precondition,
        Some(Goal::Pred(0, vec![Term::Var(vec![1])]))
    );

    Ok(())
}

#[test]
fn precondition_predicate_fails_with_variable_not_defined() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:predicates (holding ?a - block))
           (:action a
             :parameters (?b - block)
             :precondition (holding ?a)))",
    );

    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(s, "variable, ?a, not defined");
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("variable not defined error not detected");
}

#[test]
fn can_parse_precondition_predicate_with_func_term() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :object-fluents)
           (:types block square sphere)
           (:predicates (holding ?a - sphere))
           (:functions (transform ?b - block) - sphere)
           (:action a
             :parameters (?b - BLOCK)
             :precondition (Holding (Transform ?B))))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let f = Term::Func(0, vec![Term::Var(vec![1])]);
    assert_eq!(a.precondition, Some(Goal::Pred(0, vec![f])));

    Ok(())
}

#[test]
fn precondition_predicate_fails_with_func_term_not_defined() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :object-fluents)
           (:types block square sphere)
           (:predicates (holding ?a - sphere))
           (:functions (transform ?b - block) - sphere)
           (:action a
             :parameters (?b - BLOCK)
             :precondition (Holding (tranform ?B))))",
    );

    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(s, "function, tranform, not defined");
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("function not defined error not detected");
}

#[test]
fn precondition_func_term_fails_with_arg_of_wrong_type() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :object-fluents)
           (:types block square sphere)
           (:predicates (holding ?a - sphere))
           (:functions (transform ?b - (either block sphere)) - sphere)
           (:action a
             :parameters (?b - square)
             :precondition (Holding (transform ?B))))",
    );

    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(
                s,
                "none of the types for ?B are one of or a subtype of [\"block\", \"sphere\"]"
            );
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("function arg wrong type error not detected");
}

#[test]
fn precondition_predicate_fails_with_arg_of_wrong_type() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:predicates (holding ?a - sphere))
           (:action a
             :parameters (?b - square)
             :precondition (Holding ?b)))",
    );

    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(
                s,
                "none of the types for ?b are one of or a subtype of [\"sphere\"]"
            );
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("function arg wrong type error not detected");
}

#[test]
fn can_parse_precondition_predicate_with_arg_of_no_type() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips)
           (:predicates (holding ?a))
           (:action a
             :parameters (?b)
             :precondition (Holding ?b)))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);
    assert_eq!(a.precondition, Some(Goal::Pred(0, vec![Term::Var(vec![])])));

    Ok(())
}

#[test]
fn precondition_predicate_fails_with_arg_of_no_type() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:predicates (holding ?a - sphere))
           (:action a
             :parameters (?b)
             :precondition (Holding ?b)))",
    );

    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(s, "?b does not represent a type");
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("predicate arg of no type error not detected");
}

#[test]
fn precondition_predicate_fails_with_typed_arg_but_none_is_required() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:predicates (holding ?a))
           (:action a
             :parameters (?b - sphere)
             :precondition (Holding ?b)))",
    );

    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(
                s,
                "?b implements a type but none are allowed for the argument"
            );
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("predicate with typed arg but none required error not detected");
}

#[test]
fn can_parse_precondition_func_term_with_arg_of_no_type() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :object-fluents)
           (:types block square sphere)
           (:predicates (holding ?a - sphere))
           (:functions (transform ?b) - sphere)
           (:action a
             :parameters (?b)
             :precondition (Holding (transform ?B))))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let f = Term::Func(0, vec![Term::Var(vec![])]);
    assert_eq!(a.precondition, Some(Goal::Pred(0, vec![f])));

    Ok(())
}

#[test]
fn precondition_func_term_fails_with_arg_of_no_type() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :object-fluents)
           (:types block square sphere)
           (:predicates (holding ?a - sphere))
           (:functions (transform ?b - block) - sphere)
           (:action a
             :parameters (?b)
             :precondition (Holding (transform ?b))))",
    );

    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(s, "?b does not represent a type");
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("func term arg of no type error not detected");
}

#[test]
fn precondition_func_term_fails_with_typed_arg_but_none_is_required() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :object-fluents)
           (:types block square sphere)
           (:predicates (holding ?a - sphere))
           (:functions (transform ?b) - sphere)
           (:action a
             :parameters (?b - block)
             :precondition (Holding (transform ?b))))",
    );

    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(
                s,
                "?b implements a type but none are allowed for the argument"
            );
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("func term with typed arg but none required error not detected");
}

#[test]
fn precondition_func_term_fails_when_it_does_not_return_a_type() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :object-fluents :numeric-fluents)
           (:types block square sphere)
           (:predicates (holding ?a - sphere))
           (:functions (transform ?b - block))
           (:action a
             :parameters (?b - block)
             :precondition (Holding (transform ?b))))",
    );

    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(s, "function, transform, does not return a type");
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("func term not returning a type error not detected");
}

#[test]
fn precondition_not_fails_with_missing_requirement() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips)
           (:predicates (holding))
           (:action a
             :parameters ()
             :precondition (NOT (Holding))))",
    );

    if let Err(e) = d {
        if let ErrorType::MissingRequirement { req, what: _ } = e[0].what {
            assert_eq!(req, Requirement::NegativePreconditions);
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("Missing negative preconditions requirement error not returned.");
}

#[test]
fn can_parse_precondition_less_than() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :numeric-fluents)
           (:action a
             :parameters ()
             :precondition (< 1 2)))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let f1 = Fexp::Number(1.0);
    let f2 = Fexp::Number(2.0);
    assert_eq!(a.precondition, Some(Goal::Less(f1, f2)));

    Ok(())
}

#[test]
fn can_parse_precondition_less_eq_than() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :numeric-fluents)
           (:action a
             :parameters ()
             :precondition (<= 1 2)))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let f1 = Fexp::Number(1.0);
    let f2 = Fexp::Number(2.0);
    assert_eq!(a.precondition, Some(Goal::LessEq(f1, f2)));

    Ok(())
}

#[test]
fn can_parse_precondition_greater_than() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :numeric-fluents)
           (:action a
             :parameters ()
             :precondition (> 1 2)))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let f1 = Fexp::Number(1.0);
    let f2 = Fexp::Number(2.0);
    assert_eq!(a.precondition, Some(Goal::Greater(f1, f2)));

    Ok(())
}

#[test]
fn can_parse_precondition_greater_eq_than() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :numeric-fluents)
           (:action a
             :parameters ()
             :precondition (>= 1 2)))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let f1 = Fexp::Number(1.0);
    let f2 = Fexp::Number(2.0);
    assert_eq!(a.precondition, Some(Goal::GreaterEq(f1, f2)));

    Ok(())
}

#[test]
fn precondition_less_than_fails_with_missing_requirement() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips)
           (:action a
             :parameters ()
             :precondition (< 1 2)))",
    );

    if let Err(e) = d {
        if let ErrorType::MissingRequirement { req, what: _ } = e[0].what {
            assert_eq!(req, Requirement::NumericFluents);
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("Missing numeric fluents requirement error not returned.");
}

#[test]
fn precondition_fexp_returns_fn_symbol() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :numeric-fluents)
           (:action a
             :parameters ()
             :precondition (< foo bar)))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let f1 = Fexp::FnSymbol("foo".to_string());
    let f2 = Fexp::FnSymbol("bar".to_string());
    assert_eq!(a.precondition, Some(Goal::Less(f1, f2)));

    Ok(())
}

#[test]
fn precondition_fexp_func_term_fails_when_not_returning_number() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :object-fluents :numeric-fluents)
           (:functions (foo) - object (bar ?a))
           (:action a
             :parameters (?a)
             :precondition (< (foo) (bar ?a))))",
    );

    if let Err(e) = d {
        if let ErrorType::SemanticError(s) = &e[0].what {
            assert_eq!(s, "function, foo, does not return a number");
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("fexp function term not returning a number error not detected");
}

#[test]
fn precondition_fexp_returns_func_expr() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :numeric-fluents)
           (:functions (foo) (bar ?a))
           (:action a
             :parameters (?a)
             :precondition (< (foo) (bar ?a))))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let f1 = Fexp::Func(0, vec![]);
    let f2 = Fexp::Func(1, vec![Term::Var(vec![])]);
    assert_eq!(a.precondition, Some(Goal::Less(f1, f2)));

    Ok(())
}

#[test]
fn precondition_fexp_returns_mult() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :numeric-fluents)
           (:action a
             :parameters (?a)
             :precondition (< (* 1 2) (* 1 2 3))))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let n1 = Fexp::Number(1.0);
    let n2 = Fexp::Number(2.0);

    let m1 = Fexp::Number(1.0);
    let m2 = Fexp::Number(2.0);
    let m3 = Fexp::Number(3.0);

    let f1 = Fexp::Mult(Box::new(n1), vec![n2]);
    let f2 = Fexp::Mult(Box::new(m1), vec![m2, m3]);
    assert_eq!(a.precondition, Some(Goal::Less(f1, f2)));

    Ok(())
}

#[test]
fn fexp_mult_fails_with_not_enough_args() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :numeric-fluents)
           (:action a
             :parameters (?a)
             :precondition (< (* 1) (* 1 2 3))))",
    );

    if let Err(e) = d {
        if let ErrorType::Expect {
            have: h,
            expect: ex,
        } = &e[0].what
        {
            assert_eq!(h, ")");
            assert_eq!(*ex, ["number", "identifier", "("]);
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("too few mult args err not detected");
}

#[test]
fn precondition_fexp_returns_add() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :numeric-fluents)
           (:action a
             :parameters (?a)
             :precondition (< (+ 1 foo) (+ 1 2 bar))))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let n1 = Fexp::Number(1.0);
    let n2 = Fexp::FnSymbol("foo".to_string());

    let m1 = Fexp::Number(1.0);
    let m2 = Fexp::Number(2.0);
    let m3 = Fexp::FnSymbol("bar".to_string());

    let f1 = Fexp::Add(Box::new(n1), vec![n2]);
    let f2 = Fexp::Add(Box::new(m1), vec![m2, m3]);
    assert_eq!(a.precondition, Some(Goal::Less(f1, f2)));

    Ok(())
}

#[test]
fn fexp_add_fails_with_not_enough_args() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :numeric-fluents)
           (:action a
             :parameters (?a)
             :precondition (< (+ 1) (+ 1 2 bar))))",
    );

    if let Err(e) = d {
        if let ErrorType::Expect {
            have: h,
            expect: ex,
        } = &e[0].what
        {
            assert_eq!(h, ")");
            assert_eq!(*ex, ["number", "identifier", "("]);
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("too few add args err not detected");
}

#[test]
fn precondition_fexp_returns_div() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :numeric-fluents)
           (:action a
             :parameters (?a)
             :precondition (< (/ 1 foo) (/ 1 bar))))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let n1 = Fexp::Number(1.0);
    let n2 = Fexp::FnSymbol("foo".to_string());

    let m1 = Fexp::Number(1.0);
    let m2 = Fexp::FnSymbol("bar".to_string());

    let f1 = Fexp::Div(Box::new(n1), Box::new(n2));
    let f2 = Fexp::Div(Box::new(m1), Box::new(m2));
    assert_eq!(a.precondition, Some(Goal::Less(f1, f2)));

    Ok(())
}

#[test]
fn fexp_div_fails_with_not_enough_args() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :numeric-fluents)
           (:action a
             :parameters (?a)
             :precondition (< (/ 1) (/ 1 2))))",
    );

    if let Err(e) = d {
        if let ErrorType::Expect {
            have: h,
            expect: ex,
        } = &e[0].what
        {
            assert_eq!(h, ")");
            assert_eq!(*ex, ["number", "identifier", "("]);
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("too few div args err not detected");
}

#[test]
fn fexp_div_fails_with_too_many_args() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :numeric-fluents)
           (:action a
             :parameters (?a)
             :precondition (< (/ 1 2 3) (/ 1 2))))",
    );

    if let Err(e) = d {
        if let ErrorType::Expect {
            have: h,
            expect: ex,
        } = &e[0].what
        {
            assert_eq!(h, "3");
            assert_eq!(*ex, [")"]);
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("too many div args err not detected");
}

#[test]
fn precondition_fexp_returns_sub() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :numeric-fluents)
           (:action a
             :parameters (?a)
             :precondition (< (- 1 foo) (- 1 bar))))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let n1 = Fexp::Number(1.0);
    let n2 = Fexp::FnSymbol("foo".to_string());

    let m1 = Fexp::Number(1.0);
    let m2 = Fexp::FnSymbol("bar".to_string());

    let f1 = Fexp::Sub(Box::new(n1), Box::new(n2));
    let f2 = Fexp::Sub(Box::new(m1), Box::new(m2));
    assert_eq!(a.precondition, Some(Goal::Less(f1, f2)));

    Ok(())
}

#[test]
fn fexp_sub_fails_with_too_many_args() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :numeric-fluents)
           (:action a
             :parameters (?a)
             :precondition (< (- 1 2 3) (- 1 2))))",
    );

    if let Err(e) = d {
        if let ErrorType::Expect {
            have: h,
            expect: ex,
        } = &e[0].what
        {
            assert_eq!(h, "3");
            assert_eq!(*ex, [")"]);
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("too many sub args err not detected");
}

#[test]
fn precondition_fexp_returns_neg() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :numeric-fluents)
           (:action a
             :parameters (?a)
             :precondition (< (- 1) (- 2))))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let n1 = Fexp::Number(1.0);
    let m1 = Fexp::Number(2.0);

    let f1 = Fexp::Neg(Box::new(n1));
    let f2 = Fexp::Neg(Box::new(m1));
    assert_eq!(a.precondition, Some(Goal::Less(f1, f2)));

    Ok(())
}

#[test]
fn can_parse_precondition_equality_with_constants() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :equality)
           (:types block square sphere)
           (:constants metal - block wood - square)
           (:action a
             :parameters (?b - BLOCK)
             :precondition (= metal wood)))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let t0 = Term::Const(0);
    let t1 = Term::Const(1);

    assert_eq!(a.precondition, Some(Goal::EqualTerms(t0, t1)));

    Ok(())
}

#[test]
fn can_parse_precondition_equality_with_variables() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :equality)
           (:types block square sphere)
           (:action a
             :parameters (?b - BLOCK ?m)
             :precondition (= ?b ?m)))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let t0 = Term::Var(vec![1]);
    let t1 = Term::Var(vec![]);

    assert_eq!(a.precondition, Some(Goal::EqualTerms(t0, t1)));

    Ok(())
}

#[test]
fn can_parse_precondition_equality_with_func_terms() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :equality :object-fluents)
           (:types block square sphere)
           (:functions
              (foo) - object
              (bar) - block)
           (:action a
             :parameters ()
             :precondition (= (foo) (bar))))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let t0 = Term::Func(0, vec![]);
    let t1 = Term::Func(1, vec![]);

    assert_eq!(a.precondition, Some(Goal::EqualTerms(t0, t1)));

    Ok(())
}

#[test]
fn can_parse_precondition_equality_with_mixed_terms() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :equality :object-fluents)
           (:types block square sphere)
           (:constants metal - block)
           (:functions
              (foo) - object
              (bar) - block)
           (:action a
             :parameters ()
             :precondition (= metal (bar))))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let t0 = Term::Const(0);
    let t1 = Term::Func(1, vec![]);

    assert_eq!(a.precondition, Some(Goal::EqualTerms(t0, t1)));

    Ok(())
}

#[test]
fn can_parse_precondition_equality_with_mixed_terms_2() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :equality :object-fluents)
           (:types block square sphere)
           (:functions
              (foo) - object
              (bar) - block)
           (:action a
             :parameters (?b)
             :precondition (= (foo) ?b)))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let t0 = Term::Func(0, vec![]);
    let t1 = Term::Var(vec![]);

    assert_eq!(a.precondition, Some(Goal::EqualTerms(t0, t1)));

    Ok(())
}

#[test]
fn can_parse_precondition_equality_with_func_fexps() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :equality :fluents)
           (:types block square sphere)
           (:functions (foo) (bar))
           (:action a
             :parameters ()
             :precondition (= (foo) (bar))))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let t0 = Fexp::Func(0, vec![]);
    let t1 = Fexp::Func(1, vec![]);

    assert_eq!(a.precondition, Some(Goal::EqualFexps(t0, t1)));

    Ok(())
}

#[test]
fn can_parse_precondition_equality_with_fn_symbol() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :fluents)
           (:types block square sphere)
           (:action a
             :parameters ()
             :precondition (= baz quux)))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let t0 = Fexp::FnSymbol("baz".to_string());
    let t1 = Fexp::FnSymbol("quux".to_string());

    assert_eq!(a.precondition, Some(Goal::EqualFexps(t0, t1)));

    Ok(())
}

#[test]
fn can_parse_precondition_equality_with_numbers() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :fluents)
           (:types block square sphere)
           (:action a
             :parameters ()
             :precondition (= 1.2 2.0)))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let t0 = Fexp::Number(1.2);
    let t1 = Fexp::Number(2.0);

    assert_eq!(a.precondition, Some(Goal::EqualFexps(t0, t1)));

    Ok(())
}

#[test]
fn can_parse_precondition_equality_with_op_fexp() -> Result<(), Errors> {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :fluents)
           (:types block square sphere)
           (:action a
             :parameters ()
             :precondition (= (* 2 3) (+ 1 2 3))))",
    )?;

    let a = &d.actions[0];
    assert_eq!(a.id, 0);

    let n2 = Fexp::Number(2.0);
    let n3 = Fexp::Number(3.0);

    let m1 = Fexp::Number(1.0);
    let m2 = Fexp::Number(2.0);
    let m3 = Fexp::Number(3.0);

    let f1 = Fexp::Mult(Box::new(n2), vec![n3]);
    let f2 = Fexp::Add(Box::new(m1), vec![m2, m3]);

    assert_eq!(a.precondition, Some(Goal::EqualFexps(f1, f2)));

    Ok(())
}

#[test]
fn equality_fails_with_bad_right_fexp() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :fluents)
           (:types block square sphere)
           (:functions (foo))
           (:action a
             :parameters ()
             :precondition (= (foo) %)))",
    );

    if let Err(e) = d {
        if let ErrorType::Expect {
            have: h,
            expect: ex,
        } = &e[0].what
        {
            assert_eq!(h, "%");
            assert_eq!(*ex, ["number", "identifier", "("]);
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("right fexp error not detected");
}

#[test]
fn equality_fails_with_bad_left_exp() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :fluents)
           (:types block square sphere)
           (:functions (foo) - object)
           (:action a
             :parameters ()
             :precondition (= % 3)))",
    );

    if let Err(e) = d {
        if let ErrorType::Expect {
            have: h,
            expect: ex,
        } = &e[0].what
        {
            assert_eq!(h, "%");
            assert_eq!(*ex, ["number", "identifier", "("]);
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("left fexp error not detected");
}

#[test]
fn equality_fails_with_bad_right_term() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :fluents)
           (:types block square sphere)
           (:functions (foo) - object)
           (:action a
             :parameters ()
             :precondition (= (foo) 3)))",
    );

    if let Err(e) = d {
        if let ErrorType::Expect {
            have: h,
            expect: ex,
        } = &e[0].what
        {
            assert_eq!(h, "3");
            assert_eq!(*ex, ["identifier", "variable", "("]);
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("right fexp error not detected");
}

#[test]
fn equality_fails_with_missing_equality_requirement() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing :fluents)
           (:types block square sphere)
           (:action a
             :parameters (?a ?b)
             :precondition (= ?a ?b)))",
    );

    if let Err(e) = d {
        if let ErrorType::MissingRequirement { req, what: _ } = e[0].what {
            assert_eq!(req, Requirement::Equality);
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("missing equality requirement error not detected");
}

#[test]
fn equality_fails_with_missing_numeric_fluents_requirement() {
    let d = Domain::parse(
        "(define (domain d)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:action a
             :parameters ()
             :precondition (= foo (* 2 3 4))))",
    );

    if let Err(e) = d {
        if let ErrorType::MissingRequirement { req, what: _ } = e[0].what {
            assert_eq!(req, Requirement::NumericFluents);
            return;
        } else {
            panic!("WRONG ERROR: {:?}", e);
        }
    }
    panic!("missing numeric fluents requirement error not detected");
}
