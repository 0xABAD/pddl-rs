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
fn parse_top_level_name() -> Result<(), ParseError> {
    let dom = Domain::parse("(define (domain foo))")?;
    assert_eq!(dom.name, "foo");
    Ok(())
}

#[test]
fn unexpected_top_level_end_of_input() {
    if let Err(pe) = Domain::parse("(define (domain foo)") {
        match pe.what {
            ParseErrorType::Expect { have: _, expect } => assert_eq!(expect, vec!["(", ")"]),
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
            ParseErrorType::Expect { have: _, expect } => assert_eq!(expect, vec!["(", ")"]),
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
            ParseErrorType::Expect { have: _, expect } => assert_eq!(
                expect,
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
fn can_parse_requirements() -> Result<(), ParseError> {
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
fn no_requirements_implies_strips() -> Result<(), ParseError> {
    let d = Domain::parse("(define (domain foo))")?;
    assert!(d.has_requirement(Requirement::Strips));
    Ok(())
}

#[test]
fn parse_requirements_allows_duplicates() -> Result<(), ParseError> {
    let d = Domain::parse("(define (domain foo) (:requirements :strips :typing :strips :typing))")?;
    assert!(d.has_requirement(Requirement::Strips));
    assert!(d.has_requirement(Requirement::Typing));
    Ok(())
}

#[test]
fn quantified_preconditions_implies_others() -> Result<(), ParseError> {
    let d = Domain::parse("(define (domain foo) (:requirements :quantified-preconditions))")?;
    assert!(d.has_requirement(Requirement::QuantifiedPreconditions));
    assert!(d.has_requirement(Requirement::ExistentialPreconditions));
    assert!(d.has_requirement(Requirement::UniversalPreconditions));
    Ok(())
}

#[test]
fn fluents_implies_others() -> Result<(), ParseError> {
    let d = Domain::parse("(define (domain foo) (:requirements :fluents))")?;
    assert!(d.has_requirement(Requirement::Fluents));
    assert!(d.has_requirement(Requirement::NumericFluents));
    assert!(d.has_requirement(Requirement::ObjectFluents));
    Ok(())
}

#[test]
fn adl_implies_others() -> Result<(), ParseError> {
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
fn timed_initial_literals_implies_others() -> Result<(), ParseError> {
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
            ParseErrorType::Expect { have: _, expect } => {
                let mut v = REQUIREMENTS.to_vec();
                v.push(")");
                assert_eq!(expect, v)
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
            ParseErrorType::Expect { have: _, expect } => {
                let mut v = REQUIREMENTS.to_vec();
                v.push(")");
                assert_eq!(expect, v)
            }
            _ => panic!("Invalid ParseErrorType -- have {:?}, want Expect", pe.what),
        }
    } else {
        panic!("Expected error but received successful domain parse");
    }
}

#[test]
fn can_parse_types() -> Result<(), ParseError> {
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
fn has_default_object() -> Result<(), ParseError> {
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
fn correct_constants_from_top_level() -> Result<(), ParseError> {
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
            ParseErrorType::Expect { have: _, expect: _ } => return,
            _ => panic!("Invalid ParseErrorType -- have {:?}, want Expect", pe.what),
        }
    } else {
        panic!("Received successful parse when error should have occurred.");
    }
}

#[test]
fn constraints_section_missing_requirement() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips)
           (:constraints (and)))",
    );
    if let Err(pe) = d {
        if let ParseErrorType::MissingRequirement { req, what: _ } = pe.what {
            if req == Requirement::Constraints {
                return;
            }
        }
    }
    panic!("Missing constraints requirement error not returned.");
}

#[test]
fn durative_action_missing_requirement() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips)
           (:durative-action bar
              :parameters ()
              :duration ()
              :condition ()
              :effect ()))",
    );
    if let Err(pe) = d {
        if let ParseErrorType::MissingRequirement { req, what: _ } = pe.what {
            if req == Requirement::DurativeActions {
                return;
            }
        }
    }
    panic!("Missing durative-actions requirement error not returned.");
}

#[test]
fn derived_predicate_missing_requirement() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips)
           (:predicates (baz) (quux))
           (:derived (bar) (and (baz) (quux))))",
    );
    if let Err(pe) = d {
        if let ParseErrorType::MissingRequirement { req, what: _ } = pe.what {
            if req == Requirement::DerivedPredicates {
                return;
            }
        }
    }
    panic!("Missing derived-predicates requirement error not returned.");
}

#[test]
fn can_parse_predicates_without_typing() -> Result<(), ParseError> {
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
fn can_parse_predicates() -> Result<(), ParseError> {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:predicates (bar ?a - object)
                        (baz ?a ?b - sphere ?c -block)
                        (quux ?a - square ?b ?c - (either block square))))",
    )?;

    let bar = &d.predicates[0];
    assert_eq!(bar.id, 0);
    assert_eq!(bar.name, "bar");
    assert_eq!(bar.params, vec![Param(vec![0])]);

    let baz = &d.predicates[1];
    assert_eq!(baz.id, 1);
    assert_eq!(baz.name, "baz");
    assert_eq!(
        baz.params,
        vec![Param(vec![3]), Param(vec![3]), Param(vec![1])]
    );

    let quux = &d.predicates[2];
    assert_eq!(quux.id, 2);
    assert_eq!(quux.name, "quux");
    assert_eq!(
        quux.params,
        vec![Param(vec![2]), Param(vec![1, 2]), Param(vec![1, 2])]
    );

    Ok(())
}

#[test]
fn predicates_collates_either_types() -> Result<(), ParseError> {
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
    assert_eq!(bar.params, vec![Param(vec![0, 1, 2]), Param(vec![2, 3])]);

    let fub = &d.predicates[1];
    assert_eq!(fub.id, 1);
    assert_eq!(fub.name, "fub");
    assert_eq!(
        fub.params,
        vec![Param(vec![0, 3]), Param(vec![0, 1]), Param(vec![2, 3])]
    );

    Ok(())
}

#[test]
fn collected_predicates_fail_with_mismatching_arity() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:predicates (bar ?a - object)
                        (bar ?a - block ?b - object)))",
    );
    if let Err(e) = d {
        if let ParseErrorType::SemanticError(s) = e.what {
            assert_eq!(s, "bar already declared or has mis-matching arity");
            return;
        }
    }
    panic!("Mis-matching arity error not returned");
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
        if let ParseErrorType::TypeNotDefined(t) = e.what {
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
        if let ParseErrorType::TypeNotDefined(t) = e.what {
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
           (:types block square sphere)
           (:predicates (bar ?a - object)
                        (baz ?a ?b - sphere ?c - block)
                        (quux ?a - square ?b ?c - (either block square))))",
    );

    if let Err(e) = d {
        if let ParseErrorType::MissingRequirement { req, what: _ } = e.what {
            assert_eq!(req, Requirement::Typing);
            return;
        }
    }
    panic!("Missing :types requirement error not returned");
}

#[test]
fn can_parse_functions() -> Result<(), ParseError> {
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
    assert_eq!(bar.params, vec![Param(vec![0])]);
    assert_eq!(bar.return_types, vec![]);
    assert!(bar.returns_number);

    let bar2 = &d.functions[1];
    assert_eq!(bar2.id, 1);
    assert_eq!(bar2.name, "bar2");
    assert_eq!(bar2.params, vec![Param(vec![0])]);
    assert_eq!(bar2.return_types, vec![]);
    assert!(bar2.returns_number);

    let baz = &d.functions[2];
    assert_eq!(baz.id, 2);
    assert_eq!(baz.name, "baz");
    assert_eq!(
        baz.params,
        vec![Param(vec![3]), Param(vec![3]), Param(vec![1])]
    );
    assert_eq!(baz.return_types, vec![1, 3]);
    assert!(!baz.returns_number);

    let quux = &d.functions[3];
    assert_eq!(quux.id, 3);
    assert_eq!(quux.name, "quux");
    assert_eq!(
        quux.params,
        vec![Param(vec![2]), Param(vec![1, 2]), Param(vec![1, 2])]
    );
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
fn functions_collates_either_types() -> Result<(), ParseError> {
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
    assert_eq!(bar.params, vec![Param(vec![0, 2, 3])]);
    assert_eq!(bar.return_types, vec![]);
    assert!(bar.returns_number);

    let fub = &d.functions[1];
    assert_eq!(fub.id, 1);
    assert_eq!(fub.name, "fub");
    assert_eq!(fub.params, vec![Param(vec![0])]);
    assert_eq!(fub.return_types, vec![]);
    assert!(fub.returns_number);

    let baz = &d.functions[2];
    assert_eq!(baz.id, 2);
    assert_eq!(baz.name, "baz");
    assert_eq!(
        baz.params,
        vec![Param(vec![3]), Param(vec![3]), Param(vec![1])]
    );
    assert_eq!(baz.return_types, vec![1, 3]);
    assert!(baz.returns_number);

    let quux = &d.functions[3];
    assert_eq!(quux.id, 3);
    assert_eq!(quux.name, "quux");
    assert_eq!(
        quux.params,
        vec![Param(vec![2]), Param(vec![1, 2]), Param(vec![1, 2])]
    );
    assert_eq!(quux.return_types, vec![0, 1]);
    assert!(!quux.returns_number);

    Ok(())
}

#[test]
fn parse_functions_fails_when_typing_not_declared() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips)
           (:functions (baz ?a ?b) - (either sphere block)))",
    );

    if let Err(e) = d {
        if let ParseErrorType::MissingRequirement { req, what: _ } = e.what {
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
        if let ParseErrorType::MissingRequirement { req, what: _ } = e.what {
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
        if let ParseErrorType::MissingRequirement { req, what: _ } = e.what {
            assert_eq!(req, Requirement::NumericFluents);
            return;
        }
    }
    panic!("Missing :numeric-fluents requirement error not returned");
}

#[test]
fn parse_functions_fails_when_numeric_fluents_not_declared2() {
    let d = Domain::parse(
        "(define (domain foo)
           (:requirements :strips :typing)
           (:types block square sphere)
           (:functions (baz ?a ?b) - number))",
    );

    if let Err(e) = d {
        if let ParseErrorType::MissingRequirement { req, what: _ } = e.what {
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
        if let ParseErrorType::TypeNotDefined(t) = e.what {
            assert_eq!(t, "ball");
            return;
        }
    }
    panic!("Type defined error not returned");
}
