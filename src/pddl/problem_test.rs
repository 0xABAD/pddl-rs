use super::*;

#[test]
fn check_if_problem() {
    assert!(Problem::is_problem("(define (problem p1"));
}

#[test]
fn check_if_not_problem() {
    assert!(!Problem::is_problem("(define (domain d"));
}

#[test]
fn parse_problem_name() -> Result<(), Errors> {
    let prob = Problem::parse(
        "(define (problem foo)
           (:domain bar)
           (:init)
           (:goal (and)))")?;

    assert_eq!(prob.name, "foo".to_string());
    assert_eq!(prob.domain, "bar".to_string());

    Ok(())
}
