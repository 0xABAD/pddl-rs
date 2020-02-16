use super::*;

#[test]
fn check_if_domain() {
    const DOMAIN: &'static str = "(define (domain foo))";
    assert!(Domain::is_domain(DOMAIN));
}

#[test]
fn check_if_not_domain() {
    const DOMAIN: &'static str = "(define (problem foo-p1))";
    assert!(!Domain::is_domain(DOMAIN));
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
