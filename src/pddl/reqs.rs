use std::fmt;

/// `Reqs` maintains all known requirements through the use of a
/// bit vector.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct Reqs(u32);

impl Default for Reqs {
    fn default() -> Self {
        Reqs(0)
    }
}

impl Reqs {
    /// `has` returns true if `reqs` has the requirement of `r`.
    pub fn has(&self, r: Requirement) -> bool {
        let b = self.0 & (1 << r.index());
        if r == Requirement::Strips {
            return self.0 == 0 || b > 0;
        }
        b > 0
    }

    /// `add` adds the `req_index` to the current existing requirements
    /// bit vector while also expanding implied requirements of `req_index`.
    pub fn add(&mut self, r: Requirement) {
        let mut reqs = 1 << r.index();

        if let Requirement::QuantifiedPreconditions = r {
            reqs = reqs | (1 << Requirement::ExistentialPreconditions.index());
            reqs = reqs | (1 << Requirement::UniversalPreconditions.index());
        } else if let Requirement::Fluents = r {
            reqs = reqs | (1 << Requirement::NumericFluents.index());
            reqs = reqs | (1 << Requirement::ObjectFluents.index());
        } else if let Requirement::TimedInitialLiterals = r {
            reqs = reqs | (1 << Requirement::DurativeActions.index());
        } else if let Requirement::Adl = r {
            reqs = reqs | (1 << Requirement::Strips.index());
            reqs = reqs | (1 << Requirement::Typing.index());
            reqs = reqs | (1 << Requirement::Equality.index());
            reqs = reqs | (1 << Requirement::NegativePreconditions.index());
            reqs = reqs | (1 << Requirement::DisjunctivePreconditions.index());
            reqs = reqs | (1 << Requirement::QuantifiedPreconditions.index());
            reqs = reqs | (1 << Requirement::ExistentialPreconditions.index());
            reqs = reqs | (1 << Requirement::UniversalPreconditions.index());
            reqs = reqs | (1 << Requirement::ConditionalEffects.index());
        }

        self.0 = self.0 | reqs;
    }
}

/// `Requirement` represents one of the allowed requirement specifications
/// that may be within a PDDL domain.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Requirement {
    Strips,
    Typing,
    Equality,
    NegativePreconditions,
    DisjunctivePreconditions,
    ExistentialPreconditions,
    UniversalPreconditions,
    QuantifiedPreconditions,
    ConditionalEffects,
    Fluents,
    NumericFluents,
    ObjectFluents,
    Adl,
    DurativeActions,
    DurationInequalities,
    ContinuousEffects,
    DerivedPredicates,
    TimedInitialLiterals,
    Preferences,
    Constraints,
    ActionCosts,
}

impl Requirement {
    /// `index` returns index of the `Requirement` to get the string form
    /// from the `REQUIREMENTS` array.
    fn index(self) -> usize {
        match self {
            Requirement::Strips => 0,
            Requirement::Typing => 1,
            Requirement::Equality => 2,
            Requirement::NegativePreconditions => 3,
            Requirement::DisjunctivePreconditions => 4,
            Requirement::ExistentialPreconditions => 5,
            Requirement::UniversalPreconditions => 6,
            Requirement::QuantifiedPreconditions => 7,
            Requirement::ConditionalEffects => 8,
            Requirement::Fluents => 9,
            Requirement::NumericFluents => 10,
            Requirement::ObjectFluents => 11,
            Requirement::Adl => 12,
            Requirement::DurativeActions => 13,
            Requirement::DurationInequalities => 14,
            Requirement::ContinuousEffects => 15,
            Requirement::DerivedPredicates => 16,
            Requirement::TimedInitialLiterals => 17,
            Requirement::Preferences => 18,
            Requirement::Constraints => 19,
            Requirement::ActionCosts => 20,
        }
    }

    fn as_str(self) -> &'static str {
        match self {
            Requirement::Strips => ":strips",
            Requirement::Typing => ":typing",
            Requirement::Equality => ":equality",
            Requirement::NegativePreconditions => ":negative-preconditions",
            Requirement::DisjunctivePreconditions => ":disjunctive-preconditions",
            Requirement::ExistentialPreconditions => ":existential-preconditions",
            Requirement::UniversalPreconditions => ":universal-preconditions",
            Requirement::QuantifiedPreconditions => ":quantified-preconditions",
            Requirement::ConditionalEffects => ":conditional-effects",
            Requirement::Fluents => ":fluents",
            Requirement::NumericFluents => ":numeric-fluents",
            Requirement::ObjectFluents => ":object-fluents",
            Requirement::Adl => ":adl",
            Requirement::DurativeActions => ":durative-actions",
            Requirement::DurationInequalities => ":duration-inequalities",
            Requirement::ContinuousEffects => ":continuous-effects",
            Requirement::DerivedPredicates => ":derived-predicates",
            Requirement::TimedInitialLiterals => ":timed-initial-literals",
            Requirement::Preferences => ":preferences",
            Requirement::Constraints => ":constraints",
            Requirement::ActionCosts => ":action-costs",
        }
    }
}

impl fmt::Display for Requirement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn can_add_requirements() {
        let mut r = Reqs::default();

        r.add(Requirement::ConditionalEffects);
        r.add(Requirement::UniversalPreconditions);
        r.add(Requirement::Preferences);
        r.add(Requirement::Typing);

        assert!(r.has(Requirement::ConditionalEffects));
        assert!(r.has(Requirement::UniversalPreconditions));
        assert!(r.has(Requirement::Preferences));
        assert!(r.has(Requirement::Typing));
    }
}
