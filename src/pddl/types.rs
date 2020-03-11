use std::collections::{HashMap, HashSet};

pub type TypeId = usize;

type TypeSet = HashSet<TypeId>;
type TypeMap = Vec<TypeSet>;

/// `Types` is the collection of all types found from `:types` section
/// within a PDDL domain.
#[derive(Debug)]
pub struct Types {
    types: HashMap<String, TypeId>, // Lowercased type names to their assigned TypeId.
    children: TypeMap, // Immediate child TypeIds.  Vector is indexed by the parent TypeId.
    parents: TypeMap,  // Immediate parent TypeIds.  Vector is indexed by the child TypeId.
    type_id: TypeId,   // A TypeId counter.
}

impl Default for Types {
    fn default() -> Self {
        Types {
            types: HashMap::new(),
            type_id: 0,
            parents: vec![],
            children: vec![],
        }
    }
}

impl Types {
    /// `get` returns the `TypeId` of the lowercase form of `name`
    /// if it exists.
    pub fn get(&self, name: &str) -> Option<TypeId> {
        let n = name.to_ascii_lowercase();
        self.types.get(&n).map(|&id| id)
    }

    /// `insert` inserts `s` and assigns it a `TypeId` if it hasn't already
    /// been seen.
    pub fn insert(&mut self, s: &str) -> TypeId {
        let id = s.to_ascii_lowercase();
        if self.types.contains_key(&id) {
            *self.types.get(&id).unwrap()
        } else {
            let tid = self.type_id;
            self.types.insert(id, tid);
            self.type_id += 1;
            self.parents.push(TypeSet::new());
            self.children.push(TypeSet::new());
            tid
        }
    }

    /// `relate` creates a relationship where `child` is one of `parent`'s children
    /// and `parent` is one of `child`'s parents.
    pub fn relate(&mut self, child: TypeId, parent: TypeId) {
        self.parents[child].insert(parent);
        self.children[parent].insert(child);
    }

    /// `is_child_an_ancestor_of` returns true if `child` is an ancestor of `parent`.
    pub fn is_child_an_ancestor_of(&self, child: TypeId, parent: TypeId) -> bool {
        let ct = &self.children[parent];
        if ct.contains(&child) {
            true
        } else {
            for &id in ct.iter() {
                if self.is_child_an_ancestor_of(child, id) {
                    return true;
                }
            }
            false
        }
    }

    /// `has_circular_types` returns true if `id` ends up inheriting from itself.
    pub fn has_circular_types(&self, id: TypeId) -> bool {
        let pt = &self.parents[id];
        if pt.contains(&id) {
            true
        } else {
            for &pid in pt.iter() {
                if self.check_circular_parent(id, pid, pt) {
                    return true;
                }
            }
            false
        }
    }

    /// `check_circular_parent` is a helper function for `has_circular_types`.
    /// `original` should be the first `TypeSet` that was checked in
    /// `has_circular_types` and is needed when a child doesn't have a circular
    /// reference but one of its parents has a circular reference of there
    /// own.
    fn check_circular_parent(&self, child: TypeId, parent: TypeId, original: &TypeSet) -> bool {
        let pt = &self.parents[parent];
        if pt == original {
            false
        } else if pt.contains(&child) {
            true
        } else {
            for &pid in pt.iter() {
                if self.check_circular_parent(child, pid, original) {
                    return true;
                }
            }
            false
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn insert_and_get() {
        let mut t = Types::default();

        let foo = t.insert("Foo");
        let bar = t.insert("bar");

        assert_eq!(t.get("FOO"), Some(foo));
        assert_eq!(t.get("BAR"), Some(bar));
    }

    #[test]
    fn can_relate() {
        let mut t = Types::default();

        let foo = t.insert("Foo");
        let bar = t.insert("bar");
        let baz = t.insert("baz");

        t.relate(bar, foo);
        t.relate(baz, foo);

        assert!(t.is_child_an_ancestor_of(bar, foo));
        assert!(t.is_child_an_ancestor_of(baz, foo));
        assert!(!t.is_child_an_ancestor_of(foo, bar));
        assert!(!t.is_child_an_ancestor_of(foo, baz));
    }

    #[test]
    fn can_relate_grandchildren() {
        let mut t = Types::default();

        let foo = t.insert("Foo");
        let bar = t.insert("bar");
        let baz = t.insert("baz");

        t.relate(bar, foo);
        t.relate(baz, bar);

        assert!(t.is_child_an_ancestor_of(bar, foo));
        assert!(t.is_child_an_ancestor_of(baz, bar));
        assert!(t.is_child_an_ancestor_of(baz, foo));
        assert!(!t.is_child_an_ancestor_of(foo, bar));
        assert!(!t.is_child_an_ancestor_of(foo, baz));
        assert!(!t.is_child_an_ancestor_of(bar, baz));
    }

    #[test]
    fn detects_circular_types() {
        let mut t = Types::default();

        let foo = t.insert("Foo");
        let bar = t.insert("bar");
        let baz = t.insert("baz");
        let quux = t.insert("quux");

        t.relate(bar, foo);
        t.relate(baz, bar);
        t.relate(foo, baz);
        t.relate(quux, foo);

        assert!(t.has_circular_types(foo));
        assert!(t.has_circular_types(bar));
        assert!(t.has_circular_types(baz));
        assert!(!t.has_circular_types(quux));
    }
}
