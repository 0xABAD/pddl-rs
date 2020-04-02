use std::collections::HashSet;

pub type TypeId = usize;

type TypeSet = HashSet<TypeId>;
type TypeMap = Vec<TypeSet>;

/// `Types` is the collection of all types found from `:types` section
/// within a PDDL domain.
#[derive(Debug)]
pub struct Types {
    // Type names where the index into the vector is the TypeId for
    // the type.  Previously a HashMap was used but with a small number
    // of types (i.e. 12), which is typically the case, the vector lookup
    // out performed the HashMap by 10 to 20% in the worst case where
    // the item being searched was the last string in the vector.
    types: Vec<String>,

    type_id: TypeId,    // A TypeId counter.
    children: TypeMap,  // Immediate child TypeIds.  Vector is indexed by the parent TypeId.
    parents: TypeMap,   // Immediate parent TypeIds.  Vector is indexed by the child TypeId.
}

impl Default for Types {
    fn default() -> Self {
        Types {
            type_id: 0,
            types: vec![],
            parents: vec![],
            children: vec![],
        }
    }
}

impl Types {
    /// `get` returns the `TypeId` of the lowercase form of `name`
    /// if it exists.
    pub fn get(&self, name: &str) -> Option<TypeId> {
        for i in 0..self.types.len() {
            let s = &self.types[i];
            if name.eq_ignore_ascii_case(s) {
                return Some(i);
            }
        }
        None
    }

    /// `name_of` returns the type name for of the given `id`.
    pub fn name_of(&self, id: TypeId) -> &str {
        &self.types[id]
    }

    /// `insert` inserts `s` and assigns it a `TypeId` if it hasn't already
    /// been seen.
    pub fn insert(&mut self, s: &str) -> TypeId {
        if let Some(id) = self.get(s) {
            id
        } else {
            let tid = self.type_id;
            self.types.push(s.to_string());
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
        self.is_child_an_ancestor_of(id, id)
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
        assert!(!t.is_child_an_ancestor_of(bar, baz));
        assert!(!t.is_child_an_ancestor_of(baz, bar));
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
