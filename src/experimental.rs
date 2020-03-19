use std::{
    cell::RefCell,
    collections::{HashMap, VecDeque},
    fmt::{self, Write},
    iter::Iterator,
    rc::{Rc, Weak},
};

type PredPtr = Rc<RefCell<Pred>>;
type ActionPtr = Rc<RefCell<Action>>;
type State = Vec<PredPtr>;

#[derive(Debug)]
pub struct Action {
    pub name: String,
    pub params: Vec<Obj>,
    pub pre: Vec<PredPtr>,
    pub adds: Vec<PredPtr>,
    pub dels: Vec<PredPtr>,
}

impl Action {
    pub fn to_pddl(&self) -> Result<String, Box<dyn std::error::Error>> {
        let mut s = String::new();

        write!(&mut s, "(:action {}\n :parameters (", self.name)?;
        for p in &self.params {
            write!(&mut s, " {}", p)?;
        }

        write!(&mut s, " ) \n :precondition\n  (and")?;
        for p in &self.pre {
            write!(&mut s, "\n   {}", p.borrow())?;
        }

        write!(&mut s, ")\n  :effect\n  (and")?;
        for a in &self.adds {
            write!(&mut s, "\n   {}", a.borrow())?;
        }

        for d in &self.dels {
            write!(&mut s, "\n   (not {})", d.borrow())?;
        }
        write!(&mut s, "))")?;

        Ok(s)
    }
}

impl fmt::Display for Action {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}", self.name)?;
        for p in &self.params {
            write!(f, " {}", p)?;
        }
        write!(f, ")")
    }
}

#[derive(Debug)]
pub struct Pred {
    pub name: String,
    pub terms: Vec<Obj>,
    pub actions: Vec<Weak<RefCell<Action>>>,
    pub result: bool,
}

impl fmt::Display for Pred {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}", self.name)?;
        for t in &self.terms {
            write!(f, " {}", t)?;
        }
        write!(f, ")")
    }
}

#[derive(Debug, Clone)]
pub struct Obj(String);

pub fn obj(s: &str) -> Obj {
    Obj(s.to_string())
}

impl fmt::Display for Obj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

fn main() {
    let mut facts: HashMap<String, PredPtr> = HashMap::new();
    let objs = vec![obj("a"), obj("b"), obj("c")];//, obj("d")];

    facts.insert(
        "(hand-empty)".to_string(),
        Rc::new(RefCell::new(Pred {
            name: "hand-empty".to_string(),
            terms: vec![],
            actions: vec![],
            result: false,
        })),
    );

    for a in &objs {
        let p = Pred {
            name: "on-table".to_string(),
            terms: vec![a.clone()],
            actions: vec![],
            result: false,
        };
        facts.insert(format!("{}", p), Rc::new(RefCell::new(p)));

        let p = Pred {
            name: "clear".to_string(),
            terms: vec![a.clone()],
            actions: vec![],
            result: false,
        };
        facts.insert(format!("{}", p), Rc::new(RefCell::new(p)));

        let p = Pred {
            name: "holding".to_string(),
            terms: vec![a.clone()],
            actions: vec![],
            result: false,
        };
        facts.insert(format!("{}", p), Rc::new(RefCell::new(p)));

        for b in &objs {
            let p = Pred {
                name: "on".to_string(),
                terms: vec![a.clone(), b.clone()],
                actions: vec![],
                result: false,
            };
            facts.insert(format!("{}", p), Rc::new(RefCell::new(p)));
        }
    }

    let mut actions: HashMap<String, ActionPtr> = HashMap::new();

    for x in &objs {
        let pick_up = Rc::new(RefCell::new(Action {
            name: "pick-up".to_string(),
            params: vec![x.clone()],
            pre: vec![],
            adds: vec![],
            dels: vec![],
        }));

        let put_down = Rc::new(RefCell::new(Action {
            name: "put-down".to_string(),
            params: vec![x.clone()],
            pre: vec![],
            adds: vec![],
            dels: vec![],
        }));

        let key = format!("({} {})", pick_up.borrow().name, x);
        actions.insert(key, pick_up.clone());

        let key = format!("({} {})", put_down.borrow().name, x);
        actions.insert(key, put_down.clone());

        if let Some(p) = facts.get("(hand-empty)") {
            p.borrow_mut().actions.push(Rc::downgrade(&pick_up));
            pick_up.borrow_mut().pre.push(p.clone());
            pick_up.borrow_mut().dels.push(p.clone());

            p.borrow_mut().actions.push(Rc::downgrade(&put_down));
            put_down.borrow_mut().adds.push(p.clone());
        }

        let key = format!("(on-table {})", x);
        if let Some(p) = facts.get(&key) {
            p.borrow_mut().actions.push(Rc::downgrade(&pick_up));
            pick_up.borrow_mut().pre.push(p.clone());
            pick_up.borrow_mut().dels.push(p.clone());

            p.borrow_mut().actions.push(Rc::downgrade(&put_down));
            put_down.borrow_mut().adds.push(p.clone());
        }

        let key = format!("(clear {})", x);
        if let Some(p) = facts.get(&key) {
            p.borrow_mut().actions.push(Rc::downgrade(&pick_up));
            pick_up.borrow_mut().pre.push(p.clone());
            pick_up.borrow_mut().dels.push(p.clone());

            p.borrow_mut().actions.push(Rc::downgrade(&put_down));
            put_down.borrow_mut().adds.push(p.clone());
        }

        let key = format!("(holding {})", x);
        if let Some(p) = facts.get(&key) {
            p.borrow_mut().actions.push(Rc::downgrade(&pick_up));
            pick_up.borrow_mut().adds.push(p.clone());

            p.borrow_mut().actions.push(Rc::downgrade(&put_down));
            put_down.borrow_mut().pre.push(p.clone());
            put_down.borrow_mut().dels.push(p.clone());
        }

        for y in &objs {
            let unstack = Rc::new(RefCell::new(Action {
                name: "unstack".to_string(),
                params: vec![x.clone(), y.clone()],
                pre: vec![],
                adds: vec![],
                dels: vec![],
            }));

            let stack = Rc::new(RefCell::new(Action {
                name: "stack".to_string(),
                params: vec![x.clone(), y.clone()],
                pre: vec![],
                adds: vec![],
                dels: vec![],
            }));

            let key = format!("({} {} {})", unstack.borrow().name, x, y);
            actions.insert(key, unstack.clone());

            let key = format!("({} {} {})", stack.borrow().name, x, y);
            actions.insert(key, stack.clone());

            if let Some(p) = facts.get("(hand-empty)") {
                p.borrow_mut().actions.push(Rc::downgrade(&unstack));
                unstack.borrow_mut().pre.push(p.clone());
                unstack.borrow_mut().dels.push(p.clone());

                p.borrow_mut().actions.push(Rc::downgrade(&stack));
                stack.borrow_mut().adds.push(p.clone());
            }

            let key = format!("(clear {})", x);
            if let Some(p) = facts.get(&key) {
                p.borrow_mut().actions.push(Rc::downgrade(&unstack));
                unstack.borrow_mut().pre.push(p.clone());
                unstack.borrow_mut().dels.push(p.clone());

                p.borrow_mut().actions.push(Rc::downgrade(&stack));
                stack.borrow_mut().adds.push(p.clone());
            }

            let key = format!("(clear {})", y);
            if let Some(p) = facts.get(&key) {
                p.borrow_mut().actions.push(Rc::downgrade(&unstack));
                unstack.borrow_mut().adds.push(p.clone());

                p.borrow_mut().actions.push(Rc::downgrade(&stack));
                stack.borrow_mut().pre.push(p.clone());
                stack.borrow_mut().dels.push(p.clone());
            }

            let key = format!("(holding {})", x);
            if let Some(p) = facts.get(&key) {
                p.borrow_mut().actions.push(Rc::downgrade(&unstack));
                unstack.borrow_mut().adds.push(p.clone());

                p.borrow_mut().actions.push(Rc::downgrade(&stack));
                stack.borrow_mut().pre.push(p.clone());
                stack.borrow_mut().dels.push(p.clone());
            }

            let key = format!("(on {} {})", x, y);
            if let Some(p) = facts.get(&key) {
                p.borrow_mut().actions.push(Rc::downgrade(&unstack));
                unstack.borrow_mut().pre.push(p.clone());
                unstack.borrow_mut().dels.push(p.clone());

                p.borrow_mut().actions.push(Rc::downgrade(&stack));
                stack.borrow_mut().adds.push(p.clone());
            }
        }
    }

    let inits = &[
        "(on a b)",
        "(on b c)",
        "(on-table c)",
        // "(on-table d)",
        "(clear a)",
        // "(clear d)",
        "(hand-empty)",
    ];

    let goals = &[
        "(hand-empty)",
        "(on-table a)",
        // "(on d c)",
        "(on c b)",
        "(on b a)",
        // "(clear d)",
    ];

    let mut init: Vec<PredPtr> = vec![];
    let mut goal: Vec<PredPtr> = vec![];

    for &s in inits {
        if let Some(p) = facts.get(s) {
            p.borrow_mut().result = true;
            init.push(p.clone());
        }
    }

    for &g in goals {
        if let Some(p) = facts.get(g) {
            goal.push(p.clone());
        }
    }

    println!("================");
    println!("      Goal      ");
    println!("================");
    for p in &goal {
        println!("{}", p.borrow());
    }
    println!();

    println!("================");
    println!("      Init      ");
    println!("================");
    for p in &init {
        println!("{}", p.borrow());
    }
    println!();

    let (states, action_states) = rpg(&init, &goal);
    let level = states.len() - 1;

    if !is_subset(&goal, &states[level]) {
        println!("Goal is impossible");
        return;
    }

    let a_tot = rp_extract(&goal, &states, &action_states);
    let mut huer: usize = a_tot.iter().map(|a| a.len()).sum();

    println!("LEVEL {} (H = {})\n", level, huer);

    let mut count = 0;
    let mut open = VecDeque::new();

    let init_state = SearchState::new(&init, &a_tot[a_tot.len() - 1], &facts);
    open.push_back(init_state);

    'ehc: while !open.is_empty() {
        let ss = open.pop_front().unwrap();

        for (state, action) in ss {
            if is_subset(&goal, &state) {
                println!("PLAN FOUND! ==> {}", action.borrow());
                break 'ehc;
            }

            let hs = hueristic(&state, &goal);
            let n: usize = hs.iter().map(|a| a.len()).sum();

            println!("ACTION: {} - {}", action.borrow(), n);
            // println!("======> STATE <=======");
            // for s in &state {
            //     println!("{}", s.borrow());
            // }
            // println!();

            // println!("======> OTHERS <=======");
            // let actions = &hs[hs.len() - 1];
            // for a in actions {
            //     println!("{}", a.borrow());
            // }
            // println!();

            // println!("======> H(s) <=======");
            // for i in 0..hs.len() {
            //     let actions = &hs[i];                
            //     println!("   >>   A {}   <<", i);
            //     for a in actions {
            //         println!("{}", a.borrow());
            //     }
            // }
            // println!();

            count += 1;
            if count > 18 {
                break 'ehc;
            }

            if n < huer {
                huer = n;
                println!("H = {}, {}", huer, action.borrow());
                open.clear();
                open.push_back(SearchState::new(&state, &hs[hs.len() - 1], &facts));
                continue 'ehc;
            } else {
                open.push_back(SearchState::new(&state, &hs[hs.len() - 1], &facts));
            }
        }
    }

    println!("==========> Plan <===========");
}

pub fn hueristic(state: &State, goal: &State) -> Vec<Vec<ActionPtr>> {
    let (states, action_states) = rpg(state, goal);
    rp_extract(goal, &states, &action_states)
}

pub struct SearchState<'a> {
    state: State,
    actions: Vec<ActionPtr>,
    facts: &'a HashMap<String, PredPtr>,
    index: usize,
}

impl<'a> SearchState<'a> {
    pub fn new(
        init: &State,
        actions: &Vec<ActionPtr>,
        facts: &'a HashMap<String, PredPtr>,
    ) -> Self {
        let ss = SearchState {
            index: 0,
            state: init.clone(),
            actions: actions.clone(),
            facts,
        };
        ss
    }

    fn apply(&self, action: &ActionPtr) -> State {
        let mut result = self.state.clone();

        'adds: for p0 in &action.borrow().adds {
            p0.borrow_mut().result = true;
            for p1 in &result {
                if Rc::ptr_eq(&p0, &p1) {
                    continue 'adds;
                }
            }
            result.push(p0.clone());
        }
        for p0 in &action.borrow().dels {
            p0.borrow_mut().result = false;
        }

        let mut state = vec![];
        for p0 in &result {
            if p0.borrow().result {
                state.push(p0.clone());
            }
        }
        state
    }
}

impl Iterator for SearchState<'_> {
    type Item = (State, ActionPtr);

    fn next(&mut self) -> Option<Self::Item> {
        if self.index == self.actions.len() {
            return None;
        }
        rebase(&self.facts, &self.state);

        let action = &self.actions[self.index];

        self.index += 1;
        Some((self.apply(action), action.clone()))
    }
}

pub fn rebase(facts: &HashMap<String, PredPtr>, state: &State) {
    reset(facts);
    establish(state);
}

pub fn establish(state: &State) {
    for s in state {
        s.borrow_mut().result = true;
    }
}

pub fn reset(facts: &HashMap<String, PredPtr>) {
    for (_, f) in facts {
        f.borrow_mut().result = false;
    }
}

pub fn rpg(init: &State, goal: &State) -> (Vec<State>, Vec<Vec<ActionPtr>>) {
    let mut level = 0;
    let mut states: Vec<State> = vec![vec![]];
    let mut action_states: Vec<Vec<ActionPtr>> = vec![vec![]];

    for p in init {
        states[level].push(p.clone());
    }

    while !is_subset(&goal, &states[level]) {
        if level > 0 {
            let this = &states[level];
            let prev = &states[level - 1];

            if is_subset(this, prev) && is_subset(prev, this) {
                break;
            }
        }

        for p in &states[level] {
            'action: for act in &p.borrow().actions {
                if let Some(a) = act.upgrade() {
                    let mut all = true;
                    for pre in &a.borrow().pre {
                        all = all && pre.borrow().result;
                    }
                    if all {
                        for action in &action_states[level] {
                            if Rc::ptr_eq(&action, &a) {
                                continue 'action;
                            }
                        }
                        action_states[level].push(a.clone());
                    }
                }
            }
        }

        let mut next = vec![];
        for s in &states[level] {
            next.push(s.clone());
        }
        states.push(next);
        action_states.push(vec![]);
        level += 1;

        for a in &action_states[level - 1] {
            'preds: for add in &a.borrow().adds {
                for s in &states[level] {
                    if Rc::ptr_eq(&s, &add) {
                        continue 'preds;
                    }
                }
                add.borrow_mut().result = true;
                states[level].push(add.clone());
            }
        }
    }

    (states, action_states)
}

pub fn rp_extract(
    goal: &State,
    states: &Vec<State>,
    action_states: &Vec<Vec<ActionPtr>>,
) -> Vec<Vec<ActionPtr>> {
    let level = states.len() - 1;
    let mut g_tot = vec![goal.clone()];
    let mut g_new = vec![];
    let mut a_tot = vec![];

    for i in 0..level {
        let n = level - i;
        let s_diff = set_diff(&states[n], &states[n - 1]);
        let last_goal = &g_tot[g_tot.len() - 1];
        let g_next = intersection(&last_goal, &s_diff);
        let mut g_prev = set_diff(&last_goal, &g_next);

        let mut a_next = vec![];
        let mut skip: State = vec![];
        for a in &action_states[n - 1] {
            if skip.len() == g_next.len() {
                break;
            }
            'adds: for p in &a.borrow().adds {
                for s in &skip {
                    if Rc::ptr_eq(&p, &s) {
                        continue 'adds;
                    }
                }
                for g in &g_next {
                    if Rc::ptr_eq(&p, &g) {
                        skip.push(g.clone());
                        for an in &a_next {
                            if Rc::ptr_eq(&a, &an) {
                                continue 'adds;
                            }
                        }
                        a_next.push(a.clone());
                    }
                }
            }
        }

        for a in &a_next {
            g_prev = union(&g_prev, &a.borrow().pre);
        }
        a_tot.push(a_next);
        g_tot.push(g_prev);
        g_new.push(g_next);
    }

    a_tot
}

pub fn print_plan_graph(states: &Vec<State>, actions: &Vec<Vec<ActionPtr>>) {
    for i in 0..states.len() {
        println!("====================");
        println!("         s{}", i);
        println!("====================");

        for s in &states[i] {
            println!("{}", s.borrow());
        }
        println!();

        if i < actions.len() - 1 {
            println!("====================");
            println!("         a{}", i);
            println!("====================");
            for a in &actions[i] {
                println!("{}", a.borrow());
            }
            println!();
        }
    }
}

pub fn is_subset(left: &State, right: &State) -> bool {
    'top: for p0 in left {
        for p1 in right {
            if Rc::ptr_eq(p0, p1) {
                continue 'top;
            }
        }
        return false;
    }
    true
}

pub fn set_diff(left: &State, right: &State) -> State {
    let mut result = vec![];
    'top: for p0 in left {
        for p1 in right {
            if Rc::ptr_eq(p0, p1) {
                continue 'top;
            }
        }
        result.push(p0.clone());
    }
    result
}

pub fn intersection(left: &State, right: &State) -> State {
    let mut result = vec![];
    'top: for p0 in left {
        for p1 in right {
            if Rc::ptr_eq(p0, p1) {
                result.push(p0.clone());
                continue 'top;
            }
        }
    }
    result
}

pub fn union(left: &State, right: &State) -> State {
    let mut result = vec![];
    'top_left: for p0 in left {
        for p1 in &result {
            if Rc::ptr_eq(p0, p1) {
                continue 'top_left;
            }
        }
        result.push(p0.clone());
    }
    'top_right: for p0 in right {
        for p1 in &result {
            if Rc::ptr_eq(p0, p1) {
                continue 'top_right;
            }
        }
        result.push(p0.clone());
    }
    result
}
