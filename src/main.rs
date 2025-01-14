use std::collections::{HashMap, VecDeque};

// x, y, mが与えられたとき、m<=lcm(x, y)ならa, b>=0, ax+by=mを満たすa, bが存在すれば一意
// a, b <= sizeに対して、(a, b)を作るのに必要な最小手数を計算
#[derive(Clone, Debug)]
struct TerminalTable {
    size: usize,
    table: Vec<Vec<usize>>,
}

impl TerminalTable {
    fn new(size: usize) -> Self {
        let mut table = vec![vec![usize::MAX; size]; size];

        let mut queue = VecDeque::new();
        queue.push_back((0, 1));
        queue.push_back((1, 0));
        table[0][1] = 1;
        table[1][0] = 1;

        let check_and_push = |a: usize,
                              b: usize,
                              table: &mut Vec<Vec<usize>>,
                              queue: &mut VecDeque<(usize, usize)>,
                              next_cost: usize| {
            if a < size && b < size && next_cost < table[a][b] {
                table[a][b] = next_cost;
                queue.push_back((a, b));
            }
        };

        while let Some((a, b)) = queue.pop_front() {
            let next_cost = table[a][b] + 1;
            check_and_push(2 * a, b, &mut table, &mut queue, next_cost);
            check_and_push(a, 2 * b, &mut table, &mut queue, next_cost);
            check_and_push(a + b, b, &mut table, &mut queue, next_cost);
            check_and_push(a, a + b, &mut table, &mut queue, next_cost);
        }

        Self { size, table }
    }

    fn get(&self, state: &SearchState) -> Option<usize> {
        match state {
            SearchState::Terminal { a, b } => {
                if a >= &self.size || b >= &self.size {
                    None
                } else {
                    Some(self.table[*a][*b])
                }
            }
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum SearchState {
    Primal { x: usize, y: usize },
    Terminal { a: usize, b: usize },
}

impl SearchState {
    fn normalize(&self) -> Self {
        match self {
            SearchState::Primal { x, y } => {
                if x >= y {
                    SearchState::Primal { x: *x, y: *y }
                } else {
                    SearchState::Primal { x: *y, y: *x }
                }
            }
            SearchState::Terminal { a, b } => {
                if a >= b {
                    SearchState::Terminal { a: *a, b: *b }
                } else {
                    SearchState::Terminal { a: *b, b: *a }
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
struct Solver {
    terminal_table: TerminalTable,
    m: usize,
}

impl Solver {
    fn new(terminal_table_size: usize, m: usize) -> Self {
        Self {
            terminal_table: TerminalTable::new(terminal_table_size),
            m,
        }
    }

    fn gcd_trailing(x: usize, y: usize) -> u32 {
        (x | y).trailing_zeros()
    }

    fn mod_inv(x: usize, m: usize) -> usize {
        let mut a = x as i64;
        let mut b = m as i64;
        let mut u = 1;
        let mut v = 0;
        while b != 0 {
            let t = a / b;
            a -= t * b;
            u -= t * v;
            std::mem::swap(&mut a, &mut b);
            std::mem::swap(&mut u, &mut v);
        }
        u %= m as i64;
        if u < 0 {
            u += m as i64;
        }
        u as usize
    }

    fn crt(x: usize, y: usize, m: usize) -> Option<(usize, usize)> {
        let x_inv = Self::mod_inv(x, y);
        let a = (m * x_inv) % y;
        let ax = a * x;
        if ax > m {
            return None;
        }
        let b = (m - ax) / y;
        Some((a, b))
    }

    fn check_and_push(
        parent_state: &SearchState,
        state: SearchState,
        cost: usize,
        cost_table: &mut HashMap<SearchState, (usize, Option<SearchState>)>,
        queue: &mut VecDeque<SearchState>,
    ) {
        let state = state.normalize();
        if !cost_table.contains_key(&state) {
            cost_table.insert(state.clone(), (cost, Some(parent_state.clone())));
            queue.push_back(state);
        }
    }

    fn solve(&mut self, initial_state: SearchState) -> Option<(usize, Vec<SearchState>)> {
        let mut queue = VecDeque::new();
        queue.push_back(initial_state.clone());
        let mut cost_table = HashMap::new();
        cost_table.insert(initial_state, (0, None));

        let m_tail = self.m.trailing_zeros();
        let mut min_cost = usize::MAX;
        let mut min_state = None;

        while let Some(state) = queue.pop_front() {
            let cost = cost_table[&state].0 + 1;
            let next_cost = cost + 1;

            if next_cost >= min_cost {
                break;
            }

            match state {
                SearchState::Primal { x, y } => {
                    let lcm = x * y >> Self::gcd_trailing(x, y);
                    if lcm > self.m {
                        if let Some((a, b)) = Self::crt(x, y, self.m) {
                            let next_state = SearchState::Terminal { a, b };
                            Self::check_and_push(
                                &state,
                                next_state,
                                cost,
                                &mut cost_table,
                                &mut queue,
                            );
                        }
                        continue;
                    }
                    if m_tail <= Self::gcd_trailing(2 * x, y) {
                        Self::check_and_push(
                            &state,
                            SearchState::Primal { x: 2 * x, y },
                            next_cost,
                            &mut cost_table,
                            &mut queue,
                        );
                    }
                    if m_tail <= Self::gcd_trailing(x, 2 * y) {
                        Self::check_and_push(
                            &state,
                            SearchState::Primal { x, y: 2 * y },
                            next_cost,
                            &mut cost_table,
                            &mut queue,
                        );
                    }
                    Self::check_and_push(
                        &state,
                        SearchState::Primal { x: x + y, y },
                        next_cost,
                        &mut cost_table,
                        &mut queue,
                    );
                    Self::check_and_push(
                        &state,
                        SearchState::Primal { x, y: x + y },
                        next_cost,
                        &mut cost_table,
                        &mut queue,
                    );
                }
                SearchState::Terminal { a, b } => {
                    if let Some(terminal_cost) = self.terminal_table.get(&state) {
                        let total_cost = cost + terminal_cost;
                        if total_cost < min_cost {
                            min_cost = total_cost;
                            min_state = Some(state.clone());
                        }
                        continue;
                    }
                    if a % 2 == 0 {
                        Self::check_and_push(
                            &state,
                            SearchState::Terminal { a: a / 2, b },
                            next_cost,
                            &mut cost_table,
                            &mut queue,
                        );
                    }
                    if b % 2 == 0 {
                        Self::check_and_push(
                            &state,
                            SearchState::Terminal { a, b: b / 2 },
                            next_cost,
                            &mut cost_table,
                            &mut queue,
                        );
                    }
                    if a >= b {
                        Self::check_and_push(
                            &state,
                            SearchState::Terminal { a: a - b, b },
                            next_cost,
                            &mut cost_table,
                            &mut queue,
                        );
                    } else {
                        Self::check_and_push(
                            &state,
                            SearchState::Terminal { a, b: b - a },
                            next_cost,
                            &mut cost_table,
                            &mut queue,
                        );
                    }
                }
            }
        }

        let mut state = &min_state?;
        let mut path = vec![state.clone()];
        while let (_, Some(parent_state)) = cost_table.get(state).unwrap() {
            state = parent_state;
            path.push(state.clone());
        }

        Some((min_cost, path))
    }
}

fn main() {
    const TERMINAL_TABLE_SIZE: usize = 10000;
    let mut solver = Solver::new(TERMINAL_TABLE_SIZE, 998244353);
    let initial_state = SearchState::Primal { x: 1, y: 1 };
    let (cost, path) = solver.solve(initial_state).unwrap();
    println!("cost: {}", cost);
    for state in path.iter().rev() {
        println!("{:?}", state);
    }
}
