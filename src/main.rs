use rustc_hash::FxHashMap as HashMap;
use std::collections::hash_map::Entry::Vacant;
use std::collections::VecDeque;

#[derive(Clone, Debug)]
enum MulOperation {
    ToXyY,
    ToXYx,
    To2XY,
    ToX2Y,
    Identity,
    PrimalToTerminal,
}

// x, y, mが与えられたとき、m<=lcm(x, y)ならa, b>=0, ax+by=mを満たすa, bが存在すれば一意
// a, b <= sizeに対して、(a, b)を作るのに必要な最小手数を計算
#[derive(Clone, Debug)]
struct TerminalTable {
    size: usize,
    table: Vec<Vec<usize>>,
    op_table: Vec<Vec<MulOperation>>,
}

impl TerminalTable {
    fn new(size: usize) -> Self {
        let mut table = vec![vec![usize::MAX / 2; size]; size];
        let mut op_table = vec![vec![MulOperation::Identity; size]; size];

        let mut queue = VecDeque::new();
        queue.push_back((0, 1));
        queue.push_back((1, 0));
        table[0][1] = 0;
        table[1][0] = 0;

        while let Some((a, b)) = queue.pop_front() {
            let next_cost = table[a][b] + 1;
            Self::check_and_push(
                2 * a,
                b,
                &mut table,
                &mut op_table,
                &mut queue,
                next_cost,
                MulOperation::To2XY,
            );
            Self::check_and_push(
                a,
                2 * b,
                &mut table,
                &mut op_table,
                &mut queue,
                next_cost,
                MulOperation::ToX2Y,
            );
            Self::check_and_push(
                a + b,
                b,
                &mut table,
                &mut op_table,
                &mut queue,
                next_cost,
                MulOperation::ToXYx,
            );
            Self::check_and_push(
                a,
                a + b,
                &mut table,
                &mut op_table,
                &mut queue,
                next_cost,
                MulOperation::ToXyY,
            );
        }

        Self {
            size,
            table,
            op_table,
        }
    }

    fn check_and_push(
        a: usize,
        b: usize,
        table: &mut Vec<Vec<usize>>,
        op_table: &mut Vec<Vec<MulOperation>>,
        queue: &mut VecDeque<(usize, usize)>,
        next_cost: usize,
        op: MulOperation,
    ) {
        if a < table.len() && b < table.len() && next_cost < table[a][b] {
            table[a][b] = next_cost;
            op_table[a][b] = op;
            queue.push_back((a, b));
        }
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

    fn get_op(&self, state: &SearchState) -> Option<MulOperation> {
        match state {
            SearchState::Terminal { a, b } => {
                if a >= &self.size || b >= &self.size {
                    None
                } else {
                    Some(self.op_table[*a][*b].clone())
                }
            }
            _ => None,
        }
    }

    fn get_path(&self, state: &SearchState) -> Option<Vec<MulOperation>> {
        let mut state = state.clone();
        let mut path = vec![];
        while let Some(op) = self.get_op(&state) {
            if let MulOperation::Identity = op {
                break;
            }
            state = state.apply(&op);
            path.push(op);
        }
        path.reverse();
        Some(path)
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum SearchState {
    Primal { x: usize, y: usize },
    Terminal { a: usize, b: usize },
}

impl SearchState {
    fn normalize_to_sorted(&self) -> Self {
        match self {
            SearchState::Primal { x, y } => {
                let (x, y) = if x >= y { (*x, *y) } else { (*y, *x) };
                SearchState::Primal { x, y }
            }
            SearchState::Terminal { a, b } => {
                let (a, b) = if a >= b { (*a, *b) } else { (*b, *a) };
                SearchState::Terminal { a, b }
            }
        }
    }

    fn apply_operation<F, G>(&self, primal_func: F, terminal_func: G) -> Self
    where
        F: Fn(usize, usize) -> (usize, usize),
        G: Fn(usize, usize) -> (usize, usize),
    {
        match self {
            SearchState::Primal { x, y } => {
                let (x, y) = primal_func(*x, *y);
                SearchState::Primal { x, y }
            }
            SearchState::Terminal { a, b } => {
                let (a, b) = terminal_func(*a, *b);
                SearchState::Terminal { a, b }
            }
        }
    }

    fn apply(&self, op: &MulOperation) -> Self {
        match op {
            MulOperation::To2XY => self.apply_operation(|x, y| (2 * x, y), |a, b| (a / 2, b)),
            MulOperation::ToX2Y => self.apply_operation(|x, y| (x, 2 * y), |a, b| (a, b / 2)),
            MulOperation::ToXYx => self.apply_operation(|x, y| (x, y + x), |a, b| (a - b, b)),
            MulOperation::ToXyY => self.apply_operation(|x, y| (x + y, y), |a, b| (a, b - a)),
            _ => self.clone(),
        }
    }

    fn inverse(&self, op: &MulOperation) -> Self {
        match op {
            MulOperation::To2XY => self.apply_operation(|x, y| (x / 2, y), |a, b| (2 * a, b)),
            MulOperation::ToX2Y => self.apply_operation(|x, y| (x, y / 2), |a, b| (a, 2 * b)),
            MulOperation::ToXYx => self.apply_operation(|x, y| (x, y - x), |a, b| (a + b, b)),
            MulOperation::ToXyY => self.apply_operation(|x, y| (x - y, y), |a, b| (a, a + b)),
            _ => self.clone(),
        }
    }
}

#[derive(Clone, Debug)]
struct Solver {
    terminal_table: TerminalTable,
}

impl Solver {
    fn new(terminal_table_size: usize) -> Self {
        Self {
            terminal_table: TerminalTable::new(terminal_table_size),
        }
    }

    fn gcd_trailing(x: usize, y: usize) -> u32 {
        (x | y).trailing_zeros()
    }

    fn log2(x: usize) -> u32 {
        64 - x.leading_zeros()
    }

    fn mod_inv(x: usize, m: usize) -> Result<usize, String> {
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

        if a != 1 {
            return Err(format!("{} is not invertible modulo {}", x, m));
        }

        u %= m as i64;
        if u < 0 {
            u += m as i64;
        }
        Ok(u as usize)
    }

    fn crt(x: usize, y: usize, m: usize) -> Result<(usize, usize), String> {
        let gcd = Self::gcd_trailing(x, y);
        let x = x >> gcd;
        let y = y >> gcd;
        let m = m >> gcd;
        let x_inv = Self::mod_inv(x, y)?;
        let a = (m * x_inv) % y;
        let ax = a * x;
        if ax > m {
            return Err(format!("No non-negative solution for {}x+{}y={}", x, y, m));
        }
        let b = (m - ax) / y;
        Ok((a, b))
    }

    fn check_and_push(
        state: SearchState,
        cost: usize,
        mul_operation: MulOperation,
        cost_table: &mut HashMap<SearchState, (usize, MulOperation)>,
        queue: &mut VecDeque<SearchState>,
    ) {
        let state_norm = state.normalize_to_sorted();
        let entry = cost_table.entry(state_norm.clone());
        if let Vacant(entry) = entry {
            entry.insert((cost, mul_operation));
            queue.push_back(state);
        }
    }

    fn end_check(
        &self,
        state: &SearchState,
        cost: usize,
        m: usize,
        min_cost: &mut usize,
        min_state: &mut Option<SearchState>,
    ) {
        match state {
            SearchState::Primal { x, y } => {
                if (*x == m || *y == m) && cost < *min_cost {
                    *min_cost = cost;
                    *min_state = Some(state.clone());
                }
            }
            SearchState::Terminal { a: _, b: _ } => {
                if let Some(terminal_cost) = self.terminal_table.get(&state) {
                    let total_cost = cost + terminal_cost;
                    if total_cost < *min_cost {
                        *min_cost = total_cost;
                        *min_state = Some(state.clone());
                    }
                }
            }
        }
    }

    fn reconstruct_path(
        &self,
        state: SearchState,
        cost_table: &HashMap<SearchState, (usize, MulOperation)>,
        terminal_to_primal: &HashMap<SearchState, SearchState>,
    ) -> Option<Vec<MulOperation>> {
        let mut state = state;
        let mut path = Vec::new();
        while let Some((_, op)) = cost_table.get(&state.normalize_to_sorted()) {
            if let MulOperation::PrimalToTerminal = op {
                state = terminal_to_primal.get(&state)?.clone();
                continue;
            }
            if let MulOperation::Identity = op {
                break;
            }
            state = state.inverse(op);
            path.push(op.clone());
        }
        Some(path)
    }

    fn is_impossible_state(
        &self,
        state: &SearchState,
        cost: usize,
        m: usize,
        min_cost: usize,
    ) -> bool {
        if cost + 1 >= min_cost {
            return true;
        }
        match state {
            SearchState::Primal { x, y } => {
                if *x > m || *y > m {
                    return true;
                }

                min_cost <= cost + (Self::log2(m) - Self::log2(*x.max(y))) as usize
            }
            SearchState::Terminal { a, b } => min_cost <= cost + Self::log2(a.max(b) - 1) as usize,
        }
    }

    fn expand_primal_state(
        &self,
        state: SearchState,
        cost: usize,
        m: usize,
        cost_table: &mut HashMap<SearchState, (usize, MulOperation)>,
        terminal_to_primal: &mut HashMap<SearchState, SearchState>,
        queue: &mut VecDeque<SearchState>,
    ) {
        let (x, y) = match state {
            SearchState::Primal { x, y } => (x, y),
            _ => return,
        };

        let next_cost = cost + 1;
        let lcm = (x * y) >> Self::gcd_trailing(x, y);
        if lcm > m {
            if let Ok((a, b)) = Self::crt(x, y, m) {
                let next_state = SearchState::Terminal { a, b };
                terminal_to_primal
                    .entry(next_state.clone())
                    .or_insert(state.clone());
                Self::check_and_push(
                    next_state,
                    cost,
                    MulOperation::PrimalToTerminal,
                    cost_table,
                    queue,
                );
            }
            return;
        }

        let m_tail = m.trailing_zeros();
        if m_tail >= Self::gcd_trailing(2 * x, y) {
            Self::check_and_push(
                SearchState::Primal { x: 2 * x, y },
                next_cost,
                MulOperation::To2XY,
                cost_table,
                queue,
            );
        }
        if m_tail >= Self::gcd_trailing(x, 2 * y) {
            Self::check_and_push(
                SearchState::Primal { x, y: 2 * y },
                next_cost,
                MulOperation::ToX2Y,
                cost_table,
                queue,
            );
        }
        Self::check_and_push(
            SearchState::Primal { x: x + y, y },
            next_cost,
            MulOperation::ToXyY,
            cost_table,
            queue,
        );
        Self::check_and_push(
            SearchState::Primal { x, y: x + y },
            next_cost,
            MulOperation::ToXYx,
            cost_table,
            queue,
        );
    }

    fn expand_terminal_state(
        &self,
        state: SearchState,
        cost: usize,
        cost_table: &mut HashMap<SearchState, (usize, MulOperation)>,
        queue: &mut VecDeque<SearchState>,
    ) {
        let (a, b) = match state {
            SearchState::Terminal { a, b } => (a, b),
            _ => return,
        };

        let next_cost = cost + 1;

        if a % 2 == 0 {
            Self::check_and_push(
                SearchState::Terminal { a: a / 2, b },
                next_cost,
                MulOperation::To2XY,
                cost_table,
                queue,
            );
        }
        if b % 2 == 0 {
            Self::check_and_push(
                SearchState::Terminal { a, b: b / 2 },
                next_cost,
                MulOperation::ToX2Y,
                cost_table,
                queue,
            );
        }
        if a >= b {
            Self::check_and_push(
                SearchState::Terminal { a: a - b, b },
                next_cost,
                MulOperation::ToXYx,
                cost_table,
                queue,
            );
        } else {
            Self::check_and_push(
                SearchState::Terminal { a, b: b - a },
                next_cost,
                MulOperation::ToXyY,
                cost_table,
                queue,
            );
        }
    }

    fn solve(&self, m: usize, initial_state: SearchState) -> Option<(usize, Vec<MulOperation>)> {
        let mut queue = VecDeque::new();
        queue.push_back(initial_state.clone());
        let mut cost_table = HashMap::default();
        let mut terminal_to_primal = HashMap::default();
        cost_table.insert(initial_state, (0, MulOperation::Identity));

        let mut min_cost = usize::MAX / 2;
        let mut min_state = None;

        while let Some(state) = queue.pop_front() {
            let cost = cost_table[&state.normalize_to_sorted()].0;

            self.end_check(&state, cost, m, &mut min_cost, &mut min_state);

            if self.is_impossible_state(&state, cost, m, min_cost) {
                continue;
            }

            match state {
                SearchState::Primal { x: _, y: _ } => {
                    self.expand_primal_state(
                        state,
                        cost,
                        m,
                        &mut cost_table,
                        &mut terminal_to_primal,
                        &mut queue,
                    );
                }
                SearchState::Terminal { a: _, b: _ } => {
                    self.expand_terminal_state(state, cost, &mut cost_table, &mut queue);
                }
            }
        }

        let state = min_state?.clone();
        let mut path = self.terminal_table.get_path(&state).unwrap_or_default();
        path.extend(self.reconstruct_path(state, &cost_table, &terminal_to_primal)?);
        path.reverse();
        Some((min_cost, path))
    }
}

fn main() {
    const TERMINAL_TABLE_SIZE: usize = 100;
    let solver = Solver::new(TERMINAL_TABLE_SIZE);
    let initial_state = SearchState::Primal { x: 1, y: 1 };
    let (cost, path) = solver.solve(110, initial_state).unwrap();
    println!("cost: {}", cost);
    for state in path.iter() {
        println!("{:?}", state);
    }
}

#[cfg(test)]
mod tests {
    fn naive_dp(size: usize) -> Vec<usize> {
        let mut table = vec![vec![usize::MAX / 2; size]; size];
        table[1][1] = 0;

        for i in 0..size {
            for j in 0..size {
                if i % 2 == 0 {
                    table[i][j] = table[i][j].min(table[i / 2][j] + 1);
                }
                if j % 2 == 0 {
                    table[i][j] = table[i][j].min(table[i][j / 2] + 1);
                }
                if i >= j {
                    table[i][j] = table[i][j].min(table[i - j][j] + 1);
                }
                if j >= i {
                    table[i][j] = table[i][j].min(table[i][j - i] + 1);
                }
            }
        }

        table
            .into_iter()
            .map(|row| row.into_iter().min().unwrap())
            .collect()
    }

    fn test_solver<const TERMINAL_TABLE_SIZE: usize, const MAX_SIZE: usize>() {
        let solver = super::Solver::new(TERMINAL_TABLE_SIZE);
        let expected = naive_dp(MAX_SIZE);

        for (i, &expected) in expected.iter().enumerate().skip(1) {
            let initial_state = super::SearchState::Primal { x: 1, y: 1 };
            let (cost, path) = solver.solve(i, initial_state.clone()).unwrap();
            assert_eq!(
                cost, expected,
                "Failed for i: {}, Initial state: {:?}, Path: {:?}",
                i, initial_state, path
            );

            let sim = path.iter().fold(initial_state, |state, op| state.apply(op));
            if let super::SearchState::Primal { x, y } = sim {
                // assert_eq!(x.max(y), i, "i: {}, path: {:?}, sim: {:?}", i, path, sim);
                assert_eq!(
                    x.max(y),
                    i,
                    "Path reached invalid state: i: {}, path: {:?}, sim: {:?}",
                    i,
                    path,
                    sim
                );
            } else {
                panic!(
                    "Path reached invalid state: i: {}, path: {:?}, sim: {:?}",
                    i, path, sim
                );
            }
        }
    }
    #[test]
    fn test_solver_with_small_table() {
        test_solver::<2, 1000>();
    }

    #[test]
    fn test_solver_with_medium_table() {
        test_solver::<100, 1000>();
    }

    #[test]
    fn test_solver_with_large_table() {
        test_solver::<1000, 1000>();
    }

    #[test]
    fn test_solver_5000() {
        test_solver::<1000, 5000>();
    }
}
