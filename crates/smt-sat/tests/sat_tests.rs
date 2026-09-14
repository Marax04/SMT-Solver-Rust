use smt_sat::{LBool, SatSolver};

#[test]
fn test_sat_simple() {
    let mut solver = SatSolver::new();
    let x1 = solver.new_var();
    let x2 = solver.new_var();

    // (x1 or x2)
    solver.add_clause(vec![x1.to_lit(), x2.to_lit()]);
    // (!x1 or x2)
    solver.add_clause(vec![x1.to_neg_lit(), x2.to_lit()]);

    let res = solver.solve();
    assert_eq!(res, LBool::True);
    assert_eq!(solver.model_value(x2), LBool::True);
}

#[test]
fn test_unsat_simple() {
    let mut solver = SatSolver::new();
    let x = solver.new_var();

    solver.add_clause(vec![x.to_lit()]);
    solver.add_clause(vec![x.to_neg_lit()]);

    let res = solver.solve();
    assert_eq!(res, LBool::False);
}

#[test]
fn test_pigeonhole_2_1() {
    // 2 pigeons into 1 hole => UNSAT
    let mut solver = SatSolver::new();
    let p0_h0 = solver.new_var();
    let p1_h0 = solver.new_var();

    // Pigeon 0 must be in hole 0
    solver.add_clause(vec![p0_h0.to_lit()]);
    // Pigeon 1 must be in hole 0
    solver.add_clause(vec![p1_h0.to_lit()]);
    // At most one pigeon in hole 0: (!p0_h0 or !p1_h0)
    solver.add_clause(vec![p0_h0.to_neg_lit(), p1_h0.to_neg_lit()]);

    let res = solver.solve();
    assert_eq!(res, LBool::False);
}

#[test]
fn test_assumptions() {
    let mut solver = SatSolver::new();
    let x = solver.new_var();
    let y = solver.new_var();

    // (x or y)
    solver.add_clause(vec![x.to_lit(), y.to_lit()]);

    // Assume !x and !y => UNSAT
    let res = solver.solve_with_assumptions(&[x.to_neg_lit(), y.to_neg_lit()]);
    assert_eq!(res, LBool::False);

    // Assume x => SAT
    let res2 = solver.solve_with_assumptions(&[x.to_lit()]);
    assert_eq!(res2, LBool::True);
}

#[test]
fn test_drat_proof() {
    let mut solver = SatSolver::new();
    solver.enable_drat(true);
    let x = solver.new_var();
    solver.add_clause(vec![x.to_lit()]);
    solver.add_clause(vec![x.to_neg_lit()]);

    let res = solver.solve();
    assert_eq!(res, LBool::False);
}

#[test]
fn test_vsids_reinsert_after_backtrack() {
    use smt_sat::trail::Reason;
    use smt_sat::{SatSolver, Var, Vsids};

    let mut solver = SatSolver::new();
    let v0 = solver.new_var();
    let v1 = solver.new_var();
    let v2 = solver.new_var();
    let v3 = solver.new_var();

    // Verify initial VSIDS heap contains all variables
    let mut initial_vsids = Vsids::new();
    initial_vsids.ensure_var(4);
    for i in 0..4 {
        assert!(initial_vsids.is_in_heap(Var(i)));
    }

    // Simulate trail assignments at decision level 1
    solver.trail.new_decision_level();
    solver.trail.assign(v0.to_lit(), Reason::Decision);
    solver.trail.assign(v1.to_lit(), Reason::Unit);
    solver.trail.assign(v2.to_lit(), Reason::Unit);

    // Variable selection must skip assigned variables
    assert!(solver.trail.is_assigned(v0));
    assert!(solver.trail.is_assigned(v1));
    assert!(solver.trail.is_assigned(v2));
    assert!(!solver.trail.is_assigned(v3));

    // Backtrack to level 0: all unassigned variables MUST be restored to VSIDS heap
    let mut restored = Vec::new();
    solver.trail.backtrack_to_with(0, |v| restored.push(v));

    assert_eq!(restored.len(), 3);
    assert!(restored.contains(&v0));
    assert!(restored.contains(&v1));
    assert!(restored.contains(&v2));

    for &v in &[v0, v1, v2, v3] {
        assert!(!solver.trail.is_assigned(v));
    }

    // --- Key red/green assertion ---
    // After solve() completes, SatSolver::backtrack_to(0) is called internally.
    // This MUST re-insert all assigned variables back into the VSIDS heap.
    // With the BUGGY backtrack_to (no callback), variables assigned during
    // propagation are popped off the heap but never re-inserted, causing the
    // heap to shrink permanently across calls to solve().
    let mut s2 = SatSolver::new();
    let x0 = s2.new_var();
    let x1 = s2.new_var();
    let x2 = s2.new_var();
    let x3 = s2.new_var();

    // Formula: requires conflict + backtrack to solve
    // (x0 or x1) & (!x0 or x2) & (!x0 or !x2) & (x0 or !x1 or x3) & (x0 or !x1 or !x3)
    s2.add_clause(vec![x0.to_lit(), x1.to_lit()]);
    s2.add_clause(vec![x0.to_neg_lit(), x2.to_lit()]);
    s2.add_clause(vec![x0.to_neg_lit(), x2.to_neg_lit()]);
    s2.add_clause(vec![x0.to_lit(), x1.to_neg_lit(), x3.to_lit()]);
    s2.add_clause(vec![x0.to_lit(), x1.to_neg_lit(), x3.to_neg_lit()]);

    let res = s2.solve();
    assert_eq!(res, LBool::False, "Solver must conclude UNSAT after exploring conflicts via backtrack");
    assert!(s2.stats.conflicts > 0, "At least one conflict and backtrack must have occurred");

    // THE CRITICAL CHECK: after solve() finishes, backtrack_to(0) must have
    // re-inserted every variable back into the VSIDS heap.
    // With the buggy backtrack_to (no VSIDS callback):
    //   - Variables assigned during propagation are removed from the heap by select_decision_var()
    //   - They are NEVER re-inserted on backtrack
    //   - The heap loses variables permanently → is_in_heap returns false
    // With the correct backtrack_to_with callback:
    //   - Every variable unassigned during backtrack is re-inserted
    //   - The heap is always consistent with the trail assignment state
    for &v in &[x0, x1, x2, x3] {
        assert!(
            s2.vsids.is_in_heap(v),
            "Variable {:?} must be in VSIDS heap after solve() resets trail to level 0. \
             This fails with the buggy backtrack_to that drops the reinsertion callback.",
            v
        );
    }
}

#[test]
fn test_assumption_conflict_resolution_unsat() {
    let mut solver = SatSolver::new();
    let a = solver.new_var();
    let b = solver.new_var();
    let c = solver.new_var();
    let d = solver.new_var();

    // Clauses:
    // (a or b)
    // (!a or c)
    // (!c or d)
    // (!d)
    solver.add_clause(vec![a.to_lit(), b.to_lit()]);
    solver.add_clause(vec![a.to_neg_lit(), c.to_lit()]);
    solver.add_clause(vec![c.to_neg_lit(), d.to_lit()]);
    solver.add_clause(vec![d.to_neg_lit()]);

    // Under assumption [a = true]:
    // a=true implies c=true, which implies d=true, which contradicts (!d).
    // Conflict resolution derives (!a). Backtrack level is 0 < assumption level 1.
    // Solver must immediately return UNSAT without continuing past level 0.
    let res = solver.solve_with_assumptions(&[a.to_lit()]);
    assert_eq!(res, LBool::False, "Assumption conflict must yield UNSAT under assumptions");

    // Without assumption a=true, formula is SAT (with a=false, b=true, c=false, d=false)
    let res_no_assump = solver.solve();
    assert_eq!(res_no_assump, LBool::True, "Formula without assumption a=true is satisfiable");
    assert_eq!(solver.model_value(b), LBool::True);
}

