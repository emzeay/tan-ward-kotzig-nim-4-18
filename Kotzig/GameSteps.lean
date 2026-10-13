import Kotzig.GameSemantics

/-! Reordering a two-step move list does not change the game or its outcome. -/
namespace Kotzig

theorem evaluate_swap (n first second fuel : Nat) : ∀ s,
    evaluate n [first,second] fuel s = evaluate n [second,first] fuel s := by
  induction fuel with
  | zero => intro s; rfl
  | succ fuel ih =>
    intro s
    simp only [evaluate, List.any_cons, List.any_nil, Bool.or_false]
    rw [ih (move n s first), ih (move n s second)]
    exact Bool.or_comm _ _

theorem initialWin_swap (n first second : Nat) :
    initialWin n [first,second] = initialWin n [second,first] :=
  evaluate_swap n first second n (initial n)

theorem outcome_swap {n first second s winner} :
    Outcome n [first,second] s winner ↔ Outcome n [second,first] s winner := by
  rw [outcome_iff_evaluate (fuel := s.available.length) (by omega),
    outcome_iff_evaluate (fuel := s.available.length) (by omega), evaluate_swap]

#print axioms initialWin_swap
#print axioms outcome_swap
end Kotzig
