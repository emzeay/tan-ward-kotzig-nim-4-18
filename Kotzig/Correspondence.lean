import Kotzig.GameTargets
import Kotzig.GameSemantics

namespace Kotzig

/-- The imported visited-list evaluator agrees with the unvisited-list semantics,
for every fuel, whenever the two board representations correspond. -/
theorem prototype_evaluate_eq (n : Nat) (steps : List Nat) (hn : 0 < n) (fuel : Nat) :
    ∀ s visited, Represents n visited s.available →
      evaluate n steps fuel s =
        GameTargets.firstPlayerWins n steps fuel s.position visited := by
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
      intro s visited hr
      simp only [evaluate, GameTargets.firstPlayerWins]
      apply congrArg (List.any steps)
      funext step
      have hd : destination n s.position step < n := Nat.mod_lt _ hn
      have he : decide (destination n s.position step ∈ s.available) =
          !(visited.contains (destination n s.position step)) := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, Bool.not_eq_true', Bool.eq_false_iff]
        have hr' := hr.2 (destination n s.position step)
        simp only [hd, true_and] at hr'
        exact hr'.trans (not_congr List.contains_iff_mem).symm
      rw [he, ih (move n s step) (destination n s.position step :: visited)
        (move_represents hr)]
      rfl

theorem prototype_initialWin_eq {n : Nat} (hn : 0 < n) (steps : List Nat) :
    initialWin n steps = GameTargets.initialWin n steps :=
  prototype_evaluate_eq n steps hn n (initial n) [0] (initial_represents n)

/-- The starting proposition in the imported artifact refers to the same faithful
normal-play outcome as the new semantics; this does not prove its classification. -/
theorem prototype_initial_outcome {n : Nat} (hn : 0 < n) (steps : List Nat) :
    Outcome n steps (initial n) (GameTargets.initialWin n steps) := by
  rw [← prototype_initialWin_eq hn]
  exact initial_outcome n steps

#print axioms prototype_evaluate_eq
#print axioms prototype_initial_outcome
end Kotzig
