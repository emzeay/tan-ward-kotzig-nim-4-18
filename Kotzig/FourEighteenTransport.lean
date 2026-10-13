import Kotzig.GameMultiplication
import Kotzig.GameSteps

namespace Kotzig.FourEighteen

/-- The reflection multiplier is a unit on every positive board of size at least two. -/
theorem reflection_square {n : Nat} (hn : 2 ≤ n) :
    ((n-1)*(n-1)) % n = 1 := by
  have he : (n-1)*(n-1) = n*(n-2)+1 := by
    have hnn : 2*n ≤ n*n := Nat.mul_le_mul_right n hn
    simp only [Nat.sub_mul, Nat.mul_sub, Nat.mul_one, Nat.one_mul, Nat.mul_two]
    omega
  rw [he, Nat.add_mod]
  simp [Nat.mod_eq_of_lt (by omega : 1 < n)]

/-- Reflection sends the original three-step move to the reflected backward-three move. -/
theorem reflection_three {n : Nat} (hn : 5 ≤ n) :
    ((n-1)*3) % n = n-3 := by
  have he : (n-1)*3 = 2*n+(n-3) := by omega
  rw [he, Nat.add_mod]
  simp [Nat.mod_eq_of_lt (by omega : n-3 < n)]

/-- Uniform actual-game transport: all initial strategies and all opponent moves
are preserved, with no history restriction or placement turn. -/
theorem reflection_outcome {n : Nat} (hn : 5 ≤ n) (winner : Bool) :
    Outcome n [3,n-1] (initial n) winner ↔
    Outcome n [1,n-3] (initial n) winner := by
  have he := multiplication_embedding (unit := n-1) (inverse := n-1)
    (by omega : 0 < n) (reflection_square (by omega : 2 ≤ n))
  have ho := embedding_initial_outcome (winner := winner) he (by simp) [3,n-1]
  simp only [List.map_cons, List.map_nil, reflection_three hn,
    reflection_square (by omega : 2 ≤ n)] at ho
  exact ho.trans (outcome_swap (n := n) (s := initial n) (first := n-3) (second := 1) (winner := winner))

#print axioms reflection_outcome
end Kotzig.FourEighteen
