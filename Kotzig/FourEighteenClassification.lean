import Kotzig.FourEighteenLosing
import Kotzig.FourEighteenWinning
import Kotzig.FourEighteenEven
import Kotzig.FourEighteenTransport
import Kotzig.Correspondence

/-! Tan–Ward Conjecture4.18, with faithful normal-play strategies for every m>3.
The odd cases also follow mathematically from older consecutive-move results;
no external source statement or conjectural axiom is used in this proof. -/
namespace Kotzig.FourEighteen

/-- A uniform strategy derivation on the reflected +1/−3 board. -/
theorem reflected_strategy {n : Nat} (hn : 5 ≤ n) :
    Outcome n [1,n-3] (initial n) (decide (n%4≠3)) := by
  by_cases h3 : n%4=3
  · simpa [h3] using FourEighteenLosing.losing_initial_outcome hn h3
  · by_cases he : n%2=0
    · simpa [h3] using FourEighteenEven.even_initial_outcome hn he
    · have h1 : n%4=1 := by omega
      simpa [h3] using FourEighteenWinning.odd_initial_outcome hn h1

/-- Exact second-player outcome on every reflected board, without a finite cap. -/
theorem reflected_second_player_iff {n : Nat} (hn : 5 ≤ n) :
    Outcome n [1,n-3] (initial n) false ↔ n%4=3 := by
  constructor
  · intro ho
    have hb := outcome_unique ho (reflected_strategy hn)
    have : decide (n%4≠3) = false := hb.symm
    simpa using this
  · exact FourEighteenLosing.losing_initial_outcome hn

/-- Strategies for the literal original move pair and parameter convention. -/
theorem classification_strategy {m : Nat} (hm : 3 < m) :
    Outcome (m+1) [3,m] (initial (m+1)) (decide (m%4≠2)) := by
  have hn : 5 ≤ m+1 := by omega
  have ho := (reflection_outcome hn _).mpr (reflected_strategy hn)
  have he : decide ((m+1)%4≠3) = decide (m%4≠2) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  simpa only [Nat.add_sub_cancel,he] using ho

/-- The full original Conjecture4.18: no parity, upper bound or source premise. -/
theorem second_player_iff {m : Nat} (hm : 3 < m) :
    Outcome (m+1) [3,m] (initial (m+1)) false ↔ m%4=2 := by
  have ht := (reflection_outcome (n := m+1) (by omega) false).trans
    (reflected_second_player_iff (n := m+1) (by omega))
  have he : (m+1)%4=3 ↔ m%4=2 := by omega
  simpa only [Nat.add_sub_cancel] using ht.trans he

/-- Adequate-fuel evaluation of the faithful initial board has the exact winner. -/
theorem initial_classification {m : Nat} (hm : 3 < m) :
    initialWin (m+1) [3,m] = decide (m%4≠2) :=
  outcome_unique (initial_outcome _ _) (classification_strategy hm)

/-- The imported visited-history evaluator agrees with the same universal formula. -/
theorem prototype_initial_classification {m : Nat} (hm : 3 < m) :
    GameTargets.initialWin (m+1) [3,m] = decide (m%4≠2) := by
  rw [← prototype_initialWin_eq (by omega : 0 < m+1)]
  exact initial_classification hm

#print axioms reflected_strategy
#print axioms classification_strategy
#print axioms second_player_iff
#print axioms initial_classification
#print axioms prototype_initial_classification
end Kotzig.FourEighteen
