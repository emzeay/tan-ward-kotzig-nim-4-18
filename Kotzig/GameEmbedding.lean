import Kotzig.GameSemantics

/-!
Outcome transport under an injective modular vertex embedding. The target may
contain additional vertices outside the image: destination preservation proves
that play from an embedded position cannot reach them. No game classification
or source theorem is assumed.
-/
namespace Kotzig

/-- A vertex map and step map preserving every modular destination. -/
structure VertexEmbedding (n m : Nat) (vertex stepMap : Nat → Nat) : Prop where
  sourcePositive : 0 < n
  targetPositive : 0 < m
  bounded : ∀ x, x < n → vertex x < m
  injective : ∀ x y, x < n → y < n → vertex x = vertex y → x = y
  destination : ∀ x step, x < n →
    vertex (Kotzig.destination n x step) =
      Kotzig.destination m (vertex x) (stepMap step)

/-- Availability need only agree on the image. Additional target vertices are
allowed, and no surjectivity is required. -/
structure EmbeddedState (n : Nat) (vertex : Nat → Nat) (s t : State) : Prop where
  sourceBound : s.position < n
  position : t.position = vertex s.position
  sourceNodup : s.available.Nodup
  targetNodup : t.available.Nodup
  available : ∀ x, x < n → (x ∈ s.available ↔ vertex x ∈ t.available)

theorem embedding_move {n m vertex stepMap s t step}
    (he : VertexEmbedding n m vertex stepMap) (hs : EmbeddedState n vertex s t) :
    EmbeddedState n vertex (move n s step) (move m t (stepMap step)) := by
  have hd : vertex (destination n s.position step) = destination m t.position (stepMap step) := by
    rw [hs.position]
    exact he.destination s.position step hs.sourceBound
  refine ⟨Nat.mod_lt _ he.sourcePositive, hd.symm,
    hs.sourceNodup.erase _, hs.targetNodup.erase _, ?_⟩
  intro x hx
  simp only [move, List.Nodup.mem_erase_iff hs.sourceNodup,
    List.Nodup.mem_erase_iff hs.targetNodup]
  rw [hs.available x hx, ← hd]
  have hi : vertex x = vertex (destination n s.position step) ↔
      x = destination n s.position step := by
    constructor
    · exact he.injective x _ hx (Nat.mod_lt _ he.sourcePositive)
    · intro hh; rw [hh]
  exact and_congr (not_congr hi.symm) Iff.rfl

theorem embedding_destination {n m vertex stepMap s t step}
    (he : VertexEmbedding n m vertex stepMap) (hs : EmbeddedState n vertex s t) :
    (destination n s.position step ∈ s.available) ↔
      (destination m t.position (stepMap step) ∈ t.available) := by
  have hd : vertex (destination n s.position step) = destination m t.position (stepMap step) := by
    rw [hs.position]
    exact he.destination s.position step hs.sourceBound
  simpa only [hd] using hs.available (destination n s.position step) (Nat.mod_lt _ he.sourcePositive)

/-- Same-fuel evaluation agrees without imposing a fuel sufficiency assumption. -/
theorem embedding_evaluate {n m vertex stepMap}
    (he : VertexEmbedding n m vertex stepMap) (steps : List Nat) (fuel : Nat) :
    ∀ s t, EmbeddedState n vertex s t →
      evaluate n steps fuel s = evaluate m (steps.map stepMap) fuel t := by
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
      intro s t hs
      simp only [evaluate, List.any_map]
      apply List.any_congr rfl
      intro step
      have ha : decide (destination n s.position step ∈ s.available) =
          decide (destination m t.position (stepMap step) ∈ t.available) := by
        apply Bool.eq_iff_iff.mpr
        simpa using embedding_destination he hs (step := step)
      rw [ha, ih _ _ (embedding_move he hs)]
      rfl

/-- Strategy derivations are preserved in both directions. Adequate fuel follows
from existing termination theorems, using one common bound for the two boards. -/
theorem embedding_outcome {n m vertex stepMap s t winner}
    (he : VertexEmbedding n m vertex stepMap) (hs : EmbeddedState n vertex s t)
    (steps : List Nat) :
    Outcome n steps s winner ↔ Outcome m (steps.map stepMap) t winner := by
  rw [outcome_iff_evaluate (fuel := s.available.length + t.available.length) (by omega),
    outcome_iff_evaluate (fuel := s.available.length + t.available.length) (by omega),
    embedding_evaluate he steps _ s t hs]

theorem embedding_initial {n m vertex stepMap}
    (he : VertexEmbedding n m vertex stepMap) (hzero : vertex 0 = 0) :
    EmbeddedState n vertex (initial n) (initial m) := by
  refine ⟨he.sourcePositive, ?_, (initial_represents n).1, (initial_represents m).1, ?_⟩
  · simpa only [initial] using hzero.symm
  · intro x hx
    rw [(initial_represents n).2, (initial_represents m).2]
    have htarget := he.bounded x hx
    have hz : vertex x = 0 ↔ x = 0 := by
      constructor
      · intro hh
        exact he.injective x 0 hx he.sourcePositive (hh.trans hzero.symm)
      · intro hh; rw [hh, hzero]
    simp only [List.mem_cons, List.not_mem_nil, or_false, hx, htarget, true_and]
    exact not_congr hz.symm

/-- Initial winners agree even when target vertices outside the image are present. -/
theorem embedding_initialWin {n m vertex stepMap}
    (he : VertexEmbedding n m vertex stepMap) (hzero : vertex 0 = 0) (steps : List Nat) :
    initialWin n steps = initialWin m (steps.map stepMap) := by
  have ho := (embedding_outcome he (embedding_initial he hzero) steps).mp (initial_outcome n steps)
  exact (outcome_unique (initial_outcome m (steps.map stepMap)) ho).symm

theorem embedding_initial_outcome {n m vertex stepMap winner}
    (he : VertexEmbedding n m vertex stepMap) (hzero : vertex 0 = 0) (steps : List Nat) :
    Outcome n steps (initial n) winner ↔
      Outcome m (steps.map stepMap) (initial m) winner :=
  embedding_outcome he (embedding_initial he hzero) steps

/-- Scaling selects the zero residue component of a larger board. Other target
vertices stay present but cannot be reached by scaled moves. -/
theorem scaling_embedding {n factor : Nat} (hn : 0 < n) (hf : 0 < factor) :
    VertexEmbedding n (factor * n) (fun x => factor * x) (fun step => factor * step) := by
  refine ⟨hn, Nat.mul_pos hf hn, ?_, ?_, ?_⟩
  · intro x hx
    exact (Nat.mul_lt_mul_left hf).mpr hx
  · intro x y _ _ he
    exact Nat.eq_of_mul_eq_mul_left hf he
  · intro x step _
    simp only [destination, ← Nat.mul_add, Nat.mul_mod_mul_left]

theorem scaling_initialWin {n factor : Nat} (hn : 0 < n) (hf : 0 < factor) (steps : List Nat) :
    initialWin n steps = initialWin (factor * n) (steps.map fun step => factor * step) :=
  embedding_initialWin (scaling_embedding hn hf) (Nat.mul_zero factor) steps

theorem scaling_initial_outcome {n factor winner} (hn : 0 < n) (hf : 0 < factor)
    (steps : List Nat) :
    Outcome n steps (initial n) winner ↔
      Outcome (factor * n) (steps.map fun step => factor * step) (initial (factor * n)) winner :=
  embedding_initial_outcome (scaling_embedding hn hf) (Nat.mul_zero factor) steps

#print axioms embedding_evaluate
#print axioms embedding_outcome
#print axioms embedding_initialWin
#print axioms scaling_initialWin
end Kotzig
