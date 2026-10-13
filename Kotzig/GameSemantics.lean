import Std

/-!
A finite normal-play semantics. `available` lists precisely the unvisited vertices;
each legal move erases its landing vertex. Passing over a vertex is unrestricted.
No classification axiom or conjecture is assumed.
-/
namespace Kotzig

structure State where
  position : Nat
  available : List Nat
  deriving DecidableEq, Repr

def destination (n position step : Nat) : Nat := (position + step) % n

def Legal (n : Nat) (steps : List Nat) (s : State) (step : Nat) : Prop :=
  step ∈ steps ∧ destination n s.position step ∈ s.available

instance (n : Nat) (steps : List Nat) (s : State) (step : Nat) :
    Decidable (Legal n steps s step) := inferInstanceAs (Decidable (_ ∧ _))

def move (n : Nat) (s : State) (step : Nat) : State :=
  let d := destination n s.position step
  ⟨d, s.available.erase d⟩

def initial (n : Nat) : State := ⟨0, (List.range n).erase 0⟩

def evaluate (n : Nat) (steps : List Nat) : Nat → State → Bool
  | 0, _ => false
  | fuel + 1, s => steps.any fun step =>
      decide (destination n s.position step ∈ s.available) &&
        !(evaluate n steps fuel (move n s step))

/-- A strategy derivation: a winning node chooses one losing child; a losing node
requires a winning response at every legal child. This covers every opponent move. -/
inductive Outcome (n : Nat) (steps : List Nat) : State → Bool → Prop where
  | win {s step} : Legal n steps s step → Outcome n steps (move n s step) false →
      Outcome n steps s true
  | lose {s} : (∀ step, Legal n steps s step → Outcome n steps (move n s step) true) →
      Outcome n steps s false

theorem move_length {n steps s step} (h : Legal n steps s step) :
    (move n s step).available.length + 1 = s.available.length := by
  simp only [move]
  rw [List.length_erase_of_mem h.2]
  have hp : 0 < s.available.length := List.length_pos_iff.mpr (by
    intro he; simpa [he] using h.2)
  omega

/-- Any legal play consumes one available vertex on every move. -/
theorem move_decreases {n steps s step} (h : Legal n steps s step) :
    (move n s step).available.length < s.available.length := by
  have := move_length h
  omega

/-- An operational play with exactly `k` token moves. -/
inductive Play (n : Nat) (steps : List Nat) : State → State → Nat → Prop where
  | nil {s} : Play n steps s s 0
  | cons {s t k step} : Legal n steps s step → Play n steps (move n s step) t k →
      Play n steps s t (k + 1)

theorem play_length {n steps s t k} (h : Play n steps s t k) :
    t.available.length + k = s.available.length := by
  induction h with
  | nil => omega
  | cons hl _ ih => have := move_length hl; omega

theorem play_bound {n steps s t k} (h : Play n steps s t k) :
    k ≤ s.available.length := by have := play_length h; omega

/-- Once fuel is at least the number of unvisited vertices, evaluation supplies
an actual normal-play strategy derivation, including at terminal states. -/
theorem evaluate_outcome (n : Nat) (steps : List Nat) (fuel : Nat) :
    ∀ s, s.available.length ≤ fuel → Outcome n steps s (evaluate n steps fuel s) := by
  induction fuel with
  | zero =>
      intro s h
      apply Outcome.lose
      intro step hs
      have he : s.available = [] := List.eq_nil_of_length_eq_zero (by omega)
      simpa [he] using hs.2
  | succ fuel ih =>
      intro s h
      cases he : evaluate n steps (fuel + 1) s with
      | false =>
          apply Outcome.lose
          intro step hs
          have hl : (move n s step).available.length ≤ fuel := by
            have := move_length hs
            omega
          have hc := ih (move n s step) hl
          have ha := (List.any_eq_false.mp he) step hs.1
          have hb : evaluate n steps fuel (move n s step) = true := by
            simpa [hs.2] using ha
          simpa [hb] using hc
      | true =>
          obtain ⟨step, hm, hv⟩ := List.any_eq_true.mp he
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hv
          have hd : destination n s.position step ∈ s.available := by
            exact hv.1
          have hs : Legal n steps s step := ⟨hm, hd⟩
          apply Outcome.win hs
          have hl : (move n s step).available.length ≤ fuel := by
            have := move_length hs
            omega
          have hc := ih (move n s step) hl
          have hb : evaluate n steps fuel (move n s step) = false := by
            simpa using hv.2
          simpa [hb] using hc

/-- Strategy derivations cannot give opposite winners. -/
theorem outcome_unique {n steps s a} (h : Outcome n steps s a) :
    ∀ {b}, Outcome n steps s b → a = b := by
  induction h with
  | win hl hc ih =>
      intro b hb
      cases hb with
      | win _ _ => rfl
      | lose hall => have hh := ih (hall _ hl); cases hh
  | lose hall ih =>
      intro b hb
      cases hb with
      | lose _ => rfl
      | win hl hc => have hh := ih _ hl hc; cases hh

theorem adequate_fuel_independent {n steps s f g}
    (hf : s.available.length ≤ f) (hg : s.available.length ≤ g) :
    evaluate n steps f s = evaluate n steps g s :=
  outcome_unique (evaluate_outcome n steps f s hf) (evaluate_outcome n steps g s hg)

/-- Complete solver/strategy-tree correspondence for sufficient fuel. -/
theorem outcome_iff_evaluate {n steps s fuel winner} (hf : s.available.length ≤ fuel) :
    Outcome n steps s winner ↔ evaluate n steps fuel s = winner := by
  constructor
  · intro ho
    exact outcome_unique (evaluate_outcome n steps fuel s hf) ho
  · intro he
    rw [← he]
    exact evaluate_outcome n steps fuel s hf

/-- Exact correspondence between a list of unvisited vertices and a visited history. -/
def Represents (n : Nat) (visited available : List Nat) : Prop :=
  available.Nodup ∧ ∀ d, d ∈ available ↔ d < n ∧ d ∉ visited

theorem initial_represents (n : Nat) : Represents n [0] (initial n).available := by
  constructor
  · exact List.Nodup.erase 0 List.nodup_range
  · intro d
    simp only [initial, List.Nodup.mem_erase_iff List.nodup_range,
      List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
    simp only [and_comm]

theorem move_represents {n visited s step}
    (hr : Represents n visited s.available) :
    Represents n (destination n s.position step :: visited) (move n s step).available := by
  constructor
  · exact hr.1.erase _
  · intro d
    simp only [move, List.Nodup.mem_erase_iff hr.1, hr.2,
      List.mem_cons, not_or]
    simp only [and_left_comm]

/-- Legality is exactly the rule forbidding a previously visited landing vertex.
There is no condition on vertices passed over. -/
theorem legal_iff_unvisited {n steps visited s step} (hn : 0 < n)
    (hr : Represents n visited s.available) :
    Legal n steps s step ↔ step ∈ steps ∧ destination n s.position step ∉ visited := by
  unfold Legal
  rw [hr.2]
  have hb : destination n s.position step < n := Nat.mod_lt _ hn
  simp only [hb, true_and]

theorem initial_available_length {n : Nat} (hn : 0 < n) :
    (initial n).available.length = n - 1 := by
  simp only [initial]
  rw [List.length_erase_of_mem (List.mem_range.mpr hn), List.length_range]

theorem initial_play_bound {n steps t k} (hn : 0 < n)
    (h : Play n steps (initial n) t k) : k ≤ n - 1 := by
  have := play_bound h
  rwa [initial_available_length hn] at this

def initialWin (n : Nat) (steps : List Nat) : Bool := evaluate n steps n (initial n)

theorem initial_outcome (n : Nat) (steps : List Nat) :
    Outcome n steps (initial n) (initialWin n steps) := by
  apply evaluate_outcome
  exact Nat.le_trans List.length_erase_le (by simp)

/-- Board equivalence ignores the order of the duplicate-free unvisited list. -/
def BoardEquiv (s t : State) : Prop :=
  s.position = t.position ∧ ∀ d, d ∈ s.available ↔ d ∈ t.available

theorem move_boardEquiv {n s t step} (he : BoardEquiv s t)
    (hs : s.available.Nodup) (ht : t.available.Nodup) :
    BoardEquiv (move n s step) (move n t step) := by
  constructor
  · simp only [move, he.1]
  · intro d
    simp only [move, List.Nodup.mem_erase_iff hs, List.Nodup.mem_erase_iff ht,
      he.1, he.2]

theorem evaluate_boardEquiv (n : Nat) (steps : List Nat) (fuel : Nat) :
    ∀ s t, BoardEquiv s t → s.available.Nodup → t.available.Nodup →
      evaluate n steps fuel s = evaluate n steps fuel t := by
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
      intro s t he hs ht
      simp only [evaluate]
      apply congrArg (List.any steps)
      funext step
      simp only [he.1, he.2]
      rw [ih (move n s step) (move n t step) (move_boardEquiv he hs ht)
        (hs.erase _) (ht.erase _)]

theorem outcome_boardEquiv {n steps s t winner} (he : BoardEquiv s t)
    (hs : s.available.Nodup) (ht : t.available.Nodup) :
    Outcome n steps s winner ↔ Outcome n steps t winner := by
  rw [outcome_iff_evaluate (fuel := s.available.length + t.available.length) (by omega),
    outcome_iff_evaluate (fuel := s.available.length + t.available.length) (by omega),
    evaluate_boardEquiv n steps _ s t he hs ht]

#check evaluate_outcome
#check adequate_fuel_independent
#print axioms evaluate_outcome
#print axioms adequate_fuel_independent
#print axioms initial_outcome
end Kotzig
