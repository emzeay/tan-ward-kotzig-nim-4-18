import Kotzig.GameSemantics

namespace Kotzig

theorem terminal_outcome {n steps s} (ht : ∀ step, ¬ Legal n steps s step) :
    Outcome n steps s false := by
  apply Outcome.lose
  intro step hl
  exact False.elim (ht step hl)

theorem forced_outcome {n steps s step b}
    (hl : Legal n steps s step)
    (ho : ∀ t, Legal n steps s t → t = step)
    (hc : Outcome n steps (move n s step) b) : Outcome n steps s (!b) := by
  cases b with
  | false => exact Outcome.win hl hc
  | true =>
      apply Outcome.lose
      intro t ht
      rw [ho t ht]
      exact hc

theorem two_options_outcome {n s first second a b}
    (hfirst : Legal n [first,second] s first)
    (hsecond : Legal n [first,second] s second)
    (hcfirst : Outcome n [first,second] (move n s first) a)
    (hcsecond : Outcome n [first,second] (move n s second) b) :
    Outcome n [first,second] s (!a || !b) := by
  cases a with
  | false => exact Outcome.win hfirst hcfirst
  | true =>
      cases b with
      | false => exact Outcome.win hsecond hcsecond
      | true =>
          apply Outcome.lose
          intro step hl
          have hm := hl.1
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with he | he
          · subst step; exact hcfirst
          · subst step; exact hcsecond

/-- A forced odd-depth hole chain. Other parts of the board are unrestricted. -/
def Tail (n h i : Nat) (s : State) : Prop :=
  s.position = 2*i+1 ∧ 2*h+2 < n ∧ i < h ∧ s.available.Nodup ∧
  (∀ j, j ≤ h → (2*j+1 ∈ s.available ↔ i < j ∧ j < h)) ∧
  (∀ j, j ≤ h → 2*j ∉ s.available)

theorem tail_destination_two {n h i s} (ht : Tail n h i s) :
    destination n s.position 2 = 2*(i+1)+1 := by
  unfold destination
  rw [ht.1]
  have he : 2*i+1+2 = 2*(i+1)+1 := by omega
  rw [he, Nat.mod_eq_of_lt (by have := ht.2.1; have := ht.2.2.1; omega)]

theorem tail_destination_back {n h i s} (ht : Tail n h i s) :
    destination n s.position (n-1) = 2*i := by
  unfold destination
  rw [ht.1]
  have he : 2*i+1+(n-1) = n+2*i := by have := ht.2.1; omega
  rw [he, Nat.add_mod]
  simp only [Nat.mod_self, Nat.zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by have := ht.2.1; have := ht.2.2.1; omega)

theorem tail_legal {n h i s step} (ht : Tail n h i s) :
    Legal n [2,n-1] s step ↔ step = 2 ∧ i+1 < h := by
  constructor
  · intro hl
    have hm := hl.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with he | he
    · subst step
      have hh := hl.2
      rw [tail_destination_two ht] at hh
      have hm := (ht.2.2.2.2.1 (i+1) (by have := ht.2.2.1; omega)).mp hh
      exact ⟨rfl, hm.2⟩
    · subst step
      have hh := hl.2
      rw [tail_destination_back ht] at hh
      exact False.elim (ht.2.2.2.2.2 i (by have := ht.2.2.1; omega) hh)
  · rintro ⟨rfl, hh⟩
    constructor
    · simp
    · rw [tail_destination_two ht]
      exact (ht.2.2.2.2.1 (i+1) (by omega)).mpr ⟨by omega, hh⟩

theorem tail_move {n h i s} (ht : Tail n h i s) (hh : i+1 < h) :
    Tail n h (i+1) (move n s 2) := by
  refine ⟨tail_destination_two ht, ht.2.1, hh, ht.2.2.2.1.erase _, ?_, ?_⟩
  · intro j hj
    simp only [move, tail_destination_two ht,
      List.Nodup.mem_erase_iff ht.2.2.2.1, ht.2.2.2.2.1 j hj]
    omega
  · intro j hj
    simp only [move]
    intro hm
    exact ht.2.2.2.2.2 j hj (List.mem_of_mem_erase hm)

/-- The actual game's tail has exactly h-i-1 forced moves remaining. -/
theorem tail_outcome_aux (r : Nat) : ∀ n h i s,
    Tail n h i s → h = i+r+1 →
    Outcome n [2,n-1] s (decide (r % 2 = 1)) := by
  induction r with
  | zero =>
      intro n h i s ht he
      simp only [Nat.zero_mod, Nat.zero_ne_one, decide_false]
      apply Outcome.lose
      intro step hl
      have hh := (tail_legal ht).mp hl
      omega
  | succ r ih =>
      intro n h i s ht he
      have hh : i+1<h := by omega
      have hl : Legal n [2,n-1] s 2 := (tail_legal ht).mpr ⟨rfl,hh⟩
      have hc := ih n h (i+1) (move n s 2) (tail_move ht hh) (by omega)
      have hp : decide ((r+1)%2=1) = !(decide (r%2=1)) := by
        have hb : r%2<2 := Nat.mod_lt _ (by omega)
        have hr : (r+1)%2 = (r%2+1)%2 := by omega
        by_cases hm : r%2=0
        · have he0 : (r+1)%2=1 := by omega
          simp [hm,he0]
        · have he1 : r%2=1 := by omega
          have he0 : (r+1)%2=0 := by omega
          simp [he1,he0]
      rw [hp]
      cases hb : decide (r%2=1) with
      | false =>
          simp only [Bool.not_false]
          apply Outcome.win hl
          simpa only [hb] using hc
      | true =>
          simp only [Bool.not_true]
          apply Outcome.lose
          intro step hs
          have hx := (tail_legal ht).mp hs
          rw [hx.1]
          simpa only [hb] using hc

theorem tail_outcome {n h i s} (ht : Tail n h i s) :
    Outcome n [2,n-1] s (decide ((h-i-1)%2=1)) :=
  tail_outcome_aux (h-i-1) n h i s ht (by have := ht.2.2.1; omega)

/-- A position immediately before wrapping into the first odd-depth hole chain. -/
def WrapTail (n h : Nat) (s : State) : Prop :=
  s.position = n-1 ∧ 2*h+2 < n ∧ s.available.Nodup ∧ n-2 ∉ s.available ∧
  (∀ j, j ≤ h → (2*j+1 ∈ s.available ↔ j < h)) ∧
  (∀ j, j ≤ h → 2*j ∉ s.available)

theorem wrap_destination_two {n h s} (hw : WrapTail n h s) :
    destination n s.position 2 = 1 := by
  unfold destination
  rw [hw.1]
  have he : n-1+2 = n+1 := by have := hw.2.1; omega
  rw [he, Nat.add_mod]
  simp only [Nat.mod_self, Nat.zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by have := hw.2.1; omega)

theorem wrap_destination_back {n h s} (hw : WrapTail n h s) :
    destination n s.position (n-1) = n-2 := by
  unfold destination
  rw [hw.1]
  have he : n-1+(n-1) = n+(n-2) := by have := hw.2.1; omega
  rw [he, Nat.add_mod]
  simp only [Nat.mod_self, Nat.zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by have := hw.2.1; omega)

theorem wrap_legal {n h s step} (hw : WrapTail n h s) :
    Legal n [2,n-1] s step ↔ step = 2 ∧ 0 < h := by
  constructor
  · intro hl
    have hm := hl.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with he | he
    · subst step
      have hh := hl.2
      rw [wrap_destination_two hw] at hh
      have hm := (hw.2.2.2.2.1 0 (by omega)).mp hh
      exact ⟨rfl,hm⟩
    · subst step
      have hh := hl.2
      rw [wrap_destination_back hw] at hh
      exact False.elim (hw.2.2.2.1 hh)
  · rintro ⟨rfl,hh⟩
    constructor
    · simp
    · rw [wrap_destination_two hw]
      exact (hw.2.2.2.2.1 0 (by omega)).mpr hh

theorem wrap_move_tail {n h s} (hw : WrapTail n h s) (hh : 0<h) :
    Tail n h 0 (move n s 2) := by
  refine ⟨wrap_destination_two hw, hw.2.1, hh, hw.2.2.1.erase _, ?_, ?_⟩
  · intro j hj
    simp only [move, wrap_destination_two hw,
      List.Nodup.mem_erase_iff hw.2.2.1, hw.2.2.2.2.1 j hj]
    omega
  · intro j hj
    simp only [move]
    intro hm
    exact hw.2.2.2.2.2 j hj (List.mem_of_mem_erase hm)

/-- Wrapping and then exhausting the chain takes exactly h moves. -/
theorem wrap_tail_outcome {n h s} (hw : WrapTail n h s) :
    Outcome n [2,n-1] s (decide (h%2=1)) := by
  by_cases hh : h=0
  · subst h
    apply terminal_outcome
    intro step hl
    have := (wrap_legal hw).mp hl
    omega
  · have hp : 0<h := by omega
    have hc := tail_outcome (wrap_move_tail hw hp)
    have hl : Legal n [2,n-1] s 2 := (wrap_legal hw).mpr ⟨rfl,hp⟩
    have ho : ∀ step, Legal n [2,n-1] s step → step=2 := by
      intro step hs
      exact ((wrap_legal hw).mp hs).1
    have he : decide (h%2=1) = !(decide ((h-0-1)%2=1)) := by
      simp only [Nat.sub_zero]
      have hb : h%2<2 := Nat.mod_lt _ (by omega)
      by_cases hm : h%2=0
      · have ht : (h-1)%2=1 := by omega
        simp [hm,ht]
      · have ht : (h-1)%2=0 := by omega
        have hm' : h%2=1 := by omega
        simp [hm',ht]
    rw [he]
    exact forced_outcome hl ho hc

#print axioms tail_outcome
#print axioms wrap_tail_outcome
end Kotzig
