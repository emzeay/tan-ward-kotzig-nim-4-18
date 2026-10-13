import Kotzig.FrontierTail

namespace Kotzig.FourEighteenLosing

/-- A proof-local landing operation; under Nodup it is the actual game move. -/
def visit (s : State) (x : Nat) : State := ⟨x, s.available.filter (· != x)⟩
@[simp] theorem visit_position (s : State) (x : Nat) : (visit s x).position = x := rfl
@[simp] theorem visit_mem {s : State} {x y : Nat} :
    x ∈ (visit s y).available ↔ x ∈ s.available ∧ x ≠ y := by
  simp [visit]
@[simp] theorem visit_nodup {s : State} (h : s.available.Nodup) (x : Nat) :
    (visit s x).available.Nodup := h.filter _

theorem move_eq_visit {n s step} (h : s.available.Nodup) :
    move n s step = visit s (destination n s.position step) := by
  simp only [move, visit, List.Nodup.erase_eq_filter h]

theorem one_dest {n x : Nat} (h : x+1<n) : destination n x 1 = x+1 := by
  exact Nat.mod_eq_of_lt h

theorem back_dest {n x : Nat} (h : 3≤x) (hx : x<n) :
    destination n x (n-3) = x-3 := by
  unfold destination
  rw [show x+(n-3)=n+(x-3) by omega, Nat.add_mod]
  simp only [Nat.mod_self, Nat.zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

theorem one_boundary {n H : Nat} (h : 1≤H) :
    destination n (H-1) 1 = H%n := by unfold destination; congr 1; omega

theorem option_cases {n s step} (h : Legal n [1,n-3] s step) :
    step=1 ∨ step=n-3 := by simpa using h.1

theorem win_visit {n s step x} (hn : s.available.Nodup)
    (hm : step ∈ [1,n-3]) (hd : destination n s.position step=x)
    (hf : x ∈ s.available) (hc : Outcome n [1,n-3] (visit s x) false) :
    Outcome n [1,n-3] s true := by
  apply Outcome.win (step := step) ⟨hm, by simpa [hd] using hf⟩
  simpa [move_eq_visit hn, hd] using hc

structure Closed (n H : Nat) (s : State) : Prop where
  low : 3≤H
  bound : H+2<n
  position : s.position=H
  nodup : s.available.Nodup
  zero : 0 ∉ s.available
  here : H ∉ s.available
  next : H+1 ∉ s.available
  nextTwo : H+2 ∉ s.available
  fresh : ∀ x, 3≤x → x≤H-2 → x ∈ s.available

structure Open (n H : Nat) (s : State) : Prop where
  low : 3≤H
  bound : H+3<n
  position : s.position=H
  nodup : s.available.Nodup
  zero : 0 ∉ s.available
  one : 1 ∉ s.available
  two : 2 ∉ s.available
  here : H ∉ s.available
  third : H+3 ∉ s.available
  fresh : ∀ x, 3≤x → x≤H-1 → x ∈ s.available
  next : H+1 ∈ s.available
  nextTwo : H+2 ∈ s.available

/-- The two-choice current-player position after a backward/forward pair.
The top may be n, so the same lemma includes the initial wrap admission. -/
structure Middle (n H : Nat) (s : State) : Prop where
  low : 7≤H
  bound : H≤n
  position : s.position=H-2
  nodup : s.available.Nodup
  zero : 0 ∉ s.available
  top : H%n ∉ s.available
  previous : H-3 ∉ s.available
  here : H-2 ∉ s.available
  fresh : ∀ x, 3≤x → x≤H-4 → x ∈ s.available

theorem middle_outcome {n H s} (hm : Middle n H s)
    (ih : ∀ t, Closed n (H-4) t → Outcome n [1,n-3] t false) :
    Outcome n [1,n-3] s false := by
  have hlow := hm.low
  have hbound := hm.bound
  apply Outcome.lose
  intro step hl
  rcases option_cases hl with he | he
  · subst step
    have hd : destination n s.position 1=H-1 := by
      rw [hm.position, one_dest (by have := hm.bound; have := hm.low; omega)] <;> omega
    rw [move_eq_visit hm.nodup, hd]
    apply win_visit (visit_nodup hm.nodup _) (by simp)
      (show destination n (visit s (H-1)).position (n-3)=H-4 by
        rw [visit_position, back_dest (by have := hm.low; omega) (by have := hm.bound; omega)] <;> omega)
    · simp only [visit_mem]
      exact ⟨hm.fresh _ (by have := hm.low; omega) (by omega), by have := hm.low; omega⟩
    · apply ih
      refine ⟨by have := hm.low; omega, by have := hm.bound; have := hm.low; omega,
        rfl, by simp [hm.nodup], ?_, ?_, ?_, ?_, ?_⟩
      · simp only [visit_mem]; intro h; exact hm.zero h.1.1
      · simp
      · simp only [visit_mem]
        intro h; have heq : H-4+1=H-3 := by have := hm.low; omega
        exact hm.previous (by simpa [heq] using h.1.1)
      · simp only [visit_mem]
        intro h; have heq : H-4+2=H-2 := by have := hm.low; omega
        exact hm.here (by simpa [heq] using h.1.1)
      · intro x hx hb
        simp only [visit_mem]
        exact ⟨⟨hm.fresh x hx (by omega), by have := hm.low; omega⟩, by have := hm.low; omega⟩
  · subst step
    have hd : destination n s.position (n-3)=H-5 := by
      rw [hm.position, back_dest (by have := hm.low; omega) (by have := hm.bound; have := hm.low; omega)] <;> omega
    rw [move_eq_visit hm.nodup, hd]
    apply win_visit (visit_nodup hm.nodup _) (by simp)
      (show destination n (visit s (H-5)).position 1=H-4 by
        rw [visit_position, one_dest (by have := hm.bound; have := hm.low; omega)] <;> omega)
    · simp only [visit_mem]
      exact ⟨hm.fresh _ (by have := hm.low; omega) (by omega), by have := hm.low; omega⟩
    · apply ih
      refine ⟨by have := hm.low; omega, by have := hm.bound; have := hm.low; omega,
        rfl, by simp [hm.nodup], ?_, ?_, ?_, ?_, ?_⟩
      · simp only [visit_mem]; intro h; exact hm.zero h.1.1
      · simp
      · simp only [visit_mem]
        intro h; have heq : H-4+1=H-3 := by have := hm.low; omega
        exact hm.previous (by simpa [heq] using h.1.1)
      · simp only [visit_mem]
        intro h; have heq : H-4+2=H-2 := by have := hm.low; omega
        exact hm.here (by simpa [heq] using h.1.1)
      · intro x hx hb
        simp only [visit_mem]
        exact ⟨⟨hm.fresh x hx (by omega), by have := hm.low; omega⟩, by have := hm.low; omega⟩

/-- The backward child admits a legal +1 response into the middle phase. -/
theorem back_child {n H s} (hH : 7≤H) (hb : H+2<n)
    (hp : s.position=H) (hn : s.available.Nodup)
    (hz : 0 ∉ s.available) (hh : H ∉ s.available)
    (hf : ∀ x, 3≤x → x≤H-2 → x ∈ s.available)
    (ih : ∀ t, Closed n (H-4) t → Outcome n [1,n-3] t false) :
    Outcome n [1,n-3] (move n s (n-3)) true := by
  have hd : destination n s.position (n-3)=H-3 := by rw [hp]; exact back_dest (by omega) (by omega)
  rw [move_eq_visit hn, hd]
  apply win_visit (visit_nodup hn _) (by simp)
    (show destination n (visit s (H-3)).position 1=H-2 by rw [visit_position, one_dest (by omega)] <;> omega)
  · simp only [visit_mem]; exact ⟨hf _ (by omega) (by omega), by omega⟩
  · apply middle_outcome (ih := ih)
    refine ⟨hH, by omega, rfl, by simp [hn], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [visit_mem]; intro h; exact hz h.1.1
    · simp only [visit_mem, Nat.mod_eq_of_lt (show H<n by omega)]
      intro h; exact hh h.1.1
    · simp
    · simp
    · intro x hx hb'
      simp only [visit_mem]; exact ⟨⟨hf _ hx (by omega), by omega⟩, by omega⟩

theorem closed_outcome (k : Nat) : ∀ n s,
    Closed n (4*k+3) s → Outcome n [1,n-3] s false := by
  induction k with
  | zero =>
    intro n s hc
    apply terminal_outcome
    intro step hl
    rcases option_cases hl with he | he
    · subst step
      have hd : destination n s.position 1=4 := by rw [hc.position]; exact one_dest (by have := hc.bound; omega)
      exact hc.next (by simpa [hd] using hl.2)
    · subst step
      have hd : destination n s.position (n-3)=0 := by rw [hc.position]; exact back_dest (by omega) (by have := hc.bound; omega)
      exact hc.zero (by simpa [hd] using hl.2)
  | succ k ih =>
    intro n s hc
    have hH : 7≤4*(k+1)+3 := by omega
    apply Outcome.lose
    intro step hl
    rcases option_cases hl with he | he
    · subst step
      have hd : destination n s.position 1=4*(k+1)+3+1 := by
        rw [hc.position]; exact one_dest (by have := hc.bound; omega)
      exact False.elim (hc.next (by simpa [hd] using hl.2))
    · subst step
      apply back_child hH hc.bound hc.position hc.nodup hc.zero hc.here hc.fresh
      intro t ht
      have he : 4*(k+1)+3-4=4*k+3 := by omega
      exact ih n t (by simpa only [he] using ht)

theorem open_outcome (k : Nat) : ∀ n s,
    Open n (4*k+3) s → Outcome n [1,n-3] s false := by
  induction k with
  | zero =>
    intro n s ho
    change Open n 3 s at ho
    have hb := ho.bound
    apply Outcome.lose
    intro step hl
    rcases option_cases hl with he | he
    · subst step
      have hd : destination n s.position 1=4 := by rw [ho.position]; exact one_dest (by omega)
      rw [move_eq_visit ho.nodup, hd]
      apply win_visit (visit_nodup ho.nodup _) (by simp)
        (show destination n (visit s 4).position 1=5 by rw [visit_position]; exact one_dest (by omega))
      · simp only [visit_mem]; exact ⟨ho.nextTwo, by omega⟩
      · apply terminal_outcome
        intro step hl
        rcases option_cases hl with he | he
        · subst step
          have hd : destination n (visit (visit s 4) 5).position 1=6 := by rw [visit_position]; exact one_dest (by omega)
          have hf := hl.2
          rw [hd] at hf
          simp only [visit_mem] at hf
          exact ho.third hf.1.1
        · subst step
          have hd : destination n (visit (visit s 4) 5).position (n-3)=2 := by rw [visit_position]; exact back_dest (by omega) (by omega)
          have hf := hl.2
          rw [hd] at hf
          simp only [visit_mem] at hf
          exact ho.two hf.1.1
    · subst step
      have hd : destination n s.position (n-3)=0 := by rw [ho.position]; exact back_dest (by omega) (by omega)
      exact False.elim (ho.zero (by simpa [hd] using hl.2))
  | succ k ih =>
    intro n s ho
    let H := 4*(k+1)+3
    change Open n H s at ho
    have hH : 7≤H := by dsimp [H] <;> omega
    have hb := ho.bound
    have hC : ∀ t, Closed n (H-4) t → Outcome n [1,n-3] t false := by
      intro t ht
      have he : H-4=4*k+3 := by dsimp [H] <;> omega
      exact closed_outcome k n t (by simpa only [he] using ht)
    apply Outcome.lose
    intro step hl
    rcases option_cases hl with he | he
    · subst step
      have hd : destination n s.position 1=H+1 := by rw [ho.position]; exact one_dest (by omega)
      rw [move_eq_visit ho.nodup, hd]
      apply win_visit (visit_nodup ho.nodup _) (by simp)
        (show destination n (visit s (H+1)).position 1=H+2 by
          rw [visit_position, one_dest (by omega)] <;> omega)
      · simp only [visit_mem]; exact ⟨ho.nextTwo, by omega⟩
      · apply Outcome.lose
        intro step hl
        rcases option_cases hl with he | he
        · subst step
          have hd : destination n (visit (visit s (H+1)) (H+2)).position 1=H+3 := by
            rw [visit_position, one_dest (by omega)] <;> omega
          have hf := hl.2
          rw [hd] at hf
          simp only [visit_mem] at hf
          exact False.elim (ho.third hf.1.1)
        · subst step
          have hd : destination n (visit (visit s (H+1)) (H+2)).position (n-3)=H-1 := by
            rw [visit_position, back_dest (by omega) (by omega)] <;> omega
          rw [move_eq_visit (by simp [ho.nodup]), hd]
          apply win_visit (visit_nodup (visit_nodup (visit_nodup ho.nodup _) _) _) (by simp)
            (show destination n (visit (visit (visit s (H+1)) (H+2)) (H-1)).position (n-3)=H-4 by
              rw [visit_position, back_dest (by omega) (by omega)] <;> omega)
          · simp only [visit_mem]
            exact ⟨⟨⟨ho.fresh _ (by omega) (by omega), by omega⟩, by omega⟩, by omega⟩
          · apply ih n
            have he : 4*k+3=H-4 := by dsimp [H] <;> omega
            rw [he]
            refine ⟨by omega, by omega, rfl, visit_nodup (visit_nodup (visit_nodup (visit_nodup ho.nodup _) _) _) _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [visit_mem]; intro h; exact ho.zero h.1.1.1.1
            · simp only [visit_mem]; intro h; exact ho.one h.1.1.1.1
            · simp only [visit_mem]; intro h; exact ho.two h.1.1.1.1
            · simp
            · simp only [visit_mem]
              intro h; have hh : H-4+3=H-1 := by omega
              exact h.1.2 hh
            · intro x hx hx'
              simp only [visit_mem]
              exact ⟨⟨⟨⟨ho.fresh _ hx (by omega), by omega⟩, by omega⟩, by omega⟩, by omega⟩
            · simp only [visit_mem]
              have hh : H-4+1=H-3 := by omega
              exact ⟨⟨⟨⟨ho.fresh _ (by omega) (by omega), by omega⟩, by omega⟩, by omega⟩, by omega⟩
            · simp only [visit_mem]
              exact ⟨⟨⟨⟨ho.fresh _ (by omega) (by omega), by omega⟩, by omega⟩, by omega⟩, by omega⟩
    · subst step
      apply back_child hH (by omega) ho.position ho.nodup ho.zero ho.here
      · intro x hx hx'; exact ho.fresh x hx (by omega)
      · exact hC

/-- An actual fully marked prefix, with every greater bounded vertex fresh. -/
structure Prefix (n d : Nat) (s : State) : Prop where
  low : 3≤d
  bound : d<n
  position : s.position=d
  nodup : s.available.Nodup
  available : ∀ x, x ∈ s.available ↔ d<x ∧ x<n

theorem prefix_outcome (r : Nat) : ∀ n d s,
    Prefix n d s → n=d+r+1 →
    Outcome n [1,n-3] s (decide (r%2=1)) := by
  induction r with
  | zero =>
    intro n d s hp he
    simp only [Nat.zero_mod, Nat.zero_ne_one, decide_false]
    apply terminal_outcome
    intro step hl
    rcases option_cases hl with hh | hh
    · subst step
      have hd : destination n s.position 1=0 := by rw [hp.position]; unfold destination; rw [show d+1=n by omega]; exact Nat.mod_self _
      have hx := (hp.available _).mp (by simpa [hd] using hl.2)
      omega
    · subst step
      have hd : destination n s.position (n-3)=d-3 := by rw [hp.position]; exact back_dest hp.low hp.bound
      have hx := (hp.available _).mp (by simpa [hd] using hl.2)
      omega
  | succ r ih =>
    intro n d s hp he
    have hb := hp.bound
    have hd := hp.low
    have hdest : destination n s.position 1=d+1 := by rw [hp.position]; exact one_dest (by omega)
    have hlegal : Legal n [1,n-3] s 1 := ⟨by simp, by rw [hdest, hp.available] <;> omega⟩
    have hforced : ∀ step, Legal n [1,n-3] s step → step=1 := by
      intro step hl
      rcases option_cases hl with hh | hh
      · exact hh
      · subst step
        have hback : destination n s.position (n-3)=d-3 := by rw [hp.position]; exact back_dest hd hb
        have hx := (hp.available _).mp (by simpa [hback] using hl.2)
        omega
    have hnext : Prefix n (d+1) (move n s 1) := by
      rw [move_eq_visit hp.nodup, hdest]
      refine ⟨by omega, by omega, rfl, by simp [hp.nodup], ?_⟩
      intro x
      simp only [visit_mem, hp.available]
      omega
    have hc := ih n (d+1) (move n s 1) hnext (by omega)
    have hpar : decide ((r+1)%2=1)= !(decide (r%2=1)) := by
      have := Nat.mod_lt r (by omega : 0<2)
      by_cases h : r%2=0 <;> simp_all <;> omega
    rw [hpar]
    exact forced_outcome hlegal hforced hc

@[simp] theorem initial_mem {n x : Nat} :
    x ∈ (initial n).available ↔ x<n ∧ x≠0 := by
  simp only [initial, List.Nodup.mem_erase_iff List.nodup_range, List.mem_range]
  exact and_comm

/-- Every board n≥5 with n≡3 mod4 is an actual initially marked P-position. -/
theorem losing_initial_outcome {n : Nat} (hn : 5≤n) (hr : n%4=3) :
    Outcome n [1,n-3] (initial n) false := by
  have hn7 : 7≤n := by omega
  let k := n/4-1
  have he : n=4*k+7 := by dsimp [k]; omega
  have hC : ∀ s, Closed n (n-4) s → Outcome n [1,n-3] s false := by
    intro s hs
    have hh : n-4=4*k+3 := by omega
    exact closed_outcome k n s (by simpa only [hh] using hs)
  have hO : ∀ s, Open n (n-4) s → Outcome n [1,n-3] s false := by
    intro s hs
    have hh : n-4=4*k+3 := by omega
    exact open_outcome k n s (by simpa only [hh] using hs)
  have hi : (initial n).available.Nodup := (initial_represents n).1
  apply Outcome.lose
  intro step hl
  rcases option_cases hl with hh | hh
  · subst step
    have hd : destination n (initial n).position 1=1 := by
      change (0+1)%n=1
      exact Nat.mod_eq_of_lt (by omega)
    rw [move_eq_visit hi, hd]
    apply win_visit (visit_nodup hi _) (by simp)
      (show destination n (visit (initial n) 1).position 1=2 by
        rw [visit_position]; exact one_dest (by omega))
    · simp only [visit_mem, initial_mem]; omega
    · apply Outcome.lose
      intro step hl
      rcases option_cases hl with hh | hh
      · subst step
        have hd : destination n (visit (visit (initial n) 1) 2).position 1=3 := by
          rw [visit_position]; exact one_dest (by omega)
        rw [move_eq_visit (visit_nodup (visit_nodup hi _) _), hd]
        have hp : Prefix n 3 (visit (visit (visit (initial n) 1) 2) 3) := by
          refine ⟨by omega, by omega, rfl, visit_nodup (visit_nodup (visit_nodup hi _) _) _, ?_⟩
          intro x
          simp only [visit_mem, initial_mem]
          omega
        have hpout := prefix_outcome (n-4) n 3 _ hp (by omega)
        have hpar : decide ((n-4)%2=1)=true := by
          have hodd : (n-4)%2=1 := by omega
          simp [hodd]
        simpa only [hpar] using hpout
      · subst step
        have hd : destination n (visit (visit (initial n) 1) 2).position (n-3)=n-1 := by
          rw [visit_position]
          unfold destination
          rw [show 2+(n-3)=n-1 by omega]
          exact Nat.mod_eq_of_lt (by omega)
        rw [move_eq_visit (visit_nodup (visit_nodup hi _) _), hd]
        apply win_visit (visit_nodup (visit_nodup (visit_nodup hi _) _) _) (by simp)
          (show destination n (visit (visit (visit (initial n) 1) 2) (n-1)).position (n-3)=n-4 by
            rw [visit_position, back_dest (by omega) (by omega)] <;> omega)
        · simp only [visit_mem, initial_mem]; omega
        · apply hO
          refine ⟨by omega, by omega, rfl, visit_nodup (visit_nodup (visit_nodup (visit_nodup hi _) _) _) _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp
          · simp
          · simp
          · simp
          · simp only [visit_mem, initial_mem]; omega
          · intro x hx hb
            simp only [visit_mem, initial_mem]
            omega
          · simp only [visit_mem, initial_mem]; omega
          · simp only [visit_mem, initial_mem]; omega
  · subst step
    have hd : destination n (initial n).position (n-3)=n-3 := by
      change (0+(n-3))%n=n-3
      simpa only [Nat.zero_add] using Nat.mod_eq_of_lt (show n-3<n by omega)
    rw [move_eq_visit hi, hd]
    apply win_visit (visit_nodup hi _) (by simp)
      (show destination n (visit (initial n) (n-3)).position 1=n-2 by
        rw [visit_position, one_dest (by omega)] <;> omega)
    · simp only [visit_mem, initial_mem]; omega
    · apply middle_outcome (ih := hC)
      refine ⟨hn7, by omega, rfl, by simp [hi], ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · simp
      · simp
      · intro x hx hb
        simp only [visit_mem, initial_mem]
        omega

#print axioms closed_outcome
#print axioms open_outcome
#print axioms prefix_outcome
#print axioms losing_initial_outcome

end Kotzig.FourEighteenLosing
