import Kotzig.GameSemantics

namespace Kotzig.FourEighteenEven

structure Paired (n : Nat) (s : State) : Prop where
  positionOdd : s.position % 2 = 1
  nodup : s.available.Nodup
  pairs : ∀ x, x < n → x % 2 = 0 → (x ∈ s.available ↔ x+1 ∈ s.available)

theorem landing_even {n s step} (hn : 5 ≤ n) (he : n % 2 = 0)
    (hp : s.position % 2 = 1) (hl : Legal n [1,n-3] s step) :
    destination n s.position step % 2 = 0 := by
  have hd : 2 ∣ n := Nat.dvd_of_mod_eq_zero he
  rw [destination, Nat.mod_mod_of_dvd _ hd, Nat.add_mod]
  have hm : step = 1 ∨ step = n-3 := by simpa [Legal] using hl.1
  rcases hm with rfl | rfl
  · simp [hp]
  · have hs : (n-3)%2 = 1 := by omega
    simp [hp,hs]

theorem reply_legal {n s step} (hn : 5 ≤ n) (he : n % 2 = 0)
    (hs : Paired n s) (hl : Legal n [1,n-3] s step) :
    Legal n [1,n-3] (move n s step) 1 := by
  let e := destination n s.position step
  have hb : e < n := Nat.mod_lt _ (by omega)
  have hp : e%2=0 := landing_even hn he hs.positionOdd hl
  have hm : e+1 ∈ s.available := (hs.pairs e hb hp).mp hl.2
  have hnext : destination n (move n s step).position 1 = e+1 := by
    exact Nat.mod_eq_of_lt (by omega : e+1 < n)
  refine ⟨by simp, ?_⟩
  rw [hnext]
  change e+1 ∈ s.available.erase e
  rw [List.Nodup.mem_erase_iff hs.nodup]
  exact ⟨by omega,hm⟩

theorem paired_reply {n s step} (hn : 5 ≤ n) (he : n % 2 = 0)
    (hs : Paired n s) (hl : Legal n [1,n-3] s step) :
    Paired n (move n (move n s step) 1) := by
  let e := destination n s.position step
  have hb : e < n := Nat.mod_lt _ (by omega)
  have hp : e%2=0 := landing_even hn he hs.positionOdd hl
  have hnext : destination n (move n s step).position 1 = e+1 :=
    Nat.mod_eq_of_lt (by omega : e+1 < n)
  refine ⟨?_, (hs.nodup.erase _).erase _, ?_⟩
  · change destination n (move n s step).position 1 % 2 = 1
    rw [hnext]; omega
  · intro x hx hxp
    change (x ∈ (s.available.erase e).erase (destination n (move n s step).position 1) ↔
      x+1 ∈ (s.available.erase e).erase (destination n (move n s step).position 1))
    rw [hnext]
    simp only [List.Nodup.mem_erase_iff (hs.nodup.erase e), List.Nodup.mem_erase_iff hs.nodup]
    have hpair := hs.pairs x hx hxp
    have hcross1 : x ≠ e+1 := by omega
    have hcross2 : x+1 ≠ e := by omega
    constructor
    · intro h; exact ⟨by omega,hcross2,hpair.mp h.2.2⟩
    · intro h; exact ⟨hcross1,by omega,hpair.mpr h.2.2⟩

/-- At the opponent's turns, each fresh even landing has a fresh odd mate. -/
theorem paired_outcome {n : Nat} (hn : 5 ≤ n) (he : n%2=0) :
    ∀ s, Paired n s → Outcome n [1,n-3] s false := by
  have aux : ∀ r s, s.available.length = r → Paired n s → Outcome n [1,n-3] s false := by
    intro r
    induction r using Nat.strongRecOn with
    | ind r ih =>
      intro s hr hs
      apply Outcome.lose
      intro step hl
      have hl1 := reply_legal hn he hs hl
      apply Outcome.win hl1
      have h1 := move_length hl
      have h2 := move_length hl1
      have hlt : (move n (move n s step) 1).available.length < r := by omega
      exact ih _ hlt _ rfl (paired_reply hn he hs hl)
  intro s hs
  exact aux s.available.length s rfl hs

theorem even_initial_outcome {n : Nat} (hn : 5 ≤ n) (he : n%2=0) :
    Outcome n [1,n-3] (initial n) true := by
  have hd : destination n (initial n).position 1 = 1 := by
    change 1 % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hr := initial_represents n
  have hl : Legal n [1,n-3] (initial n) 1 := by
    refine ⟨by simp, ?_⟩
    rw [hd,hr.2]
    simp; omega
  apply Outcome.win hl
  apply paired_outcome hn he
  refine ⟨?_,hr.1.erase _,?_⟩
  · change destination n (initial n).position 1 %2=1
    rw [hd]
  · intro x hx hp
    change x ∈ (initial n).available.erase (destination n (initial n).position 1) ↔ x+1 ∈ (initial n).available.erase (destination n (initial n).position 1)
    rw [hd]
    simp only [List.Nodup.mem_erase_iff hr.1,hr.2]
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    omega

#print axioms even_initial_outcome
end Kotzig.FourEighteenEven
