import Kotzig.GameSemantics

namespace Kotzig.FourEighteenWinning

def land (s : State) (q : Nat) : State := ⟨q,s.available.erase q⟩

theorem land_nodup {s q} (h : s.available.Nodup) : (land s q).available.Nodup := h.erase q

theorem land_mem {s q x} (h : s.available.Nodup) :
    x ∈ (land s q).available ↔ x ≠ q ∧ x ∈ s.available :=
  List.Nodup.mem_erase_iff h

theorem move_land {n s step q} (h : destination n s.position step = q) :
    move n s step = land s q := by simp [move,land,h]

theorem dest_one {n x : Nat} {s : State} (hp : s.position=x) (hb : x+1<n) :
    destination n s.position 1=x+1 := by simp [destination,hp,Nat.mod_eq_of_lt hb]

theorem dest_back {n x : Nat} {s : State} (hp : s.position=x) (hl : 3≤x) (hb : x<n) :
    destination n s.position (n-3)=x-3 := by
  unfold destination
  rw [hp]
  have he : x+(n-3)=(x-3)+n := by omega
  rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega : x-3<n)]

theorem legal_one {n s q} (hd : destination n s.position 1=q)
    (hf : q∈s.available) : Legal n [1,n-3] s 1 := ⟨by simp,by simpa [hd] using hf⟩

theorem legal_back {n s q} (hd : destination n s.position (n-3)=q)
    (hf : q∈s.available) : Legal n [1,n-3] s (n-3) := ⟨by simp,by simpa [hd] using hf⟩

theorem legal_cases {n s step} (h : Legal n [1,n-3] s step) :
    step=1 ∨ step=n-3 := by simpa [Legal] using h.1

theorem terminal {n s q r}
    (h1 : destination n s.position 1=q) (hb : destination n s.position (n-3)=r)
    (hq : q∉s.available) (hr : r∉s.available) : Outcome n [1,n-3] s false := by
  apply Outcome.lose
  intro step hl
  rcases legal_cases hl with he | he
  · subst step; exact False.elim (hq (by simpa [h1] using hl.2))
  · subst step; exact False.elim (hr (by simpa [hb] using hl.2))

theorem forced_back {n s q r}
    (h1 : destination n s.position 1=q) (hb : destination n s.position (n-3)=r)
    (hq : q∉s.available) (_hr : r∈s.available)
    (ho : Outcome n [1,n-3] (land s r) true) : Outcome n [1,n-3] s false := by
  apply Outcome.lose
  intro step hl
  rcases legal_cases hl with he | he
  · subst step; exact False.elim (hq (by simpa [h1] using hl.2))
  · subst step; rw [move_land hb]; exact ho

structure Drop (n H : Nat) (s : State) : Prop where
  depth : 5≤H
  bound : H+3<n
  position : s.position=H
  nodup : s.available.Nodup
  zero : 0∉s.available
  one : 1∉s.available
  current : H∉s.available
  two : H+2∉s.available
  three : H+3∉s.available
  fresh : ∀x, 3≤x → x≤H-1 → x∈s.available
  next : H+1∈s.available

structure Open (n H : Nat) (s : State) : Prop where
  depth : 5≤H
  bound : H+3<n
  position : s.position=H
  nodup : s.available.Nodup
  zero : 0∉s.available
  one : 1∉s.available
  two : 2∉s.available
  current : H∉s.available
  three : H+3∉s.available
  fresh : ∀x, 3≤x → x≤H-1 → x∈s.available
  next : H+1∈s.available
  nextTwo : H+2∈s.available

def run4 (s : State) (a b c d : Nat) : State := land (land (land (land s a) b) c) d

theorem run4_nodup {s a b c d} (h : s.available.Nodup) :
    (run4 s a b c d).available.Nodup :=
  land_nodup (land_nodup (land_nodup (land_nodup h)))

theorem run4_mem {s a b c d x} (h : s.available.Nodup) :
    x∈(run4 s a b c d).available ↔ x≠d ∧ x≠c ∧ x≠b ∧ x≠a ∧ x∈s.available := by
  unfold run4
  rw [land_mem (land_nodup (land_nodup (land_nodup h))),
    land_mem (land_nodup (land_nodup h)),land_mem (land_nodup h),land_mem h]

theorem drop_descent {n H s} (hs : Drop n H s) (hh : 9≤H) :
    Drop n (H-4) (run4 s (H+1) (H-2) (H-1) (H-4)) := by
  have hm := fun x => run4_mem (x:=x) (a:=H+1) (b:=H-2) (c:=H-1) (d:=H-4) hs.nodup
  refine ⟨by omega,by have := hs.bound; omega,rfl,run4_nodup hs.nodup,?_,?_,?_,?_,?_,?_,?_⟩
  · intro hx; exact hs.zero (((hm _).mp hx).2.2.2.2)
  · intro hx; exact hs.one (((hm _).mp hx).2.2.2.2)
  · intro hx; exact ((hm _).mp hx).1 rfl
  · intro hx; exact ((hm _).mp hx).2.2.1 (by omega)
  · intro hx; exact ((hm _).mp hx).2.1 (by omega)
  · intro x hx hy
    apply (hm _).mpr
    exact ⟨by omega,by omega,by omega,by omega,hs.fresh x hx (by omega)⟩
  · apply (hm _).mpr
    exact ⟨by omega,by omega,by omega,by omega,hs.fresh _ (by omega) (by omega)⟩

theorem drop_outcome_aux (k : Nat) : ∀ n s, Drop n (4*k+5) s →
    Outcome n [1,n-3] s true := by
  induction k with
  | zero =>
    intro n s hs
    have hH : 4*0+5=5 := by omega
    rw [hH] at hs
    let s1 := land s 6
    let s2 := land s1 3
    let s3 := land s2 4
    have hn1 : s1.available.Nodup := land_nodup hs.nodup
    have hn2 : s2.available.Nodup := land_nodup hn1
    have hm1 := fun x => land_mem (s:=s) (q:=6) (x:=x) hs.nodup
    have hm2 := fun x => land_mem (s:=s1) (q:=3) (x:=x) hn1
    have hm3 := fun x => land_mem (s:=s2) (q:=4) (x:=x) hn2
    have hf3 : 3∈s1.available := (hm1 _).mpr ⟨by omega,hs.fresh 3 (by omega) (by omega)⟩
    have hf4 : 4∈s2.available := (hm2 _).mpr ⟨by omega,(hm1 _).mpr ⟨by omega,hs.fresh 4 (by omega) (by omega)⟩⟩
    have ht5 : 5∉s3.available := by intro h; exact hs.current ((hm1 _).mp ((hm2 _).mp ((hm3 _).mp h).2).2).2
    have ht1 : 1∉s3.available := by intro h; exact hs.one ((hm1 _).mp ((hm2 _).mp ((hm3 _).mp h).2).2).2
    have ho3 : Outcome n [1,n-3] s3 false := terminal
      (dest_one (n:=n) (s:=s3) (x:=4) rfl (by have := hs.bound; omega))
      (dest_back (n:=n) (s:=s3) (x:=4) rfl (by omega) (by have := hs.bound; omega)) ht5 ht1
    have ho2 : Outcome n [1,n-3] s2 true := by
      have hd := dest_one (n:=n) (s:=s2) (x:=3) rfl (by have := hs.bound; omega)
      apply Outcome.win (legal_one hd hf4)
      rw [move_land hd]
      exact ho3
    have ht7 : 7∉s1.available := by intro h; exact hs.two ((hm1 _).mp h).2
    have ho1 : Outcome n [1,n-3] s1 false := forced_back
      (dest_one (n:=n) (s:=s1) (x:=6) rfl (by have := hs.bound; omega))
      (dest_back (n:=n) (s:=s1) (x:=6) rfl (by omega) (by have := hs.bound; omega)) ht7 hf3 ho2
    have hd := dest_one (n:=n) (x:=5) hs.position (by have := hs.bound; omega)
    apply Outcome.win (legal_one hd hs.next)
    rw [move_land hd]
    exact ho1
  | succ k ih =>
    intro n s hs
    let H := 4*(k+1)+5
    have hH : 4*(k+1)+5=H := rfl
    change Drop n H s at hs
    have hh : 9≤H := by dsimp [H]; omega
    let s1 := land s (H+1)
    let s2 := land s1 (H-2)
    let s3 := land s2 (H-1)
    have hn1 : s1.available.Nodup := land_nodup hs.nodup
    have hn2 : s2.available.Nodup := land_nodup hn1
    have hm1 := fun x => land_mem (s:=s) (q:=H+1) (x:=x) hs.nodup
    have hm2 := fun x => land_mem (s:=s1) (q:=H-2) (x:=x) hn1
    have hm3 := fun x => land_mem (s:=s2) (q:=H-1) (x:=x) hn2
    have hf2 : H-2∈s1.available := (hm1 _).mpr ⟨by omega,hs.fresh _ (by omega) (by omega)⟩
    have hf1 : H-1∈s2.available := (hm2 _).mpr ⟨by omega,(hm1 _).mpr ⟨by omega,hs.fresh _ (by omega) (by omega)⟩⟩
    have hf4 : H-4∈s3.available := (hm3 _).mpr ⟨by omega,(hm2 _).mpr ⟨by omega,(hm1 _).mpr ⟨by omega,hs.fresh _ (by omega) (by omega)⟩⟩⟩
    have htH : H∉s3.available := by intro h; exact hs.current ((hm1 _).mp ((hm2 _).mp ((hm3 _).mp h).2).2).2
    have hc := drop_descent hs hh
    have he : H-4=4*k+5 := by dsimp [H]; omega
    rw [he] at hc
    have ho4 := ih n _ hc
    have ho3 : Outcome n [1,n-3] s3 false := forced_back
      (dest_one (n:=n) (s:=s3) (x:=H-1) rfl (by have := hs.bound; omega))
      (dest_back (n:=n) (s:=s3) (x:=H-1) rfl (by omega) (by have := hs.bound; omega)) htH hf4 ho4
    have ho2 : Outcome n [1,n-3] s2 true := by
      have hd := dest_one (n:=n) (s:=s2) (x:=H-2) rfl (by have := hs.bound; omega)
      apply Outcome.win (legal_one hd hf1)
      rw [move_land hd]
      exact ho3
    have ht2 : H+2∉s1.available := by intro h; exact hs.two ((hm1 _).mp h).2
    have ho1 : Outcome n [1,n-3] s1 false := forced_back
      (dest_one (n:=n) (s:=s1) (x:=H+1) rfl (by have := hs.bound; omega))
      (dest_back (n:=n) (s:=s1) (x:=H+1) rfl (by omega) (by have := hs.bound; omega)) ht2 hf2 ho2
    have hd := dest_one (n:=n) (x:=H) hs.position (by have := hs.bound; omega)
    apply Outcome.win (legal_one hd hs.next)
    rw [move_land hd]
    exact ho1

theorem drop_outcome {n H s} (hs : Drop n H s) (hp : H%4=1) :
    Outcome n [1,n-3] s true := by
  have he : H=4*((H-5)/4)+5 := by have := hs.depth; omega
  have ho := drop_outcome_aux ((H-5)/4) n s
  rw [←he] at ho
  exact ho hs

theorem open_open_descent {n H s} (hs : Open n H s) (hh : 9≤H) :
    Open n (H-4) (run4 s (H+1) (H+2) (H-1) (H-4)) := by
  have hm := fun x => run4_mem (x:=x) (a:=H+1) (b:=H+2) (c:=H-1) (d:=H-4) hs.nodup
  refine ⟨by omega,by have := hs.bound; omega,rfl,run4_nodup hs.nodup,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro hx; exact hs.zero ((hm _).mp hx).2.2.2.2
  · intro hx; exact hs.one ((hm _).mp hx).2.2.2.2
  · intro hx; exact hs.two ((hm _).mp hx).2.2.2.2
  · intro hx; exact ((hm _).mp hx).1 rfl
  · intro hx; exact ((hm _).mp hx).2.1 (by omega)
  · intro x hx hy
    exact (hm _).mpr ⟨by omega,by omega,by omega,by omega,hs.fresh _ hx (by omega)⟩
  · exact (hm _).mpr ⟨by omega,by omega,by omega,by omega,hs.fresh _ (by omega) (by omega)⟩
  · exact (hm _).mpr ⟨by omega,by omega,by omega,by omega,hs.fresh _ (by omega) (by omega)⟩

theorem open_drop_descent {n H s} (hs : Open n H s) (hh : 9≤H) :
    Drop n (H-4) (run4 s (H+1) (H-2) (H-1) (H-4)) := by
  have hm := fun x => run4_mem (x:=x) (a:=H+1) (b:=H-2) (c:=H-1) (d:=H-4) hs.nodup
  refine ⟨by omega,by have := hs.bound; omega,rfl,run4_nodup hs.nodup,?_,?_,?_,?_,?_,?_,?_⟩
  · intro hx; exact hs.zero ((hm _).mp hx).2.2.2.2
  · intro hx; exact hs.one ((hm _).mp hx).2.2.2.2
  · intro hx; exact ((hm _).mp hx).1 rfl
  · intro hx; exact ((hm _).mp hx).2.2.1 (by omega)
  · intro hx; exact ((hm _).mp hx).2.1 (by omega)
  · intro x hx hy
    exact (hm _).mpr ⟨by omega,by omega,by omega,by omega,hs.fresh _ hx (by omega)⟩
  · exact (hm _).mpr ⟨by omega,by omega,by omega,by omega,hs.fresh _ (by omega) (by omega)⟩

theorem open_base {n s} (hs : Open n 5 s) : Outcome n [1,n-3] s true := by
  let s1 := land s 6
  have hn1 : s1.available.Nodup := land_nodup hs.nodup
  have hm1 := fun x => land_mem (s:=s) (q:=6) (x:=x) hs.nodup
  have finish : ∀ q, q=7 ∨ q=3 → Outcome n [1,n-3] (land s1 q) true := by
    intro q hq
    have hq4 : q≠4 := by rcases hq with h | h <;> omega
    let s2 := land s1 q
    let s3 := land s2 4
    have hn2 : s2.available.Nodup := land_nodup hn1
    have hm2 := fun x => land_mem (s:=s1) (q:=q) (x:=x) hn1
    have hm3 := fun x => land_mem (s:=s2) (q:=4) (x:=x) hn2
    have hf4 : 4∈s2.available := (hm2 _).mpr ⟨by omega,(hm1 _).mpr ⟨by omega,hs.fresh _ (by omega) (by omega)⟩⟩
    have ht5 : 5∉s3.available := by intro h; exact hs.current ((hm1 _).mp ((hm2 _).mp ((hm3 _).mp h).2).2).2
    have ht1 : 1∉s3.available := by intro h; exact hs.one ((hm1 _).mp ((hm2 _).mp ((hm3 _).mp h).2).2).2
    have ho3 : Outcome n [1,n-3] s3 false := terminal
      (dest_one (n:=n) (s:=s3) (x:=4) rfl (by have := hs.bound; omega))
      (dest_back (n:=n) (s:=s3) (x:=4) rfl (by omega) (by have := hs.bound; omega)) ht5 ht1
    rcases hq with hq | hq
    · have hp : s2.position=7 := hq
      have hd : destination n s2.position (n-3)=4 := dest_back hp (by omega) (by have := hs.bound; omega)
      apply Outcome.win (legal_back hd hf4)
      rw [move_land hd]; exact ho3
    · have hp : s2.position=3 := hq
      have hd : destination n s2.position 1=4 := dest_one hp (by have := hs.bound; omega)
      apply Outcome.win (legal_one hd hf4)
      rw [move_land hd]; exact ho3
  have hd := dest_one (n:=n) hs.position (by have := hs.bound; omega)
  apply Outcome.win (legal_one hd hs.next)
  rw [move_land hd]
  apply Outcome.lose
  intro step hl
  rcases legal_cases hl with he | he
  · subst step
    have hd : destination n s1.position 1=7 := dest_one (x:=6) rfl (by have := hs.bound; omega)
    rw [move_land hd]; exact finish 7 (Or.inl rfl)
  · subst step
    have hd : destination n s1.position (n-3)=3 := dest_back (x:=6) rfl (by omega) (by have := hs.bound; omega)
    rw [move_land hd]; exact finish 3 (Or.inr rfl)

theorem open_outcome_aux (k : Nat) : ∀ n s, Open n (4*k+5) s →
    Outcome n [1,n-3] s true := by
  induction k with
  | zero => intro n s hs; exact open_base hs
  | succ k ih =>
    intro n s hs
    let H := 4*(k+1)+5
    change Open n H s at hs
    have hh : 9≤H := by dsimp [H]; omega
    have he : H-4=4*k+5 := by dsimp [H]; omega
    let s1 := land s (H+1)
    have hn1 : s1.available.Nodup := land_nodup hs.nodup
    have hm1 := fun x => land_mem (s:=s) (q:=H+1) (x:=x) hs.nodup
    have hd := dest_one (n:=n) hs.position (by have := hs.bound; omega)
    apply Outcome.win (legal_one hd hs.next)
    rw [move_land hd]
    apply Outcome.lose
    intro step hl
    rcases legal_cases hl with ht | ht
    · subst step
      have hd2 : destination n s1.position 1=H+2 :=
        dest_one (x:=H+1) rfl (by have := hs.bound; omega)
      rw [move_land hd2]
      let s2 := land s1 (H+2)
      let s3 := land s2 (H-1)
      have hn2 : s2.available.Nodup := land_nodup hn1
      have hm2 := fun x => land_mem (s:=s1) (q:=H+2) (x:=x) hn1
      have hm3 := fun x => land_mem (s:=s2) (q:=H-1) (x:=x) hn2
      have hf1 : H-1∈s2.available := (hm2 _).mpr ⟨by omega,(hm1 _).mpr ⟨by omega,hs.fresh _ (by omega) (by omega)⟩⟩
      have hf4 : H-4∈s3.available := (hm3 _).mpr ⟨by omega,(hm2 _).mpr ⟨by omega,(hm1 _).mpr ⟨by omega,hs.fresh _ (by omega) (by omega)⟩⟩⟩
      have htH : H∉s3.available := by intro h; exact hs.current ((hm1 _).mp ((hm2 _).mp ((hm3 _).mp h).2).2).2
      have hc := open_open_descent hs hh
      rw [he] at hc
      have ho4 := ih n _ hc
      have ho3 : Outcome n [1,n-3] s3 false := forced_back
        (dest_one (n:=n) (s:=s3) (x:=H-1) rfl (by have := hs.bound; omega))
        (dest_back (n:=n) (s:=s3) (x:=H-1) rfl (by omega) (by have := hs.bound; omega)) htH hf4 ho4
      have hd3 : destination n s2.position (n-3)=H-1 := by
        have hd := dest_back (n:=n) (s:=s2) (x:=H+2) rfl (by omega) (by have := hs.bound; omega)
        have heq : H+2-3=H-1 := by omega
        simpa [heq] using hd
      apply Outcome.win (legal_back hd3 hf1)
      rw [move_land hd3]
      exact ho3
    · subst step
      have hd2 : destination n s1.position (n-3)=H-2 := by
        have hd := dest_back (n:=n) (s:=s1) (x:=H+1) rfl (by omega) (by have := hs.bound; omega)
        have heq : H+1-3=H-2 := by omega
        simpa [heq] using hd
      rw [move_land hd2]
      let s2 := land s1 (H-2)
      let s3 := land s2 (H-1)
      have hn2 : s2.available.Nodup := land_nodup hn1
      have hm2 := fun x => land_mem (s:=s1) (q:=H-2) (x:=x) hn1
      have hm3 := fun x => land_mem (s:=s2) (q:=H-1) (x:=x) hn2
      have hf1 : H-1∈s2.available := (hm2 _).mpr ⟨by omega,(hm1 _).mpr ⟨by omega,hs.fresh _ (by omega) (by omega)⟩⟩
      have hf4 : H-4∈s3.available := (hm3 _).mpr ⟨by omega,(hm2 _).mpr ⟨by omega,(hm1 _).mpr ⟨by omega,hs.fresh _ (by omega) (by omega)⟩⟩⟩
      have htH : H∉s3.available := by intro h; exact hs.current ((hm1 _).mp ((hm2 _).mp ((hm3 _).mp h).2).2).2
      have hc := open_drop_descent hs hh
      rw [he] at hc
      have ho4 := drop_outcome_aux k n _ hc
      have ho3 : Outcome n [1,n-3] s3 false := forced_back
        (dest_one (n:=n) (s:=s3) (x:=H-1) rfl (by have := hs.bound; omega))
        (dest_back (n:=n) (s:=s3) (x:=H-1) rfl (by omega) (by have := hs.bound; omega)) htH hf4 ho4
      have hd3 : destination n s2.position 1=H-1 := by
        have hd := dest_one (n:=n) (s:=s2) (x:=H-2) rfl (by have := hs.bound; omega)
        have heq : H-2+1=H-1 := by omega
        simpa [heq] using hd
      apply Outcome.win (legal_one hd3 hf1)
      rw [move_land hd3]
      exact ho3

theorem open_outcome {n H s} (hs : Open n H s) (hp : H%4=1) :
    Outcome n [1,n-3] s true := by
  have he : H=4*((H-5)/4)+5 := by have := hs.depth; omega
  have ho := open_outcome_aux ((H-5)/4) n s
  rw [←he] at ho
  exact ho hs

theorem initial_mem (n x : Nat) : x∈(initial n).available ↔ x<n ∧ x≠0 := by
  have hm := (initial_represents n).2 x
  simpa using hm

theorem initial_open {n : Nat} (hn : 9≤n) :
    Open n (n-4) (run4 (initial n) 1 2 (n-1) (n-4)) := by
  have hnd := (initial_represents n).1
  have hm := fun x => run4_mem (x:=x) (a:=1) (b:=2) (c:=n-1) (d:=n-4) hnd
  refine ⟨by omega,by omega,rfl,run4_nodup hnd,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro hx; have := ((initial_mem n 0).mp ((hm _).mp hx).2.2.2.2); omega
  · intro hx; exact ((hm _).mp hx).2.2.2.1 rfl
  · intro hx; exact ((hm _).mp hx).2.2.1 rfl
  · intro hx; exact ((hm _).mp hx).1 rfl
  · intro hx; exact ((hm _).mp hx).2.1 (by omega)
  · intro x hx hy
    apply (hm _).mpr
    exact ⟨by omega,by omega,by omega,by omega,(initial_mem n x).mpr ⟨by omega,by omega⟩⟩
  · exact (hm _).mpr ⟨by omega,by omega,by omega,by omega,(initial_mem n _).mpr ⟨by omega,by omega⟩⟩
  · exact (hm _).mpr ⟨by omega,by omega,by omega,by omega,(initial_mem n _).mpr ⟨by omega,by omega⟩⟩

theorem initial_drop {n : Nat} (hn : 9≤n) :
    Drop n (n-4) (run4 (initial n) 1 (n-2) (n-1) (n-4)) := by
  have hnd := (initial_represents n).1
  have hm := fun x => run4_mem (x:=x) (a:=1) (b:=n-2) (c:=n-1) (d:=n-4) hnd
  refine ⟨by omega,by omega,rfl,run4_nodup hnd,?_,?_,?_,?_,?_,?_,?_⟩
  · intro hx; have := ((initial_mem n 0).mp ((hm _).mp hx).2.2.2.2); omega
  · intro hx; exact ((hm _).mp hx).2.2.2.1 rfl
  · intro hx; exact ((hm _).mp hx).1 rfl
  · intro hx; exact ((hm _).mp hx).2.2.1 (by omega)
  · intro hx; exact ((hm _).mp hx).2.1 (by omega)
  · intro x hx hy
    exact (hm _).mpr ⟨by omega,by omega,by omega,by omega,(initial_mem n x).mpr ⟨by omega,by omega⟩⟩
  · exact (hm _).mpr ⟨by omega,by omega,by omega,by omega,(initial_mem n _).mpr ⟨by omega,by omega⟩⟩

theorem initial_large {n : Nat} (hn : 9≤n) (hp : n%4=1) :
    Outcome n [1,n-3] (initial n) true := by
  let s := initial n
  let s1 := land s 1
  have hn0 : s.available.Nodup := (initial_represents n).1
  have hn1 : s1.available.Nodup := land_nodup hn0
  have hm1 := fun x => land_mem (s:=s) (q:=1) (x:=x) hn0
  have finish : ∀ q, q=2 ∨ q=n-2 → Outcome n [1,n-3] (land s1 q) true := by
    intro q hq
    let s2 := land s1 q
    let s3 := land s2 (n-1)
    have hn2 : s2.available.Nodup := land_nodup hn1
    have hm2 := fun x => land_mem (s:=s1) (q:=q) (x:=x) hn1
    have hm3 := fun x => land_mem (s:=s2) (q:=n-1) (x:=x) hn2
    have hqbound : q<n-1 := by rcases hq with h | h <;> omega
    have hfend : n-1∈s2.available := (hm2 _).mpr ⟨by omega,(hm1 _).mpr ⟨by omega,(initial_mem n _).mpr ⟨by omega,by omega⟩⟩⟩
    have hf4 : n-4∈s3.available := by
      have hneq : n-4≠q := by rcases hq with h | h <;> omega
      exact (hm3 _).mpr ⟨by omega,(hm2 _).mpr ⟨hneq,(hm1 _).mpr ⟨by omega,(initial_mem n _).mpr ⟨by omega,by omega⟩⟩⟩⟩
    have ht0 : 0∉s3.available := by
      intro hx
      have hx0 := (initial_mem n 0).mp ((hm1 _).mp ((hm2 _).mp ((hm3 _).mp hx).2).2).2
      omega
    have hd1 : destination n s3.position 1=0 := by
      change ((n-1)+1)%n=0
      have he : n-1+1=n := by omega
      rw [he,Nat.mod_self]
    have hdb : destination n s3.position (n-3)=n-4 := by
      have hd := dest_back (n:=n) (s:=s3) (x:=n-1) rfl (by omega) (by omega)
      have he : n-1-3=n-4 := by omega
      simpa [he] using hd
    have hphase : (n-4)%4=1 := by omega
    have ho4 : Outcome n [1,n-3] (land s3 (n-4)) true := by
      rcases hq with hq | hq
      · subst q; exact open_outcome (initial_open hn) hphase
      · subst q; exact drop_outcome (initial_drop hn) hphase
    have ho3 : Outcome n [1,n-3] s3 false := forced_back hd1 hdb ht0 hf4 ho4
    rcases hq with hq | hq
    · have hd : destination n s2.position (n-3)=n-1 := by
        change (q+(n-3))%n=n-1
        have he : q+(n-3)=n-1 := by omega
        rw [he,Nat.mod_eq_of_lt (by omega : n-1<n)]
      apply Outcome.win (legal_back hd hfend)
      rw [move_land hd]; exact ho3
    · have hd : destination n s2.position 1=n-1 := by
        change (q+1)%n=n-1
        have he : q+1=n-1 := by omega
        rw [he,Nat.mod_eq_of_lt (by omega : n-1<n)]
      apply Outcome.win (legal_one hd hfend)
      rw [move_land hd]; exact ho3
  have hd : destination n s.position 1=1 := dest_one (x:=0) rfl (by omega)
  have hf : 1∈s.available := (initial_mem n 1).mpr ⟨by omega,by omega⟩
  apply Outcome.win (legal_one hd hf)
  rw [move_land hd]
  apply Outcome.lose
  intro step hl
  rcases legal_cases hl with ht | ht
  · subst step
    have hd2 : destination n s1.position 1=2 := dest_one (x:=1) rfl (by omega)
    rw [move_land hd2]; exact finish 2 (Or.inl rfl)
  · subst step
    have hd2 : destination n s1.position (n-3)=n-2 := by
      change (1+(n-3))%n=n-2
      have he : 1+(n-3)=n-2 := by omega
      rw [he,Nat.mod_eq_of_lt (by omega : n-2<n)]
    rw [move_land hd2]; exact finish (n-2) (Or.inr rfl)

theorem five_outcome : Outcome 5 [1,5-3] (initial 5) true := by
  have he : evaluate 5 [1,5-3] 5 (initial 5)=true := by decide
  have ho := evaluate_outcome 5 [1,5-3] 5 (initial 5) (by decide)
  rw [he] at ho
  exact ho

theorem odd_initial_outcome {n : Nat} (hn : 5≤n) (hp : n%4=1) :
    Outcome n [1,n-3] (initial n) true := by
  by_cases hh : n=5
  · subst n; exact five_outcome
  · exact initial_large (by omega) hp

#print axioms odd_initial_outcome
end Kotzig.FourEighteenWinning
