import Kotzig.GameEmbedding

namespace Kotzig

theorem multiplication_destination (n unit x step : Nat) :
    (unit * destination n x step) % n =
      destination n ((unit*x)%n) ((unit*step)%n) := by
  unfold destination
  rw [Nat.mul_mod, Nat.mod_mod]
  rw [← Nat.mul_mod]
  rw [Nat.mul_add, Nat.add_mod]


theorem multiplication_leftInverse {n unit inverse x : Nat} (hx : x<n)
    (hi : (inverse*unit)%n=1) :
    (inverse*((unit*x)%n))%n=x := by
  rw [Nat.mul_mod,Nat.mod_mod,←Nat.mul_mod,←Nat.mul_assoc,
    Nat.mul_mod,hi,Nat.one_mul,Nat.mod_mod,Nat.mod_eq_of_lt hx]

theorem multiplication_embedding {n unit inverse : Nat} (hn : 0<n)
    (hi : (inverse*unit)%n=1) :
    VertexEmbedding n n (fun x => (unit*x)%n) (fun step => (unit*step)%n) := {
  sourcePositive := hn
  targetPositive := hn
  bounded := fun _ _ => Nat.mod_lt _ hn
  injective := by
    intro x y hx hy he
    have hm := congrArg (fun z => (inverse*z)%n) he
    rw [multiplication_leftInverse hx hi,multiplication_leftInverse hy hi] at hm
    exact hm
  destination := fun _ _ _ => multiplication_destination _ _ _ _
}


#print axioms multiplication_embedding
end Kotzig
