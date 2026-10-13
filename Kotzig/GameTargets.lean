import Std

/-!
Executable statement prototypes for two old Kotzig's Nim conjectures.
These are definitions of propositions, not proofs of the conjectures.
Normal play: move the shared token to a previously unvisited vertex.
The initial vertex 0 counts as visited. Steps are interpreted modulo n.
At most n-1 moves are possible, so fuel n is sufficient from the initial state.
A proof project should establish this bound and the strategy/recursion correspondence.
-/

namespace GameTargets

def firstPlayerWins : Nat → List Nat → Nat → Nat → List Nat → Bool
  | _, _, 0, _, _ => false
  | n, steps, fuel + 1, position, visited =>
      steps.any fun step =>
        let dest := (position + step) % n
        !visited.contains dest &&
          !firstPlayerWins n steps fuel dest (dest :: visited)

def initialWin (n : Nat) (steps : List Nat) : Bool :=
  firstPlayerWins n steps n 0 [0]

/-- Tan-Ward (2014), Conjecture 4.21, reflected as steps +1 and -2. -/
def TanWardForwardOneBackwardTwo : Prop :=
  ∀ n : Nat, 4 ≤ n →
    initialWin n [1, n - 2] =
      decide (n % 10 ≠ 3 ∧ n % 10 ≠ 7 ∧ n % 10 ≠ 8)

/-- Tan-Ward (2014), Conjecture 4.3, with exactly its three exceptions. -/
def TanWardThreeFive : Prop :=
  ∀ n : Nat, 1 ≤ n →
    initialWin n [3, 5] =
      decide (n % 2 = 0 ∨ n = 9 ∨ n = 11 ∨ n = 17)

#check TanWardForwardOneBackwardTwo
#check TanWardThreeFive
#eval (List.range 9).map fun i => (i + 4, initialWin (i + 4) [1, i + 2])
#eval (List.range 12).map fun i => (i + 1, initialWin (i + 1) [3, 5])

end GameTargets
