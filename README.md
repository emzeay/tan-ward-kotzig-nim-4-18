# Kotzig's Nim: Tan–Ward Conjecture 4.18

A complete Lean 4 proof of **Conjecture 4.18** in Xin Lu Tan and Mark D. Ward's [*On Kotzig's Nim*, Integers 14 (2014), G06](https://math.colgate.edu/~integers/og6/og6.pdf).

**Provisional research release.** This repository contains the complete formal proof and a mathematical exposition. The formalization has been checked locally with Lean's kernel. Independent external mathematical review has not been completed.

**AI disclosure.** This project was developed with substantial AI assistance, including mathematical research, Lean formalization, and documentation. [PROOF.md](PROOF.md) is an AI-generated prose argument explaining the formal proof. Lean’s kernel checks the formalization but the prose argument requires separate mathematical review. I plan to release a revised proof exposition with more of my own mathematical development and writing.

## Statement

For every integer $m>3$, the game with moves $\{3,m\}$ on a circular board of length $m+1$ is a second-player win exactly when

$$m\equiv2\pmod4.$$

Vertex 0 is initially marked; Player I makes the first edge move. A move adds either step modulo the board length. Only the landing vertex must be unmarked; jumping over marked vertices is allowed. The player with no legal move loses.

The final declaration is `Kotzig.FourEighteen.second_player_iff` in [FourEighteenClassification.lean](Kotzig/FourEighteenClassification.lean):

```lean
theorem second_player_iff {m : Nat} (hm : 3 < m) :
    Outcome (m+1) [3,m] (initial (m+1)) false ↔ m%4=2
```

`false` denotes a losing position for the player to move. The module also proves strategy derivations and agreement with the game evaluators.

## Verification

Install [Lean and elan](https://lean-lang.org/install/), then run from this directory:

```sh
lake build
lake env lean --trust=0 Kotzig/FourEighteenClassification.lean
```

Lean **4.34.1** is pinned in `lean-toolchain`. The project uses bundled Std with no external Lake dependencies. The final exports report exactly:

```text
[propext, Classical.choice, Quot.sound]
```

These are standard Lean axioms. No `sorry`, custom conjectural axiom, unsafe proof code, or `native_decide` is used. Diagnostic `#eval` commands in `GameTargets` are not proof premises. Kernel checking establishes the formal statement under these axioms. The definitions and exposition require separate mathematical review.

## Reading the proof

Start with [PROOF.md](PROOF.md). Importing the top-level [Kotzig.lean](Kotzig.lean) entry file brings in the complete formalization. The argument reflects the game to moves +1 and -3, uses an even-board pairing, and proves descending phase strategies for odd boards.

1. [GameSemantics.lean](Kotzig/GameSemantics.lean) defines the faithful game, termination, evaluation, and outcomes.
2. [FourEighteenLosing.lean](Kotzig/FourEighteenLosing.lean) and [FourEighteenWinning.lean](Kotzig/FourEighteenWinning.lean) prove the odd-board phase strategies.
3. [FourEighteenEven.lean](Kotzig/FourEighteenEven.lean) proves the even-board pairing.
4. [FourEighteenTransport.lean](Kotzig/FourEighteenTransport.lean) proves reflection; [FourEighteenClassification.lean](Kotzig/FourEighteenClassification.lean) assembles the original theorem.

## Sources

Tan–Ward attribute the odd-$m$ cases to earlier work. Older consecutive-step classifications also bear on the remaining cases through modular relabeling. The sources and parameter translations are described in [PROOF.md](PROOF.md#literature).

## License

Source and documentation are licensed under the [Apache License, Version 2.0](LICENSE).
