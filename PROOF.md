# Proof of Tan–Ward Conjecture 4.18

This is the mathematical exposition accompanying the Lean formalization of Conjecture 4.18 in Xin Lu Tan and Mark D. Ward's [*On Kotzig's Nim*, Integers 14 (2014), G06, printed page 25](https://math.colgate.edu/~integers/og6/og6.pdf). It is a provisional research exposition. Independent external mathematical review has not been completed.

**AI disclosure.** This document is an AI-generated prose argument explaining the formal proof. Mathematical research and formalization were also conducted with AI assistance.

## Statement and conventions

For every integer $m>3$, the landing-only normal-play game with moves $\{3,m\}$ on a cycle of length $m+1$ is a second-player win if and only if

$$m\equiv2\pmod4.$$

On a board of length $n$, vertices are the residues $0,\ldots,n-1$. The token starts at vertex $0$, which is already marked. Player I makes the first edge move. Each move adds an allowed step modulo $n$ and marks its landing vertex. A move is legal precisely when that vertex is fresh, meaning unmarked. Passing over marked vertices is allowed. A player with no legal move loses.

A position includes both the token location and the entire marked set. **P** means the player to move loses with optimal play; **N** means that player wins. In particular, an initial P-position is a second-player win. Each legal move marks one fresh vertex, so every play is finite, with at most $n-1$ moves from the initial position.

The formal theorem is [FourEighteenClassification.lean](Kotzig/FourEighteenClassification.lean), `Kotzig.FourEighteen.second_player_iff`. The lemmas below are uniform statements about actual positions, including all marked vertices. Unspecified vertices in a phase may be marked or fresh; no historical marks are erased when applying an induction hypothesis.

## 1. Reflection and the proof plan

Set $n=m+1\ge5$. The original moves are $3$ and $n-1$. Relabel the board by $x\mapsto -x\pmod n$. This bijection fixes $0$, changes the two steps to $-3$ and $+1$, and transports the entire marked set. Every legal move, player turn, and terminal position is preserved. The formal correspondence is proved in [FourEighteenTransport.lean](Kotzig/FourEighteenTransport.lean).

We therefore classify the reflected game with moves $+1$ and $-3$. It suffices to prove that its initial position is P exactly when $n\equiv3\pmod4$.

Even boards admit a pairing strategy for Player I. Odd boards are handled by three position shapes, called **closed**, **open**, and **dropped** phases. Their parameter $H$ is the current token location. Four-move blocks return the turn to the same player and reduce $H$ by $4$. This gives finite inductions within the two odd residue classes.

## 2. Even boards: a first-player pairing strategy

Assume $n\ge6$ is even. Pair each even vertex $e$ with the odd vertex $f(e)=e+1$. Since $e\le n-2$, this mate lies on the board without wrapping. The map $f$ is a bijection from even vertices to odd vertices.

Player I opens with $+1$, marking vertex $1=f(0)$. After each of Player I's turns, maintain the following invariant: the token is on an odd vertex, and the set of marked odd vertices is exactly $f(E)$, where $E$ is the set of marked even vertices.

Both allowed displacements, $1$ and $n-3$, are odd. Modulo an even board length they change parity, so every legal Player II move reaches a fresh even vertex $e$. Its mate $f(e)$ is fresh: otherwise $f(e)\in f(E)$, and injectivity would give $e\in E$, contradicting legality. Player I replies by $+1$ to $f(e)$ and restores the invariant.

Thus every legal Player II move has a legal Player I reply. Finiteness forces the game to end on Player II's turn. The initial position is N. This argument is formalized in [FourEighteenEven.lean](Kotzig/FourEighteenEven.lean).

## 3. Losing phases when the frontier is 3 modulo 4

In this section the opponent of the player currently to move uses the following rule: play $+1$ when its landing is fresh, and otherwise play $-3$. We prove that this rule is legal and winning on two classes of positions.

### 3.1. Closed phase

A position satisfies $C(n,H)$ if the token is at $H$, $3\le H$, $H+2<n$, and:

- vertices $0,H,H+1,H+2$ are marked;
- every vertex in $[3,H-2]$ is fresh.

All other vertices are unrestricted, including $H-1$, $1$, and $2$. Empty intervals impose no condition. If $H\equiv3\pmod4$, the position is P.

Induct on $(H-3)/4$. At $H=3$, the destinations $4$ and $0$ are both marked, so the player to move is blocked.

For $H\ge7$, the move to $H+1$ is blocked. The only legal move is $-3$ to $H-3$, which is fresh. The opponent replies by $+1$ to the fresh vertex $H-2$. There are now at most two legal continuations, with the following four-move paths:

$$H\to H-3\to H-2\to H-1\to H-4,$$

$$H\to H-3\to H-2\to H-5\to H-4.$$

The first continuation exists only if $H-1$ is fresh. Its final reply is $-3$, because the forward destination $H$ is marked. The second continuation exists only if $H-5$ is fresh; its final reply is $+1$. At $H=7$, vertex $H-5=2$ is unrestricted and may already be marked, in which case that branch is absent. Every prescribed opponent reply is fresh by the phase hypotheses.

Both paths produce $C(n,H-4)$. The required marks at the new frontier are $H-4,H-3,H-2$; vertex $0$ remains marked, and the smaller interval $[3,H-6]$ remains fresh. The extra mark in either path lies outside that smaller interval. Four moves restore the original turn, so the induction hypothesis proves the claim.

### 3.2. Open phase

A position satisfies $O(n,H)$ if the token is at $H$, $3\le H$, $H+3<n$, and:

- vertices $0,1,2,H,H+3$ are marked;
- every vertex in $[3,H-1]$ is fresh;
- vertices $H+1,H+2$ are fresh.

All other vertices are unrestricted. If $H\equiv3\pmod4$, the position is P under the same opponent rule.

At $H=3$, the backward destination is the marked vertex $0$. The only move is to $4$, answered by $+1$ to $5$. The next player is blocked because its destinations $6=H+3$ and $2$ are marked.

For $H\ge7$, there are two possible first moves. A forward move, followed by the opponent’s prescribed forward reply, leads to the four-move block

$$H\to H+1\to H+2\to H-1\to H-4.$$

The third move is forced because $H+3$ is marked. The last reply is backward because $H$ is marked. The resulting phase is $O(n,H-4)$: its two forward vertices $H-3,H-2$ stayed fresh, and its third forward vertex $H-1$ has just been marked.

A backward first move goes to $H-3$, answered by $+1$ to $H-2$. The two continuations from Section 3.1 then produce $C(n,H-4)$. At $H=7$, the continuation to $2$ is blocked by the open-phase hypothesis. Induction on $(H-3)/4$, together with the closed-phase result, proves the claim. All required lower fresh intervals and persistent marks are preserved.

The closed and open phase lemmas are formalized as `closed_outcome` and `open_outcome` in [FourEighteenLosing.lean](Kotzig/FourEighteenLosing.lean).

## 4. Initial admission when n is 3 modulo 4

Write $n=4k+3$ with $k\ge1$, and set $H=n-4\equiv3\pmod4$. In particular, $H\ge3$.

If Player I opens backward to $n-3$, Player II replies forward to $n-2$. Both of Player I's possible next moves admit a reply to $H$:

$$0\to n-3\to n-2\to n-1\to n-4,$$

$$0\to n-3\to n-2\to n-5\to n-4.$$

In the first path the final reply is backward, since a forward move would revisit $0$. In the second it is forward. Both paths produce $C(n,H)$ with Player I to move. The possible extra marks $n-1$ and $n-5=H-1$ are unrestricted by that phase.

If Player I opens forward to $1$, Player II replies forward to $2$. A backward continuation produces

$$0\to1\to2\to n-1\to n-4,$$

which enters $O(n,H)$ with Player I to move. A forward continuation produces $0\to1\to2\to3\to4$. All vertices in $[0,4]$ are then marked. Thereafter play is forced forward: at each successive vertex $d\ge4$, the backward destination $d-3$ is already in the marked prefix, while $d+1$ is fresh until the end of the board. There are exactly $n-1$ moves in the complete run. This is even, so Player II marks $n-1$ last, leaving Player I with both destinations $0$ and $n-4$ marked.

These branches cover both initial moves and every subsequent legal opponent choice. Hence the initial position is P whenever $n\equiv3\pmod4$, including the smallest such board $n=7$.

## 5. Winning phases when the frontier is 1 modulo 4

We next construct a winning strategy for the player currently to move. The open shape $O(n,H)$ is exactly the one defined in Section 3.2, but its outcome changes with the residue of $H$.

### 5.1. Dropped phase

A position satisfies $D(n,H)$ if the token is at $H$, $5\le H$, $H+3<n$, and:

- vertices $0,1,H,H+2,H+3$ are marked;
- every vertex in $[3,H-1]$ is fresh;
- vertex $H+1$ is fresh.

Vertex $2$ and all other unspecified vertices are unrestricted. If $H\equiv1\pmod4$, this position is N.

At $H=5$, the current player moves forward to $6$. The opponent's forward destination $7$ is marked, so its only legal move is backward to $3$. The current player moves forward to $4$, leaving the opponent blocked at the marked destinations $5$ and $1$.

For $H\ge9$, the current player chooses the forward moves in the following block:

$$H\to H+1\to H-2\to H-1\to H-4.$$

Both opponent moves are forced backward because their forward destinations $H+2$ and $H$ are marked. All displayed landings are fresh. The resulting position satisfies $D(n,H-4)$: vertex $H-3$ remains fresh, vertices $H-2,H-1$ have been marked, and the interval $[3,H-5]$ remains fresh. Induction on $(H-5)/4$ proves a win.

### 5.2. Open phase

Assume $O(n,H)$ with $H\ge5$ and $H\equiv1\pmod4$. The current player opens forward to $H+1$. The opponent has two possible replies. The corresponding blocks are

$$H\to H+1\to H+2\to H-1\to H-4,$$

$$H\to H+1\to H-2\to H-1\to H-4.$$

In the first block the current player's reply is backward, because $H+3$ is marked. In the second it is forward. After either reply, the opponent's forward destination $H$ is marked.

If $H=5$, the current player has reached vertex $4$, and the opponent's backward destination $1$ is also marked. The opponent is therefore blocked; the final arrow in the displayed blocks is not played.

If $H\ge9$, the opponent is forced backward to the fresh vertex $H-4$. The first block gives $O(n,H-4)$, because $H-3,H-2$ stayed fresh and $H-1$ was marked. The second gives $D(n,H-4)$, because $H-3$ stayed fresh and $H-2,H-1$ were marked. The required lower fresh interval and persistent marks are preserved in both cases. Induction and Section 5.1 prove that the current player wins.

These results are `drop_outcome` and `open_outcome` in [FourEighteenWinning.lean](Kotzig/FourEighteenWinning.lean).

## 6. Initial admission when n is 1 modulo 4

First suppose $n=4k+1\ge9$, and set $H=n-4\ge5$. Player I opens forward to $1$. Player II has exactly two legal replies.

If Player II moves forward to $2$, Player I chooses backward to $n-1$. Player II cannot move forward to the marked vertex $0$ and is forced backward to $H$. The path is

$$0\to1\to2\to n-1\to H.$$

It enters $O(n,H)$ with Player I to move.

If Player II moves backward to $n-2$, Player I moves forward to $n-1$. Again Player II is forced backward to $H$, giving

$$0\to1\to n-2\to n-1\to H.$$

This enters $D(n,H)$ with Player I to move. The two phase lemmas therefore give Player I a win against either opening response and every later legal opposing move.

For the remaining board $n=5$, Player I opens to $1$. Player II may go to $2$ or $3$; Player I replies to $4$ by a backward or forward move, respectively. The opponent is then blocked at $0$ and $1$. Thus the initial position is N for every $n\equiv1\pmod4$, $n\ge5$.

The Lean proof uses a kernel-evaluated exact base for $n=5$, connected to the actual game by the proved adequate-fuel evaluator theorem. All larger boards use the uniform phase argument.

## 7. Assembly and the original parameter

Sections 2, 4, and 6 exhaust all board lengths $n\ge5$: even boards are N, odd boards congruent to $1$ modulo $4$ are N, and odd boards congruent to $3$ modulo $4$ are P. Therefore

$$\text{the reflected initial game is P}\quad\Longleftrightarrow\quad n\equiv3\pmod4.$$

Reflection preserves the original game's outcome, and $n=m+1$. Consequently

$$\Gamma(3,m;m+1)\text{ is P}\quad\Longleftrightarrow\quad m\equiv2\pmod4,$$

for every $m>3$. This is the complete Conjecture 4.18 classification.

## 8. Formalization and module map

The top-level [Kotzig.lean](Kotzig.lean) imports the final classifier and its complete dependency closure. Modules are organized under `Kotzig/`; theorem namespaces and statements are unchanged.

The formal proof represents a state by its current vertex and a duplicate-free list of available vertices. A legal move removes its landing vertex. The initial list is exactly the board without vertex $0$. The phase hypotheses are membership and non-membership conditions on this actual list, with explicit board bounds. Natural-number subtraction in the Lean code is accompanied by the lower bounds needed to justify the ordinary integer arithmetic used above.

An `Outcome` derivation expresses a winning strategy recursively: a winning node chooses a legal losing child, while a losing node requires a winning child for every legal move. Each move decreases availability. The evaluator is proved to produce the same outcome whenever its fuel is at least the number of available vertices. Thus the final declaration concerns the faithful game, without an assumed recurrence or unproved strategy-to-game correspondence.

| Part of the argument | Lean sources and public entry points |
|---|---|
| Faithful game and outcomes | [GameSemantics.lean](Kotzig/GameSemantics.lean): `Legal`, `Outcome`, `initial_represents`, `legal_iff_unvisited`, `move_represents`. |
| Termination and adequate-fuel evaluation | [GameSemantics.lean](Kotzig/GameSemantics.lean): `move_decreases`, `initial_play_bound`, `evaluate_outcome`, `outcome_iff_evaluate`. |
| Closed/open losing phases and initial admission (§§3–4) | [FourEighteenLosing.lean](Kotzig/FourEighteenLosing.lean): `closed_outcome`, `open_outcome`, `prefix_outcome`, `losing_initial_outcome`, in namespace `Kotzig.FourEighteenLosing`. |
| Generic terminal and forced-move helpers | [FrontierTail.lean](Kotzig/FrontierTail.lean): `terminal_outcome`, `forced_outcome`, `two_options_outcome`; the older target-specific tail geometry is not assumed. |
| Dropped/open winning phases and initial admission (§§5–6) | [FourEighteenWinning.lean](Kotzig/FourEighteenWinning.lean): `drop_outcome`, `open_outcome`, `initial_large`, `five_outcome`, `odd_initial_outcome`, in namespace `Kotzig.FourEighteenWinning`. |
| Even-board pairing (§2) | [FourEighteenEven.lean](Kotzig/FourEighteenEven.lean): `reply_legal`, `paired_reply`, `paired_outcome`, `even_initial_outcome`, in namespace `Kotzig.FourEighteenEven`. |
| Outcome-preserving relabeling | [GameEmbedding.lean](Kotzig/GameEmbedding.lean): `embedding_outcome`; [GameMultiplication.lean](Kotzig/GameMultiplication.lean): `multiplication_embedding`; [GameSteps.lean](Kotzig/GameSteps.lean): `outcome_swap`. |
| Reflection (§1) | [FourEighteenTransport.lean](Kotzig/FourEighteenTransport.lean): `Kotzig.FourEighteen.reflection_outcome`. |
| Visited-history evaluator correspondence | [GameTargets.lean](Kotzig/GameTargets.lean): `firstPlayerWins`, `initialWin`; [Correspondence.lean](Kotzig/Correspondence.lean): `prototype_evaluate_eq`, `prototype_initialWin_eq`, `prototype_initial_outcome`. |
| Full original theorem (§7) | [FourEighteenClassification.lean](Kotzig/FourEighteenClassification.lean): `reflected_strategy`, `classification_strategy`, `second_player_iff`, `initial_classification`, `prototype_initial_classification`, in namespace `Kotzig.FourEighteen`. |

The final exports depend only on Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`. No added mathematical axiom, admitted theorem, external solver certificate, or `native_decide` is used. The original sources inform the statement and attribution, not the proof's premises. Build and axiom-check commands appear in the [README](README.md#verification).

## Literature

- Xin Lu Tan and Mark D. Ward, [*On Kotzig’s Nim*, Integers 14 (2014), G06](https://math.colgate.edu/~integers/og6/og6.pdf). Conjecture 4.18, printed page 25, is the target. Remark 4.19 attributes its odd-$m$ cases to the older odd-moves/even-board theorem.
- Aviezri S. Fraenkel, Alan Jaffray, Anton Kotzig, and Gert Sabidussi, [*Modular Nim*, Theoretical Computer Science 143(2) (1995), 319–333](https://doi.org/10.1016/0304-3975(94)00260-P). Theorem 3 supplies the all-odd-moves/even-board result. The paper also studies consecutive move pairs; those results are relevant to the relabelings below.
- David G. C. Horrocks and Jonathan H. Horrocks, [*Sprague–Grundy Values of Modular Nim*, Integers 19 (2019), G1](https://math.colgate.edu/~integers/tg1/tg1.pdf). Theorem 5 gives the first-player outcome for consecutive moves on boards $k(2a+1)-1$, with $a\ge2$. Section 3 covers the small pair $\{1,2\}$.
- Todd Edward Grimm, [*Describing the Play: Some Combinatorial Games*, MSc thesis, Dalhousie University (1998)](https://www.collectionscanada.gc.ca/obj/s4/f2/dsk1/tape9/PQDD_0016/MQ49363.pdf). Theorem 3.2.14, printed page 41, restates the consecutive-move classification on boards $k(2a+1)+1$, including the second-player outcome for $k=2$, and refers to Fraenkel et al. for proofs.
- Balaji R. Kadam and A. J. Shaiju, [*More Results on Modular Nim Games*, CGT Japan 2026 abstract](https://deguchikikaku.sakura.ne.jp/abstracts/). The abstract announces neighboring classifications, including $\Gamma(2,b-1;b)$ and $\Gamma(2,b;2+2b)$; it does not explicitly state this release’s full $\Gamma(3,m;m+1)$ classification. The announcement is distinct from an inspected full proof.

The relationship to the consecutive-move results can be made explicit. For an odd board $n=4j+1$, multiplication by $u=3j+1$ modulo $n$ has inverse multiplication by $4$, since $4u=3n+1$. It sends the original move pair $\{3,n-1\}$ to $\{j,j+1\}$ on board $2(2j+1)-1$. For $n=4j+3$, multiplication by $u=3j+2$ has inverse multiplication by $n-4$, since $4u=3n-1$. It sends the pair to $\{j,j+1\}$ on board $2(2j+1)+1$. Both bijections fix $0$ and preserve all landing tests and player turns.

The first relabeling invokes the known first-player consecutive-move family with $k=2$; its smallest case, $j=1$ and $n=5$, belongs to the separately classified $\{1,2\}$ game. The second invokes the second-player family with $k=2$, including $j=1$ and $n=7$. Together with the odd-moves/even-board result, these older statements bear on the complete classification. The source review inspected the primary N-family statement and the secondary P-family restatement cited above.

The proof in §§1–7 is direct and does not use these external theorems as formal premises. The references identify the original conjecture and relevant prior mathematics.
