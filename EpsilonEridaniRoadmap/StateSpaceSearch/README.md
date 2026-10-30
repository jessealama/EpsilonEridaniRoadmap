# State-space search: heuristic and adversarial

Build the search algorithms of Russell and Norvig's *Artificial Intelligence:
A Modern Approach*, Chapters 3 and 5, over implicitly given state spaces: a
generic best-first search parametrised by an abstract frontier, its uninformed
instances, A* with admissible and consistent heuristics, and minimax with
alpha-beta pruning. A problem is a black box seen through its interface, the
initial state, the applicable actions, the transition function, the goal test,
and the step cost, and a heuristic is a further black box. Costs are counted in
CSLib's query-complexity framework: every call on the interface is a query, so
the textbook's measures, nodes expanded and nodes generated, are query counts
derived from the program rather than annotations placed in it. The endpoints
are soundness and completeness of the uninformed searches, optimality of
uniform-cost search and of A* under admissibility and consistency, the
expansion count for A* with a consistent heuristic, a bridge from finite
weighted digraphs to problems, the equality of alpha-beta and minimax, and the
query-model statements that make lower bounds and optimality among algorithms
expressible.

The motivation is threefold. CSLib's contribution guide asks for reusable APIs
for algorithmic paradigms, and best-first search over an abstract frontier is
one; the area follows CSLib and Mathlib conventions so that pieces can move
upstream later if wanted. Classical planning is the intended follow-on area:
STRIPS problems are search problems, and planning heuristics are the admissible
heuristics of Milestone 4. The material is also the standard undergraduate
treatment of search, and a Lean library following the book's structure has
teaching value on its own. The area would be the first consumer of CSLib's
query framework outside sorting.

**Suggested homes:** `EpsilonEridani/Algorithms/Lean/Search/` for problems,
frontiers, the searches, and their cost analyses, following the placement of
CSLib's `Query` and sorting developments; games and adversarial search under
`EpsilonEridani/Algorithms/Lean/Search/Game/`.

[`Suggested.lean`](Suggested.lean) provides suggested signatures, never an
exhaustive checklist; this document is the specification.

## Existing libraries and related work

CSLib has no search algorithms (checked 2026-10-30). Its contribution guide
lists graph algorithms and APIs for algorithmic paradigms as welcome tracks.
The developments below supply vocabulary, conventions, and proof templates;
the targets are the missing abstractions and theory.

- CSLib's [query-complexity framework](https://github.com/leanprover/cslib/tree/main/Cslib/Algorithms/Lean/Query)
  represents a program as `FreeM Q α` over a query type `Q`, and derives
  `eval`, `countQueries`, and `cost` from the free monad. Counting is
  structural: only lifted queries are charged, pure computation is free, and
  a program parametric in the oracle cannot avoid the queries. Its sorting
  examples fix the house pattern used here: define an algorithm once,
  polymorphically in a monadic interface, and instantiate it at `Id` for the
  pure algorithm and at `FreeM Q` for counting, with `eval` at the honest
  oracle equal to the pure result. `FreeM.exists_countQueries_ge_clog` is its
  adversary lemma; see [Further targets](#further-targets) for why search
  needs a second one.
- CSLib's [monad-polymorphic sorts](https://github.com/leanprover/cslib/blob/main/Cslib/Algorithms/Lean/Sort/Merge.lean)
  and `IsMonadHom` are the mechanism for transferring results between
  instantiations, as `eval_mergeSort` does.
- complexitylib has breadth-first reachability and Dijkstra over a word-RAM
  model. Both are explicit-graph algorithms with machine-time accounting, the
  bucket this area leaves to CSLib's graph track.
- Behnke, Kilian, and Gattinger's
  [lean4-search-algorithms](https://github.com/galvusdamor/lean4-search-algorithms)
  (Apache 2.0) has DFS, BFS, Dijkstra, and A* over explicit finite weighted
  digraphs, with `FinEnum` vertices and decidable adjacency, termination by
  well-founded recursion, and theorems of soundness, completeness, and
  optimality under admissibility, through the invariants of Hart, Nilsson,
  and Raphael. Their closed nodes receive distance updates, so reopening is
  built in, and there are no consistency results. Their invariants are the
  proof template for Milestones 4 and 5. The bridge of Milestone 5 lets the
  results here specialise to their setting. Adapting their code with
  attribution is welcome.
- The open roadmap PR [#6](https://github.com/cslib-community/EpsilonEridaniRoadmap/pull/6)
  covers DPLL and branching algorithms, so constraint satisfaction and
  backtracking are deferred rather than taken here.
- Mathlib supplies `Digraph`, `FinEnum`, `Nat.log`, `List.Perm`, `Set.ncard`,
  and the `LinearOrder` API. Batteries supplies `BinaryHeap`. Use these
  rather than private versions.

Published formalisations to consult for proof structure, not to port:
Nipkow's *Alpha-Beta Pruning Verified* (ITP 2024, Archive of Formal Proofs)
covers the alpha-beta milestone's theorems, including fail-hard and fail-soft
variants and lattice-valued utilities, in Isabelle.

## Conventions and acceptance criteria

### Problems and solutions

- A `Problem S A` has an initial state, `List`-valued applicable actions, a
  transition function, a Boolean goal test, and a step cost in `ℕ`. The state
  type is arbitrary and need not be finite; finiteness of the reachable set,
  or existence of a solution, is a hypothesis of the theorems that need it.
  Branching is finite by construction, since actions form a list.
- The successor relation, reachability, and path cost are derived from the
  interface as definitions and lemmas, never taken as primitive. A solution is
  a list of actions, each applicable where it is taken, from the initial
  state to a goal. An optimal solution is a solution of least path cost.
- Step costs are natural numbers. Where the textbook requires step costs at
  least `ε > 0`, the hypothesis is that every step cost is positive. General
  ordered monoids and real-valued costs are out of scope.
- All recursive searches take a fuel argument and are total. Nothing is
  `partial`. Completeness theorems say that enough fuel exists; where a bound
  is natural, state it, for example fuel equal to the number of nodes of
  depth at most the solution depth for breadth-first search.

### The frontier interface

- The frontier is an abstract type class with `empty`, `insert`, `popMin?`
  by a priority function into `ℕ`, and `toList`, specified by: the list of
  the empty frontier is empty; inserting permutes to consing; popping returns
  an element of minimal priority together with the frontier of the rest.
  Ties may break arbitrarily; no theorem may depend on a tie-breaking rule.
- The reference instance is a list with linear-time minimum extraction. A
  Batteries binary heap is an efficiency instance and an out-of-area
  dependency; no correctness theorem may depend on it.
- Priorities are evaluated when a node is generated and stored with it, so
  that a heuristic is consulted exactly once per generated node.

### Cost model

- **One definition, two instantiations.** Each search is defined once over an
  arbitrary monad `m`, taking the problem through a monadic interface record
  whose fields are `actions`, `result`, `isGoal`, `stepCost`, and `heuristic`
  in `m`. It is instantiated at `Id` with the pure problem and heuristic,
  giving the pure algorithm that carries correctness, and at
  `FreeM (SearchQuery S A)` with each field a lifted query, giving the
  counted program. The pure algorithm equals the query program's `eval` at the
  problem's oracle; this transfer lemma is proved once through `IsMonadHom`,
  as the CSLib sorts do.
- **Queries are the interface calls.** `SearchQuery S A` has one constructor
  per interface field. Weighted costs select the measure: weight one on
  `actions` counts expansions, weight one on `result` counts generated nodes,
  weight one on `heuristic` counts heuristic evaluations. Bounds are stated
  with `FreeM.cost` directly, as explicit inequalities holding for every
  oracle satisfying the stated hypotheses. CSLib's `Cslib.Query.UpperBound`
  is unit-weight and indexed by an input size, which does not fit
  problem-dependent search bounds; a weighted, hypothesis-relative wrapper
  may be proposed upstream, and is not a prerequisite.
- **Heuristic properties are hypotheses on the oracle.** A heuristic is
  admissible when it never exceeds the optimal cost to a goal, and consistent
  when it is zero at goals and satisfies the triangle inequality along every
  applicable action. Theorems about A* quantify over every heuristic oracle
  satisfying these; nothing is assumed about how it is computed.
- **Pure computation is free.** Frontier operations, explored-set membership,
  and equality tests on states use `DecidableEq S` and the frontier instance,
  not the oracle, and are not charged. The algorithm is parametric in the
  state type and sees it only through these and the interface, so it cannot
  reconstruct the problem and the counts are meaningful. No machine-time
  claim is made; see [Out of scope](#out-of-scope).
- No big-O statement is a target. All bounds are worst-case.

### Games

- A `Game S A U` has an initial state, a player to move among two players,
  `List`-valued actions, a transition function, a terminal test, and a
  utility in a `LinearOrder U`, stated from the maximising player's point of
  view. Games are two-player, zero-sum, deterministic, and fully observable.
- The game value is defined by recursion on a depth bound, with the static
  utility at the bound. Theorems about minimax and alpha-beta are stated at
  any depth bound; agreement with the unbounded value is a corollary for
  games with a finite horizon.
- A game is well-formed when every non-terminal state has an action.
  Well-formedness is a hypothesis, never bundled into the type.
- Leaf evaluations are counted through a `GameQuery` type with weight one on
  `utility`, in the same two-instantiation pattern as problems.

### API expectations

- Every structure needs its basic API: the derived successor relation and its
  characterisation, `run` of an action sequence, `pathCost` with its
  concatenation lemma, `IsSolution`, `IsOptimalSolution`, reachability, and
  `decide`- or `rfl`-checked examples small enough to read, such as a
  sliding-tile or grid problem with a handful of states and a tic-tac-toe
  position.
- Every search needs its monad-polymorphic definition, its `Id` and `FreeM`
  instantiations, the transfer lemma, soundness, and the completeness,
  optimality, and cost statements its milestone lists.

## Milestones

Dependencies name prerequisite milestones, in addition to existing upstream
APIs. Each milestone can be implemented in smaller contributions along its
listed theorem boundaries.

### M1. Problems, solutions, and the query interface

Define `Problem`, `run`, `pathCost`, `IsSolution`, `IsOptimalSolution`,
`Reachable`, `Solvable`, `PositiveCosts`, and the derived successor relation.
Prove: `run` of an append is the composition; `pathCost` of an append is the
sum; a solution is a path from the initial state to a goal, as an
if-and-only-if against the successor relation's reflexive transitive closure;
an optimal solution's cost is unique. Define `SearchQuery`, the monadic
interface record, the `Id` interface of a problem with a heuristic, the
problem's oracle, and the `FreeM` interface, and prove that each field of the
`FreeM` interface evaluates at the oracle to the pure field. Define the
expansion, generation, and heuristic weights. Define `Game` and its basic
API in the same way, with `GameQuery`.

### M2. Frontier interface and generic best-first search

Dependencies: M1.

Define the `Frontier` class with its specification, the list instance with
its proofs, the search `Node` carrying state, action path, path cost, and
depth, node expansion, and fuel-based `bestFirstM` as tree search: pop a
minimal node, return its path if it is a goal, otherwise expand it and insert
the children with their priorities. Priorities are monad-polymorphic
functions of the interface and the node. Instantiate at `Id` and `FreeM`,
prove the transfer lemma, and prove soundness: a returned path is a solution.
Prove that the returned path is the popped node's path and that every node
in the frontier is reachable, the invariants the later milestones use.

### M3. Uninformed search

Dependencies: M2.

Instantiate best-first search at depth, giving breadth-first search, and at
path cost, giving uniform-cost search. Define depth-limited search as a
fuel-based depth-first recursion with a limit, and iterative deepening as its
iteration. Prove: breadth-first search is complete and returns a solution of
least depth, with fuel bounded by the number of nodes of depth at most the
solution depth; uniform-cost search is complete under positive step costs and
returns an optimal solution; depth-limited search is complete when the limit
is at least the solution depth and returns no path otherwise; iterative
deepening is complete and returns a solution of least depth. Prove the
generation count for breadth-first search: with branching at most `b` and
least solution depth `d`, at most `(b^(d+1) - 1) / (b - 1)` nodes are
generated, as a `FreeM.cost` bound with the generation weight.

### M4. Heuristics and A* as tree search

Dependencies: M3.

Define the optimal cost-to-go as a predicate on a state and a cost,
`Admissible`, and `Consistent`, and prove that consistency with zero at goals
implies admissibility. Instantiate best-first search at `g + h`, giving A*,
at `g + w · h`, giving weighted A*, and at `h`, giving greedy best-first
search. Prove: A* as tree search is complete under positive step costs and
returns an optimal solution when the heuristic is admissible; weighted A*
returns a solution of cost at most `w` times the optimal cost; greedy
best-first search is sound and, with an example, neither optimal nor
complete without fuel. Define iterative-deepening A* as iterated depth-first
search with an `f`-bound and prove it complete and optimal under
admissibility.

### M5. Graph search, the expansion count, and the digraph bridge

Dependencies: M4.

Define `graphSearchM` with an explored set over `DecidableEq S`, in which a
state is expanded at most once, and its instantiations and transfer lemma.
Prove: graph search is sound; with a consistent heuristic, A* graph search
returns an optimal solution, and its expansion cost, `FreeM.cost` with the
expansion weight, is at most the number of reachable states, which is finite
by hypothesis, because each state is expanded at most once. Give an example of
an admissible but inconsistent heuristic on which graph search without
reopening returns a suboptimal solution, and define the reopening variant
with its optimality under admissibility as a target. Define the problem of a
finite weighted digraph, from a Mathlib `Digraph` with `FinEnum` vertices,
decidable adjacency, a weight function, a source, and a goal predicate, and
prove that its successor relation is adjacency and that its optimal solutions
are shortest paths. This is the bridge to Behnke, Kilian, and Gattinger's
setting.

### M6. Games, game value, and minimax

Dependencies: M1.

Define the depth-bounded game value `valueM` monad-polymorphically over the
game interface, with its `Id` and `FreeM` instantiations and transfer lemma,
and the minimax decision returning an action. Prove: the value of a terminal
state is its utility; at a non-terminal state with the maximising player to
move the value is the maximum over actions of the values of the results, and
dually; the minimax decision achieves the value; for a well-formed game with
a finite horizon the value is independent of the depth bound once it exceeds
the horizon. Prove the leaf count: minimax at depth `d` on a game with
branching at most `b` makes at most `b^d` utility queries.

### M7. Alpha-beta pruning

Dependencies: M6.

Define fail-hard and fail-soft alpha-beta monad-polymorphically, with
instantiations and transfer lemmas. Prove, for a window `α < β`: fail-hard
alpha-beta returns the value clamped to the window, so equals the value when
the value is strictly inside it; fail-soft alpha-beta equals the value inside
the window, is at most `α` when the value is at most `α`, and at least `β`
when the value is at least `β`; the alpha-beta decision at the full window
agrees with minimax. Record Nipkow's statements as the template. Later
targets: lattice-valued utilities, and the Knuth and Moore leaf bound,
`b^⌈d/2⌉ + b^⌊d/2⌋ - 1` utility queries under optimal move ordering, as a
`FreeM.cost` statement.

## Further targets

These are statable only because programs are `FreeM` trees quantified over
oracles, which `TimeM` could not express. Both need an adversary lemma beyond
CSLib's `FreeM.exists_countQueries_ge_clog`, which is information-theoretic
and gives only a logarithmic bound against Boolean goal tests, while the
bounds below are linear in the number of candidate states. They belong after
M5 and are not required for completion of the area.

- An adversary lower bound for uninformed search: any sound search program
  that, on a problem whose goal is hidden among `n` reachable states, finds
  the goal under every placement must make at least `n` goal-test queries for
  some placement.
- Dechter and Pearl's optimality of A*: among programs that return optimal
  solutions for every consistent heuristic oracle, A* with tie-breaking in
  favour of goals expands no state that some such program does not also
  expand, in the sense of their 1985 paper.

## Out of scope

The following are not targets of this roadmap. A reader who needs one of
them should write a roadmap for it, citing this one.

- Explicit-graph algorithms on `SimpleGraph` or adjacency structures beyond
  the bridge of M5; these belong to CSLib's graph track and complexitylib.
- Local search and stochastic methods, including hill climbing, simulated
  annealing, and Monte Carlo tree search.
- Constraint satisfaction and backtracking, deferred given roadmap PR #6.
- `TimeM` accounting of frontier and explored-set operations, and machine-time
  claims generally; the query model leaves pure computation uncharged.
- Real-valued or general ordered-monoid step costs.
- Games with chance nodes or imperfect information, and more than two
  players.
- Classical planning itself, STRIPS, and planning heuristics; these are the
  intended follow-on area.

## Dependency and launch order

An order satisfying all dependencies is M1, M2, M3, M4, M5, M6, M7. M1 is a
single self-contained contribution and the right place to start. M6 and M7
depend only on M1 and can proceed in parallel with M2 to M5.

Completion means the structures, searches, transfer lemmas, correctness
theorems, and cost bounds above are implemented against the existing APIs.
Definitions without their lemmas, or searches without their bounds, do not
discharge a milestone.

## References

These specify the algorithms and conventions. They do not prescribe a port of
any existing formalisation.

- **Textbook:** Russell and Norvig, *Artificial Intelligence: A Modern
  Approach*, 4th edition, Chapters 3 and 5.
- **A\* and its optimality:** Hart, Nilsson, and Raphael, *A formal basis for
  the heuristic determination of minimum cost paths*, IEEE Transactions on
  Systems Science and Cybernetics 4 (1968), 100–107; Pearl, *Heuristics*,
  Addison-Wesley 1984; Dechter and Pearl, *Generalized best-first search
  strategies and the optimality of A\**, Journal of the ACM 32 (1985),
  505–536.
- **Weighted A\* and IDA\*:** Pohl, *Heuristic search viewed as path finding
  in a graph*, Artificial Intelligence 1 (1970), 193–204; Korf, *Depth-first
  iterative-deepening: an optimal admissible tree search*, Artificial
  Intelligence 27 (1985), 97–109.
- **Alpha-beta:** Knuth and Moore, *An analysis of alpha-beta pruning*,
  Artificial Intelligence 6 (1975), 293–326.
- **Query complexity:** CSLib's
  [query framework](https://github.com/leanprover/cslib/pull/401) and its
  module documentation.
- **Formalisations:** Behnke, Kilian, and Gattinger, *A\* with hmax
  Definitely Finds Optimal Plans*, ICAPS HSDIP 2026, with the
  [search](https://github.com/galvusdamor/lean4-search-algorithms) and
  [planner](https://github.com/galvusdamor/lean4-planner) repositories;
  [Nipkow, *Alpha-Beta Pruning Verified*, ITP 2024](https://www.isa-afp.org/entries/Alpha_Beta_Pruning.html).
