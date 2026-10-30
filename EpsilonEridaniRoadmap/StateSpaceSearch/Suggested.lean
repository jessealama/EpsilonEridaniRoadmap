module

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Set.Card
public import Cslib.Algorithms.Lean.Query.FreeM

/-!
# State-space search: suggested signatures

**This file is not the roadmap and is not exhaustive.** The definitive document is `README.md`.
The declarations below suggest Lean forms for the load-bearing structures and a few milestone
statements, so that contributors and reviewers converge on names and shapes. Discharging every
declaration here finishes neither a milestone nor the roadmap. `sorry` is allowed in this
human-owned roadmap library: these are targets, not completed definitions or proofs.

The pinned choices illustrated here are:

- A `Problem` is the AIMA interface: initial state, `List`-valued actions, transition, Boolean
  goal test, step cost in `ℕ`. The state type need not be finite. The successor relation, paths,
  and solutions are derived.
- Every search takes fuel and is total. Completeness theorems assert that enough fuel exists.
- The frontier is an abstract class with a list reference instance.
- Each search is defined once over an arbitrary monad through a monadic problem interface, and
  instantiated at `Id` (the pure algorithm, carrying correctness) and at
  `FreeM (SearchQuery S A)` (the counted program). Interface calls are the queries; weights
  select expansions, generations, or heuristic evaluations. Bounds are `FreeM.cost`
  inequalities over all oracles satisfying the stated hypotheses.
- Heuristic properties, admissibility and consistency, are hypotheses on the oracle.
- Games are two-player zero-sum with utilities in a `LinearOrder`, from the maximiser's view.
- State, action, and utility types are fixed in `Type`, as CSLib's query types are.

Milestones 1 to 4 and 6 are prototyped in some detail; Milestones 5 and 7 give headline
signatures only.
-/

namespace EpsilonEridani.Search

open Cslib (FreeM)

-- The monads range over `Type → Type w`: `Id` lives at `w = 0` and `FreeM Q` at `w = 1`.
universe w

/-! ## Milestone 1: problems, solutions, and the query interface -/

/-- A search problem over an implicit state space, in the AIMA parametrisation. -/
structure Problem (S A : Type) where
  /-- The initial state. -/
  initial : S
  /-- The actions applicable in a state. Branching is finite by construction. -/
  actions : S → List A
  /-- The transition function. Its value is unconstrained on inapplicable actions. -/
  result : S → A → S
  /-- The goal test. -/
  isGoal : S → Bool
  /-- The cost of one step. -/
  stepCost : S → A → ℕ

namespace Problem

variable {S A : Type} (p : Problem S A)

/-- The derived successor relation. -/
def Succ (s s' : S) : Prop := ∃ a ∈ p.actions s, p.result s a = s'

section Run

variable [DecidableEq A]

/-- Apply a sequence of actions, failing if one is inapplicable where it is taken. -/
def run : S → List A → Option S
  | s, [] => some s
  | s, a :: as => if a ∈ p.actions s then run (p.result s a) as else none

/-- Running an appended sequence runs the pieces in turn. -/
theorem run_append (s : S) (as bs : List A) :
    p.run s (as ++ bs) = (p.run s as).bind fun s' => p.run s' bs := sorry

/-- A state reachable from the initial state. -/
def Reachable (s : S) : Prop := ∃ as, p.run p.initial as = some s

/-- A solution: an applicable action sequence from the initial state to a goal. -/
def IsSolution (as : List A) : Prop :=
  ∃ g, p.run p.initial as = some g ∧ p.isGoal g = true

/-- The problem has a solution. -/
def Solvable : Prop := ∃ as, p.IsSolution as

end Run

/-- The cost of an action sequence from a state. Defined on all sequences; applicability is
tracked by `run`. -/
def pathCost : S → List A → ℕ
  | _, [] => 0
  | s, a :: as => p.stepCost s a + pathCost (p.result s a) as

/-- Path cost of an append is the sum, when the first piece runs. -/
theorem pathCost_append [DecidableEq A] (s s' : S) (as bs : List A)
    (h : p.run s as = some s') :
    p.pathCost s (as ++ bs) = p.pathCost s as + p.pathCost s' bs := sorry

/-- An optimal solution: a solution of least path cost. -/
def IsOptimalSolution [DecidableEq A] (as : List A) : Prop :=
  p.IsSolution as ∧ ∀ bs, p.IsSolution bs → p.pathCost p.initial as ≤ p.pathCost p.initial bs

/-- Every step cost is positive. The textbook's `ε > 0` hypothesis. -/
def PositiveCosts : Prop := ∀ s a, 0 < p.stepCost s a

/-- Reachability is the reflexive transitive closure of the successor relation. -/
theorem reachable_iff [DecidableEq A] (s : S) :
    p.Reachable s ↔ Relation.ReflTransGen p.Succ p.initial s := sorry

/-- `c` is the optimal cost from `s` to a goal: some goal path from `s` costs `c`, and no goal
path from `s` costs less. -/
def IsOptimalCostFrom [DecidableEq A] (s : S) (c : ℕ) : Prop :=
  (∃ as g, p.run s as = some g ∧ p.isGoal g = true ∧ p.pathCost s as = c) ∧
    ∀ as g, p.run s as = some g → p.isGoal g = true → c ≤ p.pathCost s as

/-- A heuristic never exceeds the optimal cost to a goal. -/
def Admissible [DecidableEq A] (h : S → ℕ) : Prop :=
  ∀ s c, p.IsOptimalCostFrom s c → h s ≤ c

/-- A heuristic is zero at goals and satisfies the triangle inequality along applicable
actions. -/
def Consistent (h : S → ℕ) : Prop :=
  (∀ s, p.isGoal s = true → h s = 0) ∧
    ∀ s a, a ∈ p.actions s → h s ≤ p.stepCost s a + h (p.result s a)

theorem Consistent.admissible [DecidableEq A] {h : S → ℕ} (hc : p.Consistent h) :
    p.Admissible h := sorry

end Problem

/-- The queries of the problem interface. Each constructor is one interface call; the
heuristic is part of the interface so that A* theorems quantify over heuristic oracles. -/
inductive SearchQuery (S A : Type) : Type → Type where
  | actions (s : S) : SearchQuery S A (List A)
  | result (s : S) (a : A) : SearchQuery S A S
  | isGoal (s : S) : SearchQuery S A Bool
  | stepCost (s : S) (a : A) : SearchQuery S A ℕ
  | heuristic (s : S) : SearchQuery S A ℕ

/-- The problem interface in an arbitrary monad. Searches are written against this record. -/
structure ProblemM (m : Type → Type w) (S A : Type) where
  actions : S → m (List A)
  result : S → A → m S
  isGoal : S → m Bool
  stepCost : S → A → m ℕ
  heuristic : S → m ℕ

namespace Problem

variable {S A : Type} (p : Problem S A) (h : S → ℕ)

/-- The pure interface of a problem with a heuristic. -/
def toM : ProblemM Id S A where
  actions s := pure (p.actions s)
  result s a := pure (p.result s a)
  isGoal s := pure (p.isGoal s)
  stepCost s a := pure (p.stepCost s a)
  heuristic s := pure (h s)

/-- The honest oracle of a problem with a heuristic. -/
def oracle : {ι : Type} → SearchQuery S A ι → ι
  | _, .actions s => p.actions s
  | _, .result s a => p.result s a
  | _, .isGoal s => p.isGoal s
  | _, .stepCost s a => p.stepCost s a
  | _, .heuristic s => h s

end Problem

namespace SearchQuery

variable {S A : Type}

/-- The counted interface: every call is a lifted query. -/
def interface : ProblemM (FreeM (SearchQuery S A)) S A where
  actions s := FreeM.lift (.actions s)
  result s a := FreeM.lift (.result s a)
  isGoal s := FreeM.lift (.isGoal s)
  stepCost s a := FreeM.lift (.stepCost s a)
  heuristic s := FreeM.lift (.heuristic s)

/-- Weight one on expansions. -/
def expansionWeight : {ι : Type} → SearchQuery S A ι → ℕ
  | _, .actions _ => 1
  | _, _ => 0

/-- Weight one on generated nodes. -/
def generationWeight : {ι : Type} → SearchQuery S A ι → ℕ
  | _, .result _ _ => 1
  | _, _ => 0

/-- Weight one on heuristic evaluations. -/
def heuristicWeight : {ι : Type} → SearchQuery S A ι → ℕ
  | _, .heuristic _ => 1
  | _, _ => 0

/-- Each interface field evaluates at the honest oracle to the pure field. -/
@[simp] theorem eval_actions (p : Problem S A) (h : S → ℕ) (s : S) :
    (interface.actions s).eval (p.oracle h) = p.actions s := rfl

@[simp] theorem eval_heuristic (p : Problem S A) (h : S → ℕ) (s : S) :
    (interface.heuristic s).eval (p.oracle h) = h s := rfl

end SearchQuery

/-! ## Milestone 2: frontier interface and generic best-first search -/

/-- An abstract frontier: a multiset with minimum extraction by a `ℕ`-valued priority.
Ties break arbitrarily; no theorem may depend on the tie-breaking rule. -/
class Frontier (F : Type → Type) where
  empty {α : Type} : F α
  insert {α : Type} : α → F α → F α
  popMin? {α : Type} : (α → ℕ) → F α → Option (α × F α)
  toList {α : Type} : F α → List α
  toList_empty {α : Type} : toList (empty : F α) = []
  toList_insert {α : Type} (x : α) (f : F α) : (toList (insert x f)).Perm (x :: toList f)
  popMin?_eq_none {α : Type} (prio : α → ℕ) (f : F α) : popMin? prio f = none ↔ toList f = []
  popMin?_eq_some {α : Type} (prio : α → ℕ) (f : F α) (x : α) (f' : F α) :
    popMin? prio f = some (x, f') →
      (toList f).Perm (x :: toList f') ∧ ∀ y ∈ toList f, prio x ≤ prio y

/-- Minimum extraction from a list, in linear time. -/
def listPopMin? {α : Type} (prio : α → ℕ) : List α → Option (α × List α)
  | [] => none
  | x :: xs =>
    match listPopMin? prio xs with
    | none => some (x, [])
    | some (y, ys) => if prio x ≤ prio y then some (x, xs) else some (y, x :: ys)

/-- The reference frontier. A Batteries heap is an efficiency instance, never needed for
correctness. -/
instance : Frontier List where
  empty := []
  insert := List.cons
  popMin? := listPopMin?
  toList := id
  toList_empty := rfl
  toList_insert _ _ := List.Perm.refl _
  popMin?_eq_none := sorry
  popMin?_eq_some := sorry

/-- A search node: the state, the actions taken from the initial state, their cost, and the
depth. -/
structure Node (S A : Type) where
  state : S
  path : List A
  pathCost : ℕ
  depth : ℕ

/-- The evaluation orders of Chapters 3 and 4, as data, so that one search definition serves
every monad. `key` evaluates a priority through the interface; the heuristic is consulted only by
the informed orders, once per generated node, and so is counted. A function of the node and the
heuristic value is the extensible alternative if contributors need orders beyond these. -/
inductive Priority where
  /-- Breadth-first search: depth. -/
  | depth
  /-- Uniform-cost search: path cost `g`. -/
  | pathCost
  /-- A*: `g + h`. -/
  | astar
  /-- Weighted A*: `g + w · h`. -/
  | weighted (w : ℕ)
  /-- Greedy best-first search: `h`. -/
  | greedy
  deriving DecidableEq, Repr

/-- Evaluate a priority at a node through the interface. -/
def Priority.key {S A : Type} {m : Type → Type w} [Monad m] (f : Priority) (P : ProblemM m S A)
    (n : Node S A) : m ℕ :=
  match f with
  | .depth => pure n.depth
  | .pathCost => pure n.pathCost
  | .astar => do return n.pathCost + (← P.heuristic n.state)
  | .weighted w => do return n.pathCost + w * (← P.heuristic n.state)
  | .greedy => P.heuristic n.state

section Polymorphic

variable {S A : Type} {m : Type → Type w} [Monad m] {F : Type → Type} [Frontier F]

/-- Generate the children of a node, charging one `result` and one `stepCost` call each. -/
def expandM (P : ProblemM m S A) (n : Node S A) : m (List (Node S A)) := do
  let as ← P.actions n.state
  as.mapM fun a => do
    let s' ← P.result n.state a
    let c ← P.stepCost n.state a
    return { state := s', path := n.path ++ [a], pathCost := n.pathCost + c, depth := n.depth + 1 }

/-- Generic best-first tree search, with fuel. Priorities are computed when a node is generated
and stored alongside it. The goal test is applied when a node is popped, as AIMA does, so that
uniform-cost search and A* are optimal. -/
def bestFirstM (P : ProblemM m S A) (f : Priority) :
    ℕ → F (ℕ × Node S A) → m (Option (List A))
  | 0, _ => return none
  | fuel + 1, fr =>
    match Frontier.popMin? Prod.fst fr with
    | none => return none
    | some ((_, n), fr') => do
      if ← P.isGoal n.state then
        return some n.path
      else
        let children ← expandM P n
        let keyed ← children.mapM fun c => do return ((← f.key P c), c)
        bestFirstM P f fuel (keyed.foldl (fun acc c => Frontier.insert c acc) fr')

/-- Best-first search from an initial state. -/
def bestFirstSearchM (P : ProblemM m S A) (f : Priority) (init : S) (fuel : ℕ) :
    m (Option (List A)) := do
  let n : Node S A := { state := init, path := [], pathCost := 0, depth := 0 }
  bestFirstM (F := F) P f fuel (Frontier.insert ((← f.key P n), n) Frontier.empty)

end Polymorphic

section Instances

variable {S A : Type} (p : Problem S A) (h : S → ℕ) (f : Priority) (fuel : ℕ)

/-- The pure search. Correctness is proved here. -/
def bestFirst : Option (List A) :=
  Id.run (bestFirstSearchM (F := List) (p.toM h) f p.initial fuel)

/-- The counted search. -/
def bestFirstQ (init : S) : FreeM (SearchQuery S A) (Option (List A)) :=
  bestFirstSearchM (F := List) SearchQuery.interface f init fuel

/-- Transfer: the counted search evaluates at the honest oracle to the pure search. Proved
through `IsMonadHom` from the polymorphic definition; the priority must commute with the
interpretation, which each named priority does. -/
theorem eval_bestFirstQ :
    (bestFirstQ f fuel p.initial).eval (p.oracle h) = bestFirst p h f fuel := sorry

/-- Soundness: a returned path is a solution. -/
theorem bestFirst_sound [DecidableEq A] {as : List A} (hr : bestFirst p h f fuel = some as) :
    p.IsSolution as := sorry

end Instances

/-! ## Milestone 3: uninformed search -/

section Uninformed

variable {S A : Type} [DecidableEq A] (p : Problem S A) (h : S → ℕ)

/-- Breadth-first search is complete and returns a solution of least depth. -/
theorem bfs_complete {as : List A} (hs : p.IsSolution as) :
    ∃ fuel bs, bestFirst p h .depth fuel = some bs ∧ bs.length ≤ as.length := sorry

/-- Uniform-cost search returns an optimal solution under positive step costs. -/
theorem ucs_optimal (hpos : p.PositiveCosts) (hs : p.Solvable) :
    ∃ fuel bs, bestFirst p h .pathCost fuel = some bs ∧ p.IsOptimalSolution bs := sorry

variable {m : Type → Type w} [Monad m]

/-- Depth-limited search: depth-first with a depth limit, and fuel. -/
def depthLimitedM (P : ProblemM m S A) (limit : ℕ) (init : S) (fuel : ℕ) :
    m (Option (List A)) := sorry

/-- Iterative deepening: depth-limited search for limits `0, 1, …, maxLimit`. -/
def iterativeDeepeningM (P : ProblemM m S A) (maxLimit : ℕ) (init : S) (fuel : ℕ) :
    m (Option (List A)) := sorry

/-- Generated nodes of breadth-first search: with branching at most `b` and a solution at depth
`d`, at most `(b^(d+1) - 1) / (b - 1)` `result` queries, for every oracle agreeing with `p` on
`actions`. Stated here at the honest oracle. -/
theorem bfs_generation_le (b : ℕ) (hb : ∀ s, (p.actions s).length ≤ b) {as : List A}
    (hs : p.IsSolution as) (fuel : ℕ) :
    (bestFirstQ .depth fuel p.initial).cost (p.oracle h) SearchQuery.generationWeight ≤
      (b ^ (as.length + 1) - 1) / (b - 1) := sorry

end Uninformed

/-! ## Milestone 4: heuristics and A* as tree search -/

section Informed

variable {S A : Type} [DecidableEq A] (p : Problem S A) (h : S → ℕ)

/-- A* tree search is optimal with an admissible heuristic, under positive step costs. -/
theorem astar_tree_optimal (hpos : p.PositiveCosts) (hadm : p.Admissible h) (hs : p.Solvable) :
    ∃ fuel bs, bestFirst p h .astar fuel = some bs ∧ p.IsOptimalSolution bs := sorry

/-- Weighted A* returns a solution within a factor `w` of optimal. -/
theorem weighted_astar_bound (w : ℕ) (hw : 1 ≤ w) (hpos : p.PositiveCosts)
    (hadm : p.Admissible h) {bs opt : List A} (hopt : p.IsOptimalSolution opt) (fuel : ℕ)
    (hr : bestFirst p h (.weighted w) fuel = some bs) :
    p.pathCost p.initial bs ≤ w * p.pathCost p.initial opt := sorry

variable {m : Type → Type w} [Monad m]

/-- Iterative-deepening A*: depth-first search bounded by `f = g + h`, with increasing bounds. -/
def idaStarM (P : ProblemM m S A) (init : S) (fuel : ℕ) : m (Option (List A)) := sorry

end Informed

/-! ## Milestone 5: graph search, the expansion count, and the digraph bridge -/

section GraphSearch

variable {S A : Type} [DecidableEq S] [DecidableEq A] {m : Type → Type w} [Monad m]

/-- Best-first graph search: an explored set ensures each state is expanded at most once. No
reopening; the reopening variant for admissible-but-inconsistent heuristics is a target. -/
def graphSearchM {F : Type → Type} [Frontier F] (P : ProblemM m S A) (f : Priority) (init : S)
    (fuel : ℕ) : m (Option (List A)) := sorry

variable (p : Problem S A) (h : S → ℕ) (f : Priority) (fuel : ℕ)

/-- The pure graph search. -/
def graphSearch : Option (List A) :=
  Id.run (graphSearchM (F := List) (p.toM h) f p.initial fuel)

/-- The counted graph search. -/
def graphSearchQ (init : S) : FreeM (SearchQuery S A) (Option (List A)) :=
  graphSearchM (F := List) SearchQuery.interface f init fuel

/-- A* graph search is optimal with a consistent heuristic. -/
theorem astar_graph_optimal (hcons : p.Consistent h) (hs : p.Solvable) :
    ∃ fuel bs, graphSearch p h .astar fuel = some bs ∧ p.IsOptimalSolution bs := sorry

/-- The expansion count: with a consistent heuristic, A* graph search expands each state at
most once, so its expansion cost is at most the number of reachable states. -/
theorem astar_graph_expansions (hcons : p.Consistent h) (hfin : {s | p.Reachable s}.Finite) :
    (graphSearchQ .astar fuel p.initial).cost (p.oracle h) SearchQuery.expansionWeight ≤
      {s | p.Reachable s}.ncard := sorry

end GraphSearch

/-- The problem of a finite weighted digraph: the bridge to explicit-graph formalisations. -/
def Problem.ofDigraph {V : Type} [FinEnum V] (G : Digraph V) [DecidableRel G.Adj]
    (w : V → V → ℕ) (src : V) (goal : V → Bool) : Problem V V where
  initial := src
  actions u := (FinEnum.toList V).filter fun v => decide (G.Adj u v)
  result _ v := v
  isGoal := goal
  stepCost u v := w u v

/-- The successor relation of the digraph problem is adjacency. -/
theorem Problem.ofDigraph_succ {V : Type} [FinEnum V] (G : Digraph V) [DecidableRel G.Adj]
    (w : V → V → ℕ) (src : V) (goal : V → Bool) (u v : V) :
    (Problem.ofDigraph G w src goal).Succ u v ↔ G.Adj u v := sorry

/-! ## Milestone 6: games, game value, and minimax -/

/-- The two players. Utilities are from `max`'s point of view. -/
inductive Player where
  | max
  | min
  deriving DecidableEq, Repr

/-- A two-player zero-sum deterministic game of perfect information. -/
structure Game (S A U : Type) [LinearOrder U] where
  initial : S
  toMove : S → Player
  actions : S → List A
  result : S → A → S
  isTerminal : S → Bool
  /-- The utility of a state, from the maximiser's point of view. Used as the static evaluation
  at the depth bound. -/
  utility : S → U

/-- The queries of the game interface. Weight one on `utility` counts leaf evaluations. -/
inductive GameQuery (S A U : Type) : Type → Type where
  | toMove (s : S) : GameQuery S A U Player
  | actions (s : S) : GameQuery S A U (List A)
  | result (s : S) (a : A) : GameQuery S A U S
  | isTerminal (s : S) : GameQuery S A U Bool
  | utility (s : S) : GameQuery S A U U

/-- The game interface in an arbitrary monad. -/
structure GameM (m : Type → Type w) (S A U : Type) where
  toMove : S → m Player
  actions : S → m (List A)
  result : S → A → m S
  isTerminal : S → m Bool
  utility : S → m U

namespace Game

variable {S A U : Type} [LinearOrder U] (g : Game S A U)

/-- Every non-terminal state has an action. -/
def WellFormed : Prop := ∀ s, g.isTerminal s = false → g.actions s ≠ []

/-- The pure interface. -/
def toM : GameM Id S A U where
  toMove s := pure (g.toMove s)
  actions s := pure (g.actions s)
  result s a := pure (g.result s a)
  isTerminal s := pure (g.isTerminal s)
  utility s := pure (g.utility s)

/-- The honest oracle. -/
def oracle : {ι : Type} → GameQuery S A U ι → ι
  | _, .toMove s => g.toMove s
  | _, .actions s => g.actions s
  | _, .result s a => g.result s a
  | _, .isTerminal s => g.isTerminal s
  | _, .utility s => g.utility s

end Game

namespace GameQuery

variable {S A U : Type}

/-- The counted interface. -/
def interface : GameM (FreeM (GameQuery S A U)) S A U where
  toMove s := FreeM.lift (.toMove s)
  actions s := FreeM.lift (.actions s)
  result s a := FreeM.lift (.result s a)
  isTerminal s := FreeM.lift (.isTerminal s)
  utility s := FreeM.lift (.utility s)

/-- Weight one on leaf evaluations. -/
def leafWeight : {ι : Type} → GameQuery S A U ι → ℕ
  | _, .utility _ => 1
  | _, _ => 0

end GameQuery

section GamePolymorphic

variable {S A U : Type} [LinearOrder U] {m : Type → Type w} [Monad m]

/-- The depth-bounded game value, with the static utility at the bound and at terminal states.
At a non-terminal state the value is the maximum, or minimum, over actions of the values of the
results; a state with no actions is valued statically. -/
def valueM (G : GameM m S A U) : ℕ → S → m U
  | 0, s => G.utility s
  | d + 1, s => do
    if ← G.isTerminal s then
      G.utility s
    else
      match ← G.actions s with
      | [] => G.utility s
      | a :: as =>
        let v ← valueM G d (← G.result s a)
        let vs ← as.mapM fun a => do valueM G d (← G.result s a)
        match ← G.toMove s with
        | .max => return vs.foldl max v
        | .min => return vs.foldl min v

/-- The minimax decision: an action achieving the value at depth `d + 1`. -/
def minimaxM (G : GameM m S A U) (d : ℕ) (s : S) : m (Option A) := sorry

/-- Fail-hard alpha-beta. -/
def alphaBetaM (G : GameM m S A U) : ℕ → S → U → U → m U := sorry

/-- Fail-soft alpha-beta. -/
def alphaBetaSoftM (G : GameM m S A U) : ℕ → S → U → U → m U := sorry

end GamePolymorphic

namespace Game

variable {S A U : Type} [LinearOrder U] (g : Game S A U) (d : ℕ) (s : S)

/-- The pure value. -/
def value : U := Id.run (valueM g.toM d s)

/-- The counted value. -/
def valueQ (_g : Game S A U) : FreeM (GameQuery S A U) U := valueM GameQuery.interface d s

/-- Transfer for the game value. -/
theorem eval_valueQ : (g.valueQ d s).eval g.oracle = g.value d s := sorry

/-- The value of a terminal state is its utility. -/
theorem value_of_isTerminal (ht : g.isTerminal s = true) : g.value d s = g.utility s := sorry

/-- The minimax decision achieves the value. -/
theorem minimax_spec (hw : g.WellFormed) (ht : g.isTerminal s = false) (hmax : g.toMove s = .max)
    {a : A} (ha : Id.run (minimaxM g.toM d s) = some a) :
    g.value d (g.result s a) = g.value (d + 1) s := sorry

/-- Beyond a finite horizon the value no longer depends on the depth bound. -/
theorem value_eq_of_horizon (hw : g.WellFormed) (horizon : ℕ)
    (hh : ∀ as : List A, as.length = horizon → g.isTerminal (as.foldl g.result s) = true)
    (d₁ d₂ : ℕ) (h₁ : horizon ≤ d₁) (h₂ : horizon ≤ d₂) :
    g.value d₁ s = g.value d₂ s := sorry

/-- Leaf count of minimax: at most `b ^ d` utility queries with branching at most `b`. -/
theorem valueQ_leaves_le (b : ℕ) (hb : ∀ s, (g.actions s).length ≤ b) :
    (g.valueQ d s).cost g.oracle GameQuery.leafWeight ≤ b ^ d := sorry

/-! ## Milestone 7: alpha-beta pruning -/

/-- Fail-hard alpha-beta returns the value clamped to the window. -/
theorem alphaBeta_eq_clamp (α β : U) (hab : α < β) :
    Id.run (alphaBetaM g.toM d s α β) = max α (min β (g.value d s)) := sorry

/-- Fail-soft alpha-beta agrees with the value inside the window and bounds it outside. -/
theorem alphaBetaSoft_spec (α β : U) (hab : α < β) :
    let v := Id.run (alphaBetaSoftM g.toM d s α β)
    (α < g.value d s → g.value d s < β → v = g.value d s) ∧
      (g.value d s ≤ α → v ≤ α) ∧ (β ≤ g.value d s → β ≤ v) := sorry

end Game

end EpsilonEridani.Search
