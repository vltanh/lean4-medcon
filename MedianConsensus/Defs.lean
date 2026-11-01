module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Order.Setoid.Basic

/-!
# Shared definitions

The objects of Hussain, Halappanavar, Chatterjee, Radicchi, Fortunato and Azad, *Parallel median
consensus clustering in complex networks*, Sci. Rep. 15, 3788 (2025): clusterings of a finite
vertex set, the co-clustering distance `δ`, the Mirkin distance, the objective of Eq. (4), the move
gain `ΔD` of Eq. (5), and the greedy algorithm of Eq. (6).

The block between the two markers is copied word for word into `Challenge.lean` by
`scripts/sync_challenge_defs.py`, so that the Challenge and the library have the same constants.

Conventions of the formalization, each discussed in `REPORT.md`, Section 6:

* A partition of the vertex set is a `Finpartition (univ : Finset V)`.
* A sum `∑_{uv}` of the paper runs over unordered pairs of distinct vertices. These are listed once
  each as `(u, v)` with `u < v`, in `pairs V`; the order on `V` only names the pairs, and nothing
  depends on it (`MedianConsensus.card_ordered_disagreements`, `MedianConsensus.two_mul_objective`).
* The sum `∑_u` of Eq. (5) runs over `u ≠ v`, as in the paper's Fig. 2.
-/

@[expose] public section

open Finset

namespace MedianConsensus

-- BEGIN SHARED DEFINITIONS

variable {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ}

/-- A partition, or clustering, of the vertex set: "a collection of non-overlapping clusters,
wherein each vertex is exclusively assigned to a single cluster". -/
abbrev Clustering (V : Type*) [Fintype V] [DecidableEq V] := Finpartition (univ : Finset V)

/-- The unordered pairs `{u, v}` of distinct vertices, each listed once as `(u, v)` with `u < v`.
The index set of the paper's sums `∑_{uv}`. -/
def pairs (V : Type*) [Fintype V] [LinearOrder V] : Finset (V × V) :=
  {p | p.1 < p.2}

/-- `σ_v(c)`: the indicator that the vertex `v` lies in the cluster `c`. -/
def sigma (v : V) (c : Finset V) : ℤ := if v ∈ c then 1 else 0

/-- **Eq. (2).** The co-clustering distance `δ_uv(P) = ∏_{c ∈ P} [1 - σ_u(c) σ_v(c)]`. -/
def delta (P : Clustering V) (u v : V) : ℤ := ∏ c ∈ P.parts, (1 - sigma u c * sigma v c)

/-- **Eq. (3).** The total co-clustering distance `δ_uv = ∑_{i=1}^k δ_uv(P_i)`. -/
def deltaTotal (Ps : Fin k → Clustering V) (u v : V) : ℤ := ∑ i, delta (Ps i) u v

/-- The vertices `u` and `v` lie in a common cluster of `P`. -/
def CoClustered (P : Clustering V) (u v : V) : Prop := ∃ c ∈ P.parts, u ∈ c ∧ v ∈ c

instance (P : Clustering V) (u v : V) : Decidable (CoClustered P u v) :=
  inferInstanceAs (Decidable (∃ c ∈ P.parts, u ∈ c ∧ v ∈ c))

/-- The entry `b` of the contingency table of Fig. 10: the pairs in the same cluster of `P` and in
different clusters of `Q`. -/
def contingencyB (P Q : Clustering V) : ℕ :=
  #{p ∈ pairs V | CoClustered P p.1 p.2 ∧ ¬CoClustered Q p.1 p.2}

/-- The entry `c` of the contingency table of Fig. 10: the pairs in different clusters of `P` and
in the same cluster of `Q`. -/
def contingencyC (P Q : Clustering V) : ℕ :=
  #{p ∈ pairs V | ¬CoClustered P p.1 p.2 ∧ CoClustered Q p.1 p.2}

/-- The Mirkin distance `d(P, Q) = b + c` of the paper's appendix: the number of pairs clustered
together in one of the two partitions but not in the other. -/
def mirkin (P Q : Clustering V) : ℕ := contingencyB P Q + contingencyC P Q

/-- The sum `∑_{i=1}^k d(C, P_i)` of Eq. (1), for the Mirkin distance. -/
def totalDistance (Ps : Fin k → Clustering V) (C : Clustering V) : ℕ := ∑ i, mirkin C (Ps i)

/-- **Eq. (1).** `C` is a median partition of `P_1, …, P_k`: it minimizes `∑_i d(C, P_i)`. The
`argmin` of the paper is a set, since the minimizer need not be unique. -/
def IsMedian (Ps : Fin k → Clustering V) (C : Clustering V) : Prop :=
  ∀ C', totalDistance Ps C ≤ totalDistance Ps C'

/-- The objective `∑_{uv} [k - 2 δ_uv] δ_uv(C)` of Eq. (4). -/
def objective (Ps : Fin k → Clustering V) (C : Clustering V) : ℤ :=
  ∑ p ∈ pairs V, ((k : ℤ) - 2 * deltaTotal Ps p.1 p.2) * delta C p.1 p.2

/-- **Eq. (5).** The change `ΔD_{v : c → c'} = ∑_u (k - 2 δ_uv) σ_u(c) - (k - 2 δ_uv) σ_u(c')` in
the objective when `v` moves from `c` to `c'`. The sum runs over `u ≠ v`, as in the paper's Fig. 2:
the term `u = v` would add `k` whenever `v ∈ c` and `v ∉ c'`
(`MedianConsensus.sum_all_eq_deltaD_add`). -/
def deltaD (Ps : Fin k → Clustering V) (v : V) (c c' : Finset V) : ℤ :=
  ∑ u ∈ univ.erase v,
    (((k : ℤ) - 2 * deltaTotal Ps u v) * sigma u c - ((k : ℤ) - 2 * deltaTotal Ps u v) * sigma u c')

/-- The clustering whose clusters are the fibres of a labelling of the vertices. -/
def ofLabels {L : Type*} [DecidableEq L] (f : V → L) : Clustering V :=
  letI : DecidableRel (Setoid.ker f).r := fun a b => inferInstanceAs (Decidable (f a = f b))
  Finpartition.ofSetoid (Setoid.ker f)

/-- The clustering `C` after the vertex `v` moves to the cluster `c'`: the vertex `v` gets the label
`c'`, and every other vertex keeps the cluster it had in `C` as its label. This is meant for a cluster
`c'` of `C`; if `c'` is not one, the label is new, and `v` becomes a singleton. -/
def moveVertex (C : Clustering V) (v : V) (c' : Finset V) : Clustering V :=
  ofLabels (Function.update C.part v c')

/-- `C_v`: the clusters of `C` in which `v` has at least one neighbour in the graph `G`. It may contain
the current cluster of `v`, for which `ΔD = 0`. -/
def candidateClusters (G : SimpleGraph V) [DecidableRel G.Adj] (C : Clustering V) (v : V) :
    Finset (Finset V) :=
  {c ∈ C.parts | ∃ u ∈ c, G.Adj v u}

/-- **Eq. (6).** `c'` is a value of `c*(v) = argmin_{c' ∈ C_v} ΔD_{v : c → c'}`, where `c` is the
current cluster of `v`. The minimizer need not be unique, and it does not exist when `C_v` is empty. -/
def IsBestMove (G : SimpleGraph V) [DecidableRel G.Adj] (Ps : Fin k → Clustering V)
    (C : Clustering V) (v : V) (c' : Finset V) : Prop :=
  c' ∈ candidateClusters G C v ∧
    ∀ c'' ∈ candidateClusters G C v, deltaD Ps v (C.part v) c' ≤ deltaD Ps v (C.part v) c''

/-- Some vertex `v` can be moved: a best move `c'` of `v` has `ΔD_{v : c → c'} < 0`. The algorithm
stops when this fails. -/
def CanMove (G : SimpleGraph V) [DecidableRel G.Adj] (Ps : Fin k → Clustering V)
    (C : Clustering V) : Prop :=
  ∃ v c', IsBestMove G Ps C v c' ∧ deltaD Ps v (C.part v) c' < 0

/-- One greedy move: a vertex `v` moves to a best cluster `c'` of Eq. (6), provided that
`ΔD_{v : c → c'} < 0`. -/
def GreedyStep (G : SimpleGraph V) [DecidableRel G.Adj] (Ps : Fin k → Clustering V)
    (C C' : Clustering V) : Prop :=
  ∃ v c', IsBestMove G Ps C v c' ∧ deltaD Ps v (C.part v) c' < 0 ∧ C' = moveVertex C v c'

/-- The inter-cluster edges of `G`, each listed once as `(u, v)` with `u < v`. Their number is the
paper's `m̂`. -/
def interEdges (G : SimpleGraph V) [DecidableRel G.Adj] (C : Clustering V) : Finset (V × V) :=
  {p ∈ pairs V | G.Adj p.1 p.2 ∧ ¬CoClustered C p.1 p.2}

/-- The potential moves of an iteration: the pairs `(v, c')` with `c' ∈ C_v` a cluster other than
the current cluster of `v`. -/
def potentialMoves (G : SimpleGraph V) [DecidableRel G.Adj] (C : Clustering V) :
    Finset (V × Finset V) :=
  {m ∈ (univ : Finset V) ×ˢ C.parts | m.2 ∈ candidateClusters G C m.1 ∧ m.2 ≠ C.part m.1}

/-- The vertices of the paper's Figs. 1 and 2 are `v₀, …, v₁₁`, numbered as there. The input
partitions `P₁, …, P₄` of Fig. 1, as cluster assignment vectors with colours red = 0, yellow = 1,
blue = 2, grey = 3. -/
def figureLabels : Fin 4 → Fin 12 → Fin 4 :=
  ![![0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 2],
    ![0, 0, 2, 1, 0, 0, 0, 1, 2, 1, 2, 2],
    ![3, 0, 0, 0, 3, 0, 3, 1, 2, 1, 2, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2]]

/-- The input partitions `P₁, …, P₄` of Fig. 1. -/
def figurePartitions : Fin 4 → Clustering (Fin 12) := fun i => ofLabels (figureLabels i)

/-- The 23 edges of the graph of Figs. 1 and 2, read from the right-hand panel of Fig. 1. -/
def figureEdges : List (Fin 12 × Fin 12) :=
  [(0, 1), (0, 3), (0, 4), (0, 6), (1, 2), (1, 3), (1, 5), (2, 3), (2, 8), (2, 11), (3, 4), (3, 5),
    (3, 9), (4, 5), (4, 6), (5, 6), (5, 7), (7, 8), (7, 9), (8, 10), (8, 11), (9, 11), (10, 11)]

/-- The graph of Figs. 1 and 2. -/
def figureGraph : SimpleGraph (Fin 12) := SimpleGraph.fromRel fun a b => (a, b) ∈ figureEdges

instance : DecidableRel figureGraph.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel fun a b => (a, b) ∈ figureEdges).Adj)

/-- The consensus clustering `C = {c₁, c₂, c₃, c₄}` of Fig. 2, labelling `c_j` by `j`. -/
def figureConsensus : Clustering (Fin 12) :=
  ofLabels (![3, 2, 2, 1, 3, 3, 3, 1, 4, 1, 4, 4] : Fin 12 → Fin 5)

/-- The cluster `c₁` of Fig. 2. -/
def figureC1 : Finset (Fin 12) := {3, 7, 9}

/-- The cluster `c₂` of Fig. 2. -/
def figureC2 : Finset (Fin 12) := {1, 2}

/-- The cluster `c₃` of Fig. 2. -/
def figureC3 : Finset (Fin 12) := {0, 4, 5, 6}

/-- The cluster `c₄` of Fig. 2. -/
def figureC4 : Finset (Fin 12) := {8, 10, 11}

-- END SHARED DEFINITIONS

end MedianConsensus
