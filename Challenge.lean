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
# Parallel median consensus clustering in complex networks: the statements of record

This file states the main mathematical results of Hussain, Halappanavar, Chatterjee, Radicchi, Fortunato
and Azad, *Parallel median consensus clustering in complex networks*, Sci. Rep. 15, 3788 (2025),
doi:10.1038/s41598-025-87479-6. The paper has no numbered theorems. Its mathematics is in Eqs. (1)-(7),
the derivations in its appendix, the worked example of Figs. 1 and 2, and some claims in running text.

**The problem.** Given partitions `P₁, …, P_k` of a vertex set, a median partition minimizes
`∑_i d(C, P_i)` over all partitions `C`, for the Mirkin distance `d(P, Q)`, the number of pairs of
vertices clustered together in one of `P`, `Q` and not in the other.

* `equation2`, `equation3`: the co-clustering distance `δ_uv(P)` is a product over the clusters, with
  value `0` or `1`; the total `δ_uv` counts the input partitions that separate `u` and `v`.
* `equation7`, `mirkin_eq_card_symmDiff`, `mirkin_isMetric`: the Mirkin distance in terms of `δ`, as a
  symmetric difference, and as a metric. `card_ordered_disagreements` and
  `sum_sq_parts_add_sum_sq_parts` relate it to the Mirkin metric of the literature, which is `2 d`.
* `appendix_identity`, `equation4`, `equation1`: the derivation of the objective of Eq. (4), and the
  existence of median partitions.

**The algorithm.** Starting from the singletons, a vertex moves to a cluster containing a neighbour in a
graph `G`, when this decreases the objective. The graph and the input partitions are unrelated by
hypothesis, as in the paper.

* `moveVertex_of_ne`, `moveVertex_self`: what a move to a cluster does.
* `equation5`, `moveVertex_reduces`: the objective changes by exactly `ΔD`, and a negative `ΔD` reduces
  the total distance.
* `equation6`, `not_canMove_iff`: the best move of a vertex, and the stopping condition.
* `greedyStep_wellFounded`, `exists_stable`, `greedy_run_length_le`: moves made one at a time stop, in at
  most `k n (n - 1) / 2` moves. The paper does not state this; its stopping condition needs it.
* `greedy_not_optimal`: on one instance, the algorithm stops only at partitions that are not medians.
* `card_potentialMoves_le`: an iteration has at most `2 m̂` potential moves.
* `figure1`, `figure2`: the paper's worked example, computed from these definitions. They show that the
  definitions are consistent with the paper's own computation.

**Conventions.**

* A partition is a `Finpartition (univ : Finset V)`.
* The sums `∑_uv` of the paper are over unordered pairs of distinct vertices, listed once each as
  `(u, v)` with `u < v`. The appendix's `d = b + c` is then this count, and Fig. 2's "reduces the total
  distance by 4" holds. The order on `V` only names the pairs: `card_ordered_disagreements` counts the
  disagreements without it. The paper's Methods section says that the distance "counts (twice)" the
  pairs, which is the count over ordered pairs and the Mirkin metric of the literature.
* The sum `∑_u` of Eq. (5) is over `u ≠ v`. The paper's Fig. 2 and its authors' code compute it so. With
  `u = v` included it would be larger by `k` whenever `v ∈ c` and `v ∉ c'`, and Fig. 2's move would have
  `ΔD = 0`.
* Eq. (3) prints `P_k` in the summand, for `P_i`, a misprint.
* The clustering after a move is defined through labels: `v` gets the label `c'`, and every other vertex
  keeps its old cluster as its label. `moveVertex_of_ne` and `moveVertex_self` characterize it when `c'`
  is a cluster, which is why `equation5` and `moveVertex_reduces` assume so.
* `C_v` may contain the current cluster of `v`, with `ΔD = 0`, so `IsBestMove` may pick it; such a pick is
  not a move, since a move needs `ΔD < 0`.
* `GreedyStep` is one move at a time. The paper's iteration performs all the moves together, after
  "validation checks" that it does not specify. That version is not stated here.

**Not stated here, but proved in the library.** The Hamming description of `δ_uv`; the Rand distance and
the split-join distance; the grouping of homogeneous partitions; the iteration without validation checks;
the role of the order of the moves; the bounds on the cost of an iteration; the claims that the
formalization corrects. `REPORT.md` lists them, with what is not formalized: the experiments, the
NP-completeness of the problem, and the variation of information.
-/

@[expose] public section

open Finset
open scoped symmDiff

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

namespace MedianConsensus.Challenge

variable {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ}

/-- **Eq. (2).** `δ_uv(P)` is `0` if `u` and `v` are co-clustered in `P`, and `1` otherwise. -/
theorem equation2 (P : Clustering V) (u v : V) :
    delta P u v = if CoClustered P u v then 0 else 1 := by
  sorry

/-- **Eq. (3).** `δ_uv` counts the partitions in which `u` and `v` are not clustered together. -/
theorem equation3 (Ps : Fin k → Clustering V) (u v : V) :
    deltaTotal Ps u v = #{i | ¬CoClustered (Ps i) u v} := by
  sorry

/-- **Eq. (7).** `d(P, Q) = b + c = ∑_{uv} (δ_uv(P) + δ_uv(Q) - 2 δ_uv(P) δ_uv(Q))`. -/
theorem equation7 (P Q : Clustering V) :
    (mirkin P Q : ℤ) =
      ∑ p ∈ pairs V, (delta P p.1 p.2 + delta Q p.1 p.2 - 2 * delta P p.1 p.2 * delta Q p.1 p.2) := by
  sorry

/-- The Mirkin distance is the size of the symmetric difference of the sets of co-clustered pairs. -/
theorem mirkin_eq_card_symmDiff (P Q : Clustering V) :
    mirkin P Q =
      #({p ∈ pairs V | CoClustered P p.1 p.2} ∆ {p ∈ pairs V | CoClustered Q p.1 p.2}) := by
  sorry

/-- The Mirkin distance is a metric on the partitions of `V`. -/
theorem mirkin_isMetric :
    (∀ P Q : Clustering V, mirkin P Q = 0 ↔ P = Q) ∧
      (∀ P Q : Clustering V, mirkin P Q = mirkin Q P) ∧
        ∀ P Q R : Clustering V, mirkin P R ≤ mirkin P Q + mirkin Q R := by
  sorry

/-- Counting ordered pairs gives `2 d(P, Q)`, which accounts for the "(twice)" of the paper's Methods
section. -/
theorem card_ordered_disagreements (P Q : Clustering V) :
    #{p ∈ (univ : Finset V).offDiag | ¬(CoClustered P p.1 p.2 ↔ CoClustered Q p.1 p.2)} =
      2 * mirkin P Q := by
  sorry

/-- The Mirkin metric of the literature, `∑_c |c|² + ∑_c' |c'|² - 2 ∑_c ∑_c' |c ∩ c'|²`, is
`2 d(P, Q)`. This identifies `mirkin` with the known distance. -/
theorem sum_sq_parts_add_sum_sq_parts (P Q : Clustering V) :
    ∑ c ∈ P.parts, #c ^ 2 + ∑ c ∈ Q.parts, #c ^ 2 =
      2 * mirkin P Q + 2 * ∑ c ∈ P.parts, ∑ c' ∈ Q.parts, #(c ∩ c') ^ 2 := by
  sorry

/-- **Appendix.** `∑_i d(C, P_i) = ∑_{uv} δ_uv + ∑_{uv} [k - 2 δ_uv] δ_uv(C)`. -/
theorem appendix_identity (Ps : Fin k → Clustering V) (C : Clustering V) :
    (totalDistance Ps C : ℤ) = ∑ p ∈ pairs V, deltaTotal Ps p.1 p.2 + objective Ps C := by
  sorry

/-- **Eq. (4).** The median partitions are the minimizers of `∑_{uv} [k - 2 δ_uv] δ_uv(C)`. -/
theorem equation4 (Ps : Fin k → Clustering V) (C : Clustering V) :
    IsMedian Ps C ↔ ∀ C', objective Ps C ≤ objective Ps C' := by
  sorry

/-- **Eq. (1).** A median partition exists. -/
theorem equation1 (Ps : Fin k → Clustering V) : ∃ C, IsMedian Ps C := by
  sorry

/-- A move does not change whether two vertices other than `v` are co-clustered. -/
theorem moveVertex_of_ne (C : Clustering V) {v x y : V} (c' : Finset V) (hx : x ≠ v) (hy : y ≠ v) :
    CoClustered (moveVertex C v c') x y ↔ CoClustered C x y := by
  sorry

/-- After `v` moves to the cluster `c'`, the vertices co-clustered with `v` are those of `c'`. -/
theorem moveVertex_self (C : Clustering V) {v u : V} {c' : Finset V} (hc' : c' ∈ C.parts)
    (hu : u ≠ v) : CoClustered (moveVertex C v c') u v ↔ u ∈ c' := by
  sorry

/-- **Eq. (5).** When `v` moves from its cluster `c` to a cluster `c'`, the objective changes by exactly
`ΔD_{v : c → c'}`, and `ΔD` has the second form of Eq. (5). -/
theorem equation5 (Ps : Fin k → Clustering V) (C : Clustering V) (v : V) {c' : Finset V}
    (hc' : c' ∈ C.parts) :
    objective Ps (moveVertex C v c') - objective Ps C = deltaD Ps v (C.part v) c' ∧
      deltaD Ps v (C.part v) c' =
        ∑ u ∈ univ.erase v, (sigma u c' - sigma u (C.part v)) * (2 * deltaTotal Ps u v - k) := by
  sorry

/-- "When `ΔD_{v : c → c'}` is negative, moving `v` to the new cluster `c'` reduces the overall
disagreements." -/
theorem moveVertex_reduces (Ps : Fin k → Clustering V) (C : Clustering V) (v : V) {c' : Finset V}
    (hc' : c' ∈ C.parts) (h : deltaD Ps v (C.part v) c' < 0) :
    totalDistance Ps (moveVertex C v c') < totalDistance Ps C := by
  sorry

/-- **Eq. (6).** The `argmin` of Eq. (6) exists exactly when `v` has a neighbour. -/
theorem equation6 (G : SimpleGraph V) [DecidableRel G.Adj] (Ps : Fin k → Clustering V)
    (C : Clustering V) (v : V) : (∃ c', IsBestMove G Ps C v c') ↔ ∃ u, G.Adj v u := by
  sorry

/-- The stopping condition: no vertex can be moved exactly when no candidate cluster of any vertex
has `ΔD < 0`. -/
theorem not_canMove_iff (G : SimpleGraph V) [DecidableRel G.Adj] (Ps : Fin k → Clustering V)
    (C : Clustering V) :
    ¬CanMove G Ps C ↔ ∀ v, ∀ c' ∈ candidateClusters G C v, 0 ≤ deltaD Ps v (C.part v) c' := by
  sorry

/-- There is no infinite sequence of greedy moves. -/
theorem greedyStep_wellFounded (G : SimpleGraph V) [DecidableRel G.Adj]
    (Ps : Fin k → Clustering V) : WellFounded fun C' C => GreedyStep G Ps C C' := by
  sorry

/-- From every partition, in particular from the singletons `⊥`, some sequence of greedy moves reaches
a partition in which no vertex can be moved. -/
theorem exists_stable (G : SimpleGraph V) [DecidableRel G.Adj] (Ps : Fin k → Clustering V)
    (C₀ : Clustering V) :
    ∃ C, Relation.ReflTransGen (GreedyStep G Ps) C₀ C ∧ ¬CanMove G Ps C := by
  sorry

/-- A sequence of greedy moves has at most `k n (n - 1) / 2` moves. -/
theorem greedy_run_length_le (G : SimpleGraph V) [DecidableRel G.Adj] {Ps : Fin k → Clustering V}
    {s : ℕ → Clustering V} {m : ℕ} (h : ∀ i < m, GreedyStep G Ps (s i) (s (i + 1))) :
    2 * m ≤ k * (Fintype.card V * (Fintype.card V - 1)) := by
  sorry

/-- "This greedy moving policy … does not guarantee an optimal solution": on the complete graph on four
vertices, with three input partitions, runs from the singletons stop, and every partition at which a run
stops fails to be a median partition. -/
theorem greedy_not_optimal :
    ∃ Ps : Fin 3 → Clustering (Fin 4),
      (∃ C, Relation.ReflTransGen (GreedyStep ⊤ Ps) ⊥ C ∧ ¬CanMove ⊤ Ps C) ∧
        ∀ C, Relation.ReflTransGen (GreedyStep ⊤ Ps) ⊥ C → ¬CanMove ⊤ Ps C → ¬IsMedian Ps C := by
  sorry

/-- "If there are `m̂` inter-cluster edges, the number of potential moves is at most `2 m̂`." -/
theorem card_potentialMoves_le (G : SimpleGraph V) [DecidableRel G.Adj] (C : Clustering V) :
    #(potentialMoves G C) ≤ 2 * #(interEdges G C) := by
  sorry

/-- **Fig. 1.** `δ_{v₀v₁} = 1`, `δ_{v₀v₄} = 0` and `δ_{v₃v₉} = 2`. -/
theorem figure1 :
    deltaTotal figurePartitions 0 1 = 1 ∧ deltaTotal figurePartitions 0 4 = 0 ∧
      deltaTotal figurePartitions 3 9 = 2 := by
  sorry

/-- **Fig. 2.** The clusters of the consensus are `c₁, …, c₄`; `v₃` lies in `c₁`; `c₄` contains no
neighbour of `v₃`; the sums over `c₁`, `c₂`, `c₃` are `0`, `4`, `2`, with `v₃` left out of the first;
`ΔD_{v₃ : c₁ → c₂} = -4` and `ΔD_{v₃ : c₁ → c₃} = -2`; the best move is to `c₂`, and it reduces the
total distance by `4`. -/
theorem figure2 :
    figureConsensus.parts = {figureC1, figureC2, figureC3, figureC4} ∧
      figureConsensus.part 3 = figureC1 ∧
      candidateClusters figureGraph figureConsensus 3 = {figureC1, figureC2, figureC3} ∧
      ∑ u ∈ figureC1.erase 3, ((4 : ℤ) - 2 * deltaTotal figurePartitions u 3) = 0 ∧
      ∑ u ∈ figureC2, ((4 : ℤ) - 2 * deltaTotal figurePartitions u 3) = 4 ∧
      ∑ u ∈ figureC3, ((4 : ℤ) - 2 * deltaTotal figurePartitions u 3) = 2 ∧
      deltaD figurePartitions 3 figureC1 figureC2 = -4 ∧
      deltaD figurePartitions 3 figureC1 figureC3 = -2 ∧
      IsBestMove figureGraph figurePartitions figureConsensus 3 figureC2 ∧
      (totalDistance figurePartitions figureConsensus : ℤ) -
        totalDistance figurePartitions (moveVertex figureConsensus 3 figureC2) = 4 := by
  sorry

end MedianConsensus.Challenge
