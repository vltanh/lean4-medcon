module

public import MedianConsensus.Algorithm.Complexity
public import MedianConsensus.Algorithm.Examples
public import MedianConsensus.Algorithm.Parallel
public import MedianConsensus.Evaluation.Rand
public import MedianConsensus.GraphAware.Figures
public import MedianConsensus.Grouping

/-!
# The proofs of the statements of record

Each theorem of `Challenge.lean`, repeated word for word and proved from the library. This module
imports the whole library, and serves as its entry point.
-/

@[expose] public section

open Finset
open scoped symmDiff

namespace MedianConsensus.Challenge

variable {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ}

/-- **Eq. (2).** `δ_uv(P)` is `0` if `u` and `v` are co-clustered in `P`, and `1` otherwise. -/
theorem equation2 (P : Clustering V) (u v : V) :
    delta P u v = if CoClustered P u v then 0 else 1 :=
  MedianConsensus.equation2 P u v

/-- **Eq. (3).** `δ_uv` counts the partitions in which `u` and `v` are not clustered together. -/
theorem equation3 (Ps : Fin k → Clustering V) (u v : V) :
    deltaTotal Ps u v = #{i | ¬CoClustered (Ps i) u v} :=
  MedianConsensus.equation3 Ps u v

/-- **Eq. (7).** `d(P, Q) = b + c = ∑_{uv} (δ_uv(P) + δ_uv(Q) - 2 δ_uv(P) δ_uv(Q))`. -/
theorem equation7 (P Q : Clustering V) :
    (mirkin P Q : ℤ) =
      ∑ p ∈ pairs V, (delta P p.1 p.2 + delta Q p.1 p.2 - 2 * delta P p.1 p.2 * delta Q p.1 p.2) :=
  MedianConsensus.equation7 P Q

/-- The Mirkin distance is the size of the symmetric difference of the sets of co-clustered pairs. -/
theorem mirkin_eq_card_symmDiff (P Q : Clustering V) :
    mirkin P Q =
      #({p ∈ pairs V | CoClustered P p.1 p.2} ∆ {p ∈ pairs V | CoClustered Q p.1 p.2}) :=
  MedianConsensus.mirkin_eq_card_symmDiff_coPairs P Q

/-- The Mirkin distance is a metric on the partitions of `V`. -/
theorem mirkin_isMetric :
    (∀ P Q : Clustering V, mirkin P Q = 0 ↔ P = Q) ∧
      (∀ P Q : Clustering V, mirkin P Q = mirkin Q P) ∧
        ∀ P Q R : Clustering V, mirkin P R ≤ mirkin P Q + mirkin Q R :=
  MedianConsensus.mirkin_isMetric

/-- Counting ordered pairs gives `2 d(P, Q)`, which accounts for the "(twice)" of the paper's Methods
section. -/
theorem card_ordered_disagreements (P Q : Clustering V) :
    #{p ∈ (univ : Finset V).offDiag | ¬(CoClustered P p.1 p.2 ↔ CoClustered Q p.1 p.2)} =
      2 * mirkin P Q :=
  MedianConsensus.card_ordered_disagreements P Q

/-- The Mirkin metric of the literature, `∑_c |c|² + ∑_c' |c'|² - 2 ∑_c ∑_c' |c ∩ c'|²`, is
`2 d(P, Q)`. This identifies `mirkin` with the known distance. -/
theorem sum_sq_parts_add_sum_sq_parts (P Q : Clustering V) :
    ∑ c ∈ P.parts, #c ^ 2 + ∑ c ∈ Q.parts, #c ^ 2 =
      2 * mirkin P Q + 2 * ∑ c ∈ P.parts, ∑ c' ∈ Q.parts, #(c ∩ c') ^ 2 :=
  MedianConsensus.sum_sq_parts_add_sum_sq_parts P Q

/-- **Appendix.** `∑_i d(C, P_i) = ∑_{uv} δ_uv + ∑_{uv} [k - 2 δ_uv] δ_uv(C)`. -/
theorem appendix_identity (Ps : Fin k → Clustering V) (C : Clustering V) :
    (totalDistance Ps C : ℤ) = ∑ p ∈ pairs V, deltaTotal Ps p.1 p.2 + objective Ps C :=
  MedianConsensus.appendix_identity Ps C

/-- **Eq. (4).** The median partitions are the minimizers of `∑_{uv} [k - 2 δ_uv] δ_uv(C)`. -/
theorem equation4 (Ps : Fin k → Clustering V) (C : Clustering V) :
    IsMedian Ps C ↔ ∀ C', objective Ps C ≤ objective Ps C' :=
  MedianConsensus.equation4 Ps C

/-- **Eq. (1).** A median partition exists. -/
theorem equation1 (Ps : Fin k → Clustering V) : ∃ C, IsMedian Ps C :=
  MedianConsensus.equation1 Ps

/-- A move does not change whether two vertices other than `v` are co-clustered. -/
theorem moveVertex_of_ne (C : Clustering V) {v x y : V} (c' : Finset V) (hx : x ≠ v) (hy : y ≠ v) :
    CoClustered (moveVertex C v c') x y ↔ CoClustered C x y :=
  coClustered_moveVertex_of_ne C c' hx hy

/-- After `v` moves to the cluster `c'`, the vertices co-clustered with `v` are those of `c'`. -/
theorem moveVertex_self (C : Clustering V) {v u : V} {c' : Finset V} (hc' : c' ∈ C.parts)
    (hu : u ≠ v) : CoClustered (moveVertex C v c') u v ↔ u ∈ c' :=
  coClustered_moveVertex_self C hc' hu

/-- **Eq. (5).** When `v` moves from its cluster `c` to a cluster `c'`, the objective changes by exactly
`ΔD_{v : c → c'}`, and `ΔD` has the second form of Eq. (5). -/
theorem equation5 (Ps : Fin k → Clustering V) (C : Clustering V) (v : V) {c' : Finset V}
    (hc' : c' ∈ C.parts) :
    objective Ps (moveVertex C v c') - objective Ps C = deltaD Ps v (C.part v) c' ∧
      deltaD Ps v (C.part v) c' =
        ∑ u ∈ univ.erase v, (sigma u c' - sigma u (C.part v)) * (2 * deltaTotal Ps u v - k) :=
  MedianConsensus.equation5 Ps C v hc'

/-- "When `ΔD_{v : c → c'}` is negative, moving `v` to the new cluster `c'` reduces the overall
disagreements." -/
theorem moveVertex_reduces (Ps : Fin k → Clustering V) (C : Clustering V) (v : V) {c' : Finset V}
    (hc' : c' ∈ C.parts) (h : deltaD Ps v (C.part v) c' < 0) :
    totalDistance Ps (moveVertex C v c') < totalDistance Ps C :=
  MedianConsensus.moveVertex_reduces Ps C v hc' h

/-- **Eq. (6).** The `argmin` of Eq. (6) exists exactly when `v` has a neighbour. -/
theorem equation6 (G : SimpleGraph V) [DecidableRel G.Adj] (Ps : Fin k → Clustering V)
    (C : Clustering V) (v : V) : (∃ c', IsBestMove G Ps C v c') ↔ ∃ u, G.Adj v u :=
  MedianConsensus.equation6 G Ps C v

/-- The stopping condition: no vertex can be moved exactly when no candidate cluster of any vertex
has `ΔD < 0`. -/
theorem not_canMove_iff (G : SimpleGraph V) [DecidableRel G.Adj] (Ps : Fin k → Clustering V)
    (C : Clustering V) :
    ¬CanMove G Ps C ↔ ∀ v, ∀ c' ∈ candidateClusters G C v, 0 ≤ deltaD Ps v (C.part v) c' :=
  MedianConsensus.not_canMove_iff G Ps C

/-- There is no infinite sequence of greedy moves. -/
theorem greedyStep_wellFounded (G : SimpleGraph V) [DecidableRel G.Adj]
    (Ps : Fin k → Clustering V) : WellFounded fun C' C => GreedyStep G Ps C C' :=
  MedianConsensus.greedyStep_wellFounded Ps

/-- From every partition, in particular from the singletons `⊥`, some sequence of greedy moves reaches
a partition in which no vertex can be moved. -/
theorem exists_stable (G : SimpleGraph V) [DecidableRel G.Adj] (Ps : Fin k → Clustering V)
    (C₀ : Clustering V) :
    ∃ C, Relation.ReflTransGen (GreedyStep G Ps) C₀ C ∧ ¬CanMove G Ps C :=
  MedianConsensus.exists_stable Ps C₀

/-- A sequence of greedy moves has at most `k n (n - 1) / 2` moves. -/
theorem greedy_run_length_le (G : SimpleGraph V) [DecidableRel G.Adj] {Ps : Fin k → Clustering V}
    {s : ℕ → Clustering V} {m : ℕ} (h : ∀ i < m, GreedyStep G Ps (s i) (s (i + 1))) :
    2 * m ≤ k * (Fintype.card V * (Fintype.card V - 1)) :=
  MedianConsensus.greedy_run_length_le h

/-- "This greedy moving policy … does not guarantee an optimal solution": on the complete graph on four
vertices, with three input partitions, runs from the singletons stop, and every partition at which a run
stops fails to be a median partition. -/
theorem greedy_not_optimal :
    ∃ Ps : Fin 3 → Clustering (Fin 4),
      (∃ C, Relation.ReflTransGen (GreedyStep ⊤ Ps) ⊥ C ∧ ¬CanMove ⊤ Ps C) ∧
        ∀ C, Relation.ReflTransGen (GreedyStep ⊤ Ps) ⊥ C → ¬CanMove ⊤ Ps C → ¬IsMedian Ps C :=
  MedianConsensus.greedy_not_optimal

/-- "If there are `m̂` inter-cluster edges, the number of potential moves is at most `2 m̂`." -/
theorem card_potentialMoves_le (G : SimpleGraph V) [DecidableRel G.Adj] (C : Clustering V) :
    #(potentialMoves G C) ≤ 2 * #(interEdges G C) :=
  MedianConsensus.card_potentialMoves_le G C

/-- **Fig. 1.** `δ_{v₀v₁} = 1`, `δ_{v₀v₄} = 0` and `δ_{v₃v₉} = 2`. -/
theorem figure1 :
    deltaTotal figurePartitions 0 1 = 1 ∧ deltaTotal figurePartitions 0 4 = 0 ∧
      deltaTotal figurePartitions 3 9 = 2 :=
  MedianConsensus.figure1

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
        totalDistance figurePartitions (moveVertex figureConsensus 3 figureC2) = 4 :=
  MedianConsensus.figure2

end MedianConsensus.Challenge
