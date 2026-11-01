module

public import MedianConsensus.GraphAware.BestMove

/-!
# Counting moves and computation

Section "Computation and memory complexity" of the paper. The paper's `O(·)` statements are informal.
This file makes the combinatorial content precise, for an explicit count of operations: to evaluate
one term of Eq. (5) for a cluster `c`, one computes `δ_uv` for each `u ∈ c`, at `k` comparisons each.
-/

@[expose] public section

open Finset

namespace MedianConsensus

variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Computation and memory complexity** (`claim:pairs-count`). The number of pairs of `n` objects
is `n (n - 1) / 2`, which is `k (k - 1) / 2` for the `k` input partitions. -/
theorem card_pairs : #(pairs V) = Fintype.card V * (Fintype.card V - 1) / 2 := by
  sorry

/-- **Computation and memory complexity** (`claim:moves-at-most`). "If there are `m̂` inter-cluster
edges, the number of potential moves is at most `2 m̂`." -/
theorem card_potentialMoves_le (C : Clustering V) :
    #(potentialMoves G C) ≤ 2 * #(interEdges G C) := by
  sorry

/-- **Graph-aware consensus clustering** (`claim:moves-at-most-m`). "At most `O(m)` moves are
considered": `m̂ ≤ m`. -/
theorem card_interEdges_le (C : Clustering V) : #(interEdges G C) ≤ #G.edgeFinset := by
  sorry

/-- A vertex has at most `b - 1` potential moves, one per other cluster, so an iteration has at most
`n (b - 1)` potential moves, a bound independent of `m̂`. -/
theorem card_potentialMoves_le_mul (C : Clustering V) :
    #(potentialMoves G C) ≤ Fintype.card V * (#C.parts - 1) := by
  sorry

/-- The operations needed to evaluate the two terms of Eq. (5) for a move `m = (v, c')`, with `k`
comparisons per vertex of `c` and of `c'`. -/
def moveCost (C : Clustering V) (k : ℕ) (m : V × Finset V) : ℕ :=
  (#(C.part m.1) + #m.2) * k

/-- The operations of one iteration: the two terms of Eq. (5) for every potential move. -/
def iterationCost (C : Clustering V) (k : ℕ) : ℕ :=
  ∑ m ∈ potentialMoves G C, moveCost C k m

/-- "On average, each cluster then contains `n / b` vertices": `b` clusters of size `s` cover the
`n` vertices. -/
theorem card_parts_mul_of_equal_size {C : Clustering V} {s : ℕ} (hs : ∀ c ∈ C.parts, #c = s) :
    #C.parts * s = Fintype.card V := by
  sorry

/-- **Computation and memory complexity** (`claim:iteration-cost`). The bound `O(m̂ n k_h / b)`, with
its constant, for clusters of equal size: the cost of an iteration satisfies
`cost · b ≤ 4 m̂ n k_h`. -/
theorem iterationCost_mul_parts_le {C : Clustering V} {s : ℕ} (hs : ∀ c ∈ C.parts, #c = s) (k : ℕ) :
    iterationCost G C k * #C.parts ≤ 4 * #(interEdges G C) * Fintype.card V * k := by
  sorry

/-- For clusters of equal size, the cost of an iteration is at most `2 n² k_h`, whatever `m̂` and `b`
are. -/
theorem iterationCost_le_quadratic {C : Clustering V} {s : ℕ} (hs : ∀ c ∈ C.parts, #c = s) (k : ℕ) :
    iterationCost G C k ≤ 2 * Fintype.card V ^ 2 * k := by
  sorry

/-- **Computation and memory complexity** (`claim:both-conditions`). The paper says that, for
same-size clusters, "`m̂` very high and `b` very low" "cannot occur simultaneously". They can: for
the complete bipartite graph on two sides of size `s` and the two sides as clusters, `b = 2` and
`m̂ = s² = n² / 4`. -/
theorem both_conditions_occur (s : ℕ) (hs : 0 < s) :
    ∃ (G : SimpleGraph (Fin (2 * s))) (_ : DecidableRel G.Adj) (C : Clustering (Fin (2 * s))),
      #C.parts = 2 ∧ (∀ c ∈ C.parts, #c = s) ∧ #(interEdges G C) = s ^ 2 := by
  sorry

end MedianConsensus
