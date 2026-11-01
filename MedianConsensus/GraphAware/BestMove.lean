module

public import MedianConsensus.GraphAware.Move

/-!
# The best move of a vertex: Eq. (6)
-/

@[expose] public section

open Finset

namespace MedianConsensus

variable {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ}
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The clusters of `C_v` are the clusters of the neighbours of `v`. -/
theorem mem_candidateClusters_iff (C : Clustering V) (v : V) (c' : Finset V) :
    c' ∈ candidateClusters G C v ↔ ∃ u, G.Adj v u ∧ c' = C.part u := by
  sorry

/-- **Equation (6)** (`eq:objective4`). The `argmin` of Eq. (6) exists exactly when `C_v` is nonempty,
that is, when `v` has a neighbour. -/
theorem equation6 (Ps : Fin k → Clustering V) (C : Clustering V) (v : V) :
    (∃ c', IsBestMove G Ps C v c') ↔ ∃ u, G.Adj v u := by
  sorry

/-- **The stopping condition** (`claim:stopping`). No vertex can be moved exactly when no candidate
cluster of any vertex has `ΔD < 0`. -/
theorem not_canMove_iff (Ps : Fin k → Clustering V) (C : Clustering V) :
    ¬CanMove G Ps C ↔ ∀ v, ∀ c' ∈ candidateClusters G C v, 0 ≤ deltaD Ps v (C.part v) c' := by
  sorry

end MedianConsensus
