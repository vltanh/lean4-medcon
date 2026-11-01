module

public import MedianConsensus.Problem.Mirkin
public import External.VanDongen.SplitJoin
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Grouping homogeneous partitions

Section "Grouping homogeneous partitions" of the paper. The input partitions are the vertices of a
complete graph weighted by a distance; the edges of weight greater than `λ` are removed; the groups
are the connected components of what remains. The paper says that each component has
"inter-partition distances less than `λ`". Consecutive partitions along a path do, but two partitions
of one component need not. The second theorem gives the bound that holds instead.

The threshold is a natural number here, as both distances take natural values: `d ≤ λ` depends only
on `⌊λ⌋`.
-/

@[expose] public section

open Finset

namespace MedianConsensus

variable {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ}

/-- The graph on the input partitions left after removing the edges of weight greater than `lam`. -/
def thresholdGraph (d : Clustering V → Clustering V → ℕ) (Ps : Fin k → Clustering V) (lam : ℕ) :
    SimpleGraph (Fin k) :=
  SimpleGraph.fromRel fun i j => d (Ps i) (Ps j) ≤ lam

open Classical in
/-- **Grouping homogeneous partitions** (`claim:group-distances`), corrected. For a metric `d`, two
partitions of a component of `m` partitions are at distance at most `(m - 1) λ`. -/
theorem dist_le_of_reachable (d : Clustering V → Clustering V → ℕ)
    (hsymm : ∀ P Q, d P Q = d Q P) (hself : ∀ P, d P P = 0)
    (htri : ∀ P Q R, d P R ≤ d P Q + d Q R) (Ps : Fin k → Clustering V) (lam : ℕ) {i j : Fin k}
    (hij : (thresholdGraph d Ps lam).Reachable i j) :
    d (Ps i) (Ps j) ≤ (#{j' | (thresholdGraph d Ps lam).Reachable i j'} - 1) * lam := by
  sorry

/-- **Grouping homogeneous partitions** (`claim:group-distances`). The paper's claim that the
components have "inter-partition distances less than `λ`" fails for the split-join distance that the
paper uses: three partitions of one component, the first and last at distance `2 > λ = 1`. -/
theorem group_distances_counterexample_splitJoin :
    ∃ Ps : Fin 3 → Clustering (Fin 3),
      (thresholdGraph External.VanDongen.splitJoin Ps 1).Reachable 0 2 ∧
        1 < External.VanDongen.splitJoin (Ps 0) (Ps 2) := by
  sorry

/-- The same claim fails for the Mirkin distance: `3 > λ = 2` on the same three partitions. -/
theorem group_distances_counterexample_mirkin :
    ∃ Ps : Fin 3 → Clustering (Fin 3),
      (thresholdGraph mirkin Ps 2).Reachable 0 2 ∧ 2 < mirkin (Ps 0) (Ps 2) := by
  sorry

end MedianConsensus
