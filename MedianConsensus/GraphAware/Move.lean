module

public import MedianConsensus.Problem.Objective

/-!
# Moving a vertex: Eq. (5)

Section "Graph-aware consensus clustering" of the paper and the end of its appendix: the move of a
vertex between clusters, and the change `ΔD` in the objective.
-/

@[expose] public section

open Finset

namespace MedianConsensus

variable {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ}

/-- A move changes nothing between two vertices other than `v`. -/
theorem coClustered_moveVertex_of_ne (C : Clustering V) {v x y : V} (c' : Finset V) (hx : x ≠ v)
    (hy : y ≠ v) : CoClustered (moveVertex C v c') x y ↔ CoClustered C x y := by
  sorry

/-- After `v` moves to the cluster `c'`, the vertices co-clustered with `v` are those of `c'`. -/
theorem coClustered_moveVertex_self (C : Clustering V) {v u : V} {c' : Finset V}
    (hc' : c' ∈ C.parts) (hu : u ≠ v) : CoClustered (moveVertex C v c') u v ↔ u ∈ c' := by
  sorry

/-- Moving `v` to its own cluster changes nothing. -/
theorem moveVertex_part_self (C : Clustering V) (v : V) : moveVertex C v (C.part v) = C := by
  sorry

/-- A bridge for the representation of a move by labels. If `v` moves from its cluster `c` to another
cluster `c'`, the clusters of the result are those of `C` other than `c` and `c'`, then
`c' ∪ {v}`, and `c \ {v}` unless it is empty. -/
theorem parts_moveVertex (C : Clustering V) {v : V} {c' : Finset V} (hc' : c' ∈ C.parts)
    (hne : c' ≠ C.part v) :
    (moveVertex C v c').parts =
      insert (insert v c')
        (((C.parts.erase (C.part v)).erase c') ∪
          (if (C.part v).erase v = ∅ then ∅ else {(C.part v).erase v})) := by
  sorry

/-- The two right-hand sides of Eq. (5) are equal. -/
theorem deltaD_eq_second_form (Ps : Fin k → Clustering V) (v : V) (c c' : Finset V) :
    deltaD Ps v c c' =
      ∑ u ∈ univ.erase v, (sigma u c' - sigma u c) * (2 * deltaTotal Ps u v - k) := by
  sorry

/-- The first line of the derivation of `ΔD` in the appendix,
`∑_{u ∈ c} (k - 2 δ_uv) - ∑_{u ∈ c'} (k - 2 δ_uv)`, with the sums over `u ≠ v`. -/
theorem deltaD_eq_sum_sub_sum (Ps : Fin k → Clustering V) (v : V) (c c' : Finset V) :
    deltaD Ps v c c' =
      ∑ u ∈ c.erase v, ((k : ℤ) - 2 * deltaTotal Ps u v) -
        ∑ u ∈ c'.erase v, ((k : ℤ) - 2 * deltaTotal Ps u v) := by
  sorry

/-- The sum of Eq. (5) read literally, over all `u` including `u = v`, differs from `ΔD` by `k` when
`v ∈ c` and `v ∉ c'`. The sum must run over `u ≠ v`. -/
theorem sum_all_eq_deltaD_add (Ps : Fin k → Clustering V) (v : V) (c c' : Finset V) :
    ∑ u, (((k : ℤ) - 2 * deltaTotal Ps u v) * sigma u c -
        ((k : ℤ) - 2 * deltaTotal Ps u v) * sigma u c') =
      deltaD Ps v c c' + k * (sigma v c - sigma v c') := by
  sorry

theorem deltaD_self (Ps : Fin k → Clustering V) (v : V) (c : Finset V) : deltaD Ps v c c = 0 := by
  sorry

/-- **Equation (5)** (`eq:objective3`). "The change in the objective function": when `v` moves from
its cluster `c` to a cluster `c'`, the objective of Eq. (4) changes by exactly `ΔD_{v : c → c'}`,
which is given by either side of Eq. (5). -/
theorem equation5 (Ps : Fin k → Clustering V) (C : Clustering V) (v : V) {c' : Finset V}
    (hc' : c' ∈ C.parts) :
    objective Ps (moveVertex C v c') - objective Ps C = deltaD Ps v (C.part v) c' ∧
      deltaD Ps v (C.part v) c' =
        ∑ u ∈ univ.erase v, (sigma u c' - sigma u (C.part v)) * (2 * deltaTotal Ps u v - k) := by
  sorry

/-- The change in the total distance `∑_i d(C, P_i)` is also exactly `ΔD`. -/
theorem totalDistance_moveVertex (Ps : Fin k → Clustering V) (C : Clustering V) (v : V)
    {c' : Finset V} (hc' : c' ∈ C.parts) :
    (totalDistance Ps (moveVertex C v c') : ℤ) =
      totalDistance Ps C + deltaD Ps v (C.part v) c' := by
  sorry

/-- **Methods** (`claim:negative-reduces`). "When `ΔD_{v : c → c'}` is negative, moving `v` to the
new cluster `c'` reduces the overall disagreements." -/
theorem moveVertex_reduces (Ps : Fin k → Clustering V) (C : Clustering V) (v : V) {c' : Finset V}
    (hc' : c' ∈ C.parts) (h : deltaD Ps v (C.part v) c' < 0) :
    totalDistance Ps (moveVertex C v c') < totalDistance Ps C := by
  sorry

end MedianConsensus
