module

public import MedianConsensus.Defs
public import Mathlib.InformationTheory.Hamming

/-!
# The co-clustering distance

Section "The consensus clustering problem" of the paper: Eqs. (2) and (3), and the description of
`δ_uv` as a Hamming distance in the caption of Fig. 1.
-/

@[expose] public section

open Finset

namespace MedianConsensus

variable {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ}

theorem coClustered_iff_part_eq (P : Clustering V) (u v : V) :
    CoClustered P u v ↔ P.part u = P.part v := by
  sorry

theorem mem_part_iff_coClustered (P : Clustering V) (u v : V) :
    u ∈ P.part v ↔ CoClustered P u v := by
  sorry

theorem CoClustered.symm {P : Clustering V} {u v : V} (h : CoClustered P u v) :
    CoClustered P v u := by
  sorry

theorem coClustered_comm (P : Clustering V) (u v : V) : CoClustered P u v ↔ CoClustered P v u := by
  sorry

/-- The vertices `u` and `v` are co-clustered in `ofLabels f` exactly when they have one label. -/
theorem coClustered_ofLabels {L : Type*} [DecidableEq L] (f : V → L) (u v : V) :
    CoClustered (ofLabels f) u v ↔ f u = f v := by
  sorry

/-- A clustering is determined by its co-clustered pairs. -/
theorem eq_of_coClustered_iff {P Q : Clustering V}
    (h : ∀ u v, u < v → (CoClustered P u v ↔ CoClustered Q u v)) : P = Q := by
  sorry

/-- A clustering is the clustering given by its own cluster assignment. -/
theorem ofLabels_part (P : Clustering V) : ofLabels P.part = P := by
  sorry

/-- The initial consensus `{{v₁}, …, {vₙ}}` of the algorithm is `⊥`: no two distinct vertices are
co-clustered in it. -/
theorem coClustered_bot (u v : V) : CoClustered (⊥ : Clustering V) u v ↔ u = v := by
  sorry

/-- **Equation (2)** (`eqn:rxyi`). The product `δ_uv(P) = ∏_{c ∈ P} [1 - σ_u(c) σ_v(c)]` is `0` if
`u` and `v` are co-clustered in `P`, and `1` otherwise. -/
theorem equation2 (P : Clustering V) (u v : V) :
    delta P u v = if CoClustered P u v then 0 else 1 := by
  sorry

theorem delta_comm (P : Clustering V) (u v : V) : delta P u v = delta P v u := by
  sorry

theorem deltaTotal_comm (Ps : Fin k → Clustering V) (u v : V) :
    deltaTotal Ps u v = deltaTotal Ps v u := by
  sorry

/-- A vertex is co-clustered with itself in every partition, so `δ_vv = 0`. -/
theorem deltaTotal_self (Ps : Fin k → Clustering V) (v : V) : deltaTotal Ps v v = 0 := by
  sorry

/-- **Equation (3)** (`eq:total-delta`; the paper's Eq. (3) has no TeX label). "`δ_uv` counts the
number of partitions in which `(u, v)` has not been clustered together." -/
theorem equation3 (Ps : Fin k → Clustering V) (u v : V) :
    deltaTotal Ps u v = #{i | ¬CoClustered (Ps i) u v} := by
  sorry

/-- **Caption of Fig. 1** (`claim:hamming`). "The distance between any pair of vertices is the
Hamming distance between their vectors", the cluster assignment vectors of `u` and `v`. -/
theorem deltaTotal_eq_hammingDist (Ps : Fin k → Clustering V) (u v : V) :
    deltaTotal Ps u v = hammingDist (fun i => (Ps i).part u) (fun i => (Ps i).part v) := by
  sorry

end MedianConsensus
