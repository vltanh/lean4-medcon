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
  constructor
  · rintro ⟨c, hc, hu, hv⟩
    rw [P.part_eq_of_mem hc hu, P.part_eq_of_mem hc hv]
  · intro h
    exact ⟨P.part v, P.part_mem.2 (mem_univ v), h ▸ P.mem_part (mem_univ u), P.mem_part (mem_univ v)⟩

theorem mem_part_iff_coClustered (P : Clustering V) (u v : V) :
    u ∈ P.part v ↔ CoClustered P u v :=
  P.mem_part_iff_exists

theorem CoClustered.symm {P : Clustering V} {u v : V} (h : CoClustered P u v) :
    CoClustered P v u := by
  obtain ⟨c, hc, hu, hv⟩ := h
  exact ⟨c, hc, hv, hu⟩

theorem coClustered_comm (P : Clustering V) (u v : V) : CoClustered P u v ↔ CoClustered P v u :=
  ⟨CoClustered.symm, CoClustered.symm⟩

theorem coClustered_self (P : Clustering V) (v : V) : CoClustered P v v :=
  (coClustered_iff_part_eq P v v).2 rfl

/-- The vertices `u` and `v` are co-clustered in `ofLabels f` exactly when they have one label. -/
theorem coClustered_ofLabels {L : Type*} [DecidableEq L] (f : V → L) (u v : V) :
    CoClustered (ofLabels f) u v ↔ f u = f v := by
  let : DecidableRel (Setoid.ker f).r := fun a b => inferInstanceAs (Decidable (f a = f b))
  rw [coClustered_comm, ← mem_part_iff_coClustered]
  exact (Finpartition.mem_part_ofSetoid_iff_rel (s := Setoid.ker f)).trans Iff.rfl

/-- A clustering is determined by its co-clustered pairs. -/
theorem eq_of_coClustered_iff {P Q : Clustering V}
    (h : ∀ u v, u < v → (CoClustered P u v ↔ CoClustered Q u v)) : P = Q := by
  have hall : ∀ u v, CoClustered P u v ↔ CoClustered Q u v := by
    intro u v
    rcases lt_trichotomy u v with huv | rfl | huv
    · exact h u v huv
    · exact iff_of_true (coClustered_self P u) (coClustered_self Q u)
    · rw [coClustered_comm P, coClustered_comm Q]
      exact h v u huv
  have hpart : ∀ x, P.part x = Q.part x := by
    intro x
    ext y
    rw [mem_part_iff_coClustered, mem_part_iff_coClustered, hall]
  ext c
  constructor
  · intro hc
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hc
    rw [← P.part_eq_of_mem hc hx, hpart]
    exact Q.part_mem.2 (mem_univ x)
  · intro hc
    obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts hc
    rw [← Q.part_eq_of_mem hc hx, ← hpart]
    exact P.part_mem.2 (mem_univ x)

/-- A clustering is the clustering given by its own cluster assignment. -/
theorem ofLabels_part (P : Clustering V) : ofLabels P.part = P :=
  eq_of_coClustered_iff fun u v _ => by
    rw [coClustered_ofLabels, coClustered_iff_part_eq]

/-- The initial consensus `{{v₁}, …, {vₙ}}` of the algorithm is `⊥`: no two distinct vertices are
co-clustered in it. -/
theorem coClustered_bot (u v : V) : CoClustered (⊥ : Clustering V) u v ↔ u = v := by
  constructor
  · rintro ⟨c, hc, hu, hv⟩
    obtain ⟨a, -, rfl⟩ := Finpartition.mem_bot_iff.1 hc
    rw [mem_singleton] at hu hv
    rw [hu, hv]
  · rintro rfl
    exact coClustered_self _ _

/-- **Equation (2)** (`eqn:rxyi`). The product `δ_uv(P) = ∏_{c ∈ P} [1 - σ_u(c) σ_v(c)]` is `0` if
`u` and `v` are co-clustered in `P`, and `1` otherwise. -/
theorem equation2 (P : Clustering V) (u v : V) :
    delta P u v = if CoClustered P u v then 0 else 1 := by
  unfold delta
  split_ifs with h
  · obtain ⟨c, hc, hu, hv⟩ := h
    exact prod_eq_zero hc (by simp [sigma, hu, hv])
  · refine prod_eq_one fun c hc => ?_
    have hc' : ¬(u ∈ c ∧ v ∈ c) := fun h' => h ⟨c, hc, h'.1, h'.2⟩
    by_cases hu : u ∈ c <;> by_cases hv : v ∈ c <;> simp_all [sigma]

theorem delta_comm (P : Clustering V) (u v : V) : delta P u v = delta P v u := by
  simp only [equation2, coClustered_comm P u v]

theorem deltaTotal_comm (Ps : Fin k → Clustering V) (u v : V) :
    deltaTotal Ps u v = deltaTotal Ps v u :=
  sum_congr rfl fun _ _ => delta_comm _ u v

/-- A vertex is co-clustered with itself in every partition, so `δ_vv = 0`. -/
theorem deltaTotal_self (Ps : Fin k → Clustering V) (v : V) : deltaTotal Ps v v = 0 :=
  sum_eq_zero fun _ _ => by rw [equation2, ite_eq_left (coClustered_self _ v)]

/-- **Equation (3)** (`eq:total-delta`; the paper's Eq. (3) has no TeX label). "`δ_uv` counts the
number of partitions in which `(u, v)` has not been clustered together." -/
theorem equation3 (Ps : Fin k → Clustering V) (u v : V) :
    deltaTotal Ps u v = #{i | ¬CoClustered (Ps i) u v} := by
  rw [card_filter]
  push_cast
  refine sum_congr rfl fun i _ => ?_
  rw [equation2]
  split_ifs <;> simp_all

/-- **Caption of Fig. 1** (`claim:hamming`). "The distance between any pair of vertices is the
Hamming distance between their vectors", the cluster assignment vectors of `u` and `v`. -/
theorem deltaTotal_eq_hammingDist (Ps : Fin k → Clustering V) (u v : V) :
    deltaTotal Ps u v = hammingDist (fun i => (Ps i).part u) (fun i => (Ps i).part v) := by
  rw [equation3, hammingDist]
  simp only [coClustered_iff_part_eq]

end MedianConsensus
