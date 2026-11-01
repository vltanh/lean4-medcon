module

public import MedianConsensus.Problem.Mirkin
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Lattice

/-!
# The objective of Eq. (4)

The derivation of Eq. (4) from Eq. (1) in the paper's appendix, and the paper's description of the
problem as "minimizing intra-cluster disagreements and maximizing inter-cluster disagreements".
-/

@[expose] public section

open Finset

namespace MedianConsensus

variable {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ}

/-- **Appendix** (`eq:appendix-identity`). The derivation of Eq. (4) from Eq. (1):
`∑_i d(C, P_i) = ∑_{uv} δ_uv + ∑_{uv} [k - 2 δ_uv] δ_uv(C)`. -/
theorem appendix_identity (Ps : Fin k → Clustering V) (C : Clustering V) :
    (totalDistance Ps C : ℤ) = ∑ p ∈ pairs V, deltaTotal Ps p.1 p.2 + objective Ps C := by
  calc (totalDistance Ps C : ℤ)
      = ∑ i, ∑ p ∈ pairs V,
          (delta C p.1 p.2 + delta (Ps i) p.1 p.2 - 2 * delta C p.1 p.2 * delta (Ps i) p.1 p.2) := by
        simp only [totalDistance, Nat.cast_sum, equation7]
    _ = ∑ p ∈ pairs V, (∑ _i : Fin k, delta C p.1 p.2 + ∑ i, delta (Ps i) p.1 p.2 -
          2 * ∑ i, delta C p.1 p.2 * delta (Ps i) p.1 p.2) := by
        rw [sum_comm]
        refine sum_congr rfl fun p _ => ?_
        simp only [sum_sub_distrib, sum_add_distrib, mul_sum, mul_assoc]
    _ = ∑ p ∈ pairs V, ((k : ℤ) * delta C p.1 p.2 + deltaTotal Ps p.1 p.2 -
          2 * delta C p.1 p.2 * deltaTotal Ps p.1 p.2) := by
        refine sum_congr rfl fun p _ => ?_
        simp only [deltaTotal, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum,
          mul_assoc]
    _ = ∑ p ∈ pairs V, deltaTotal Ps p.1 p.2 + objective Ps C := by
        rw [objective, ← sum_add_distrib]
        exact sum_congr rfl fun p _ => by ring

/-- **Equation (4)** (`eq:objective2`). `∑_{uv} δ_uv` does not depend on `C`, so the minimizers of
`∑_i d(C, P_i)` are the minimizers of `∑_{uv} [k - 2 δ_uv] δ_uv(C)`. -/
theorem equation4 (Ps : Fin k → Clustering V) (C : Clustering V) :
    IsMedian Ps C ↔ ∀ C', objective Ps C ≤ objective Ps C' := by
  refine forall_congr' fun C' => ?_
  rw [← Int.ofNat_le, appendix_identity, appendix_identity]
  exact add_le_add_iff_left _

/-- **Equation (1)** (`eq:objective1`). A median partition exists: there are finitely many
partitions. -/
theorem equation1 (Ps : Fin k → Clustering V) : ∃ C, IsMedian Ps C :=
  Finite.exists_min (totalDistance Ps)

/-- The objective can be computed over ordered pairs: it does not depend on the order on `V`. -/
theorem two_mul_objective (Ps : Fin k → Clustering V) (C : Clustering V) :
    2 * objective Ps C =
      ∑ p ∈ (univ : Finset V).offDiag, ((k : ℤ) - 2 * deltaTotal Ps p.1 p.2) * delta C p.1 p.2 := by
  rw [sum_offDiag_eq_two_mul (fun x y => ((k : ℤ) - 2 * deltaTotal Ps x y) * delta C x y)
    (fun x y => by rw [deltaTotal_comm, delta_comm]), objective, pairs, two_nsmul, two_mul]

/-- For one input partition, the input is a median partition. -/
theorem isMedian_of_one (P : Clustering V) : IsMedian ![P] P := by
  intro C'
  simp [totalDistance, mirkin_self]

/-- For two input partitions, each input is a median partition, by the triangle inequality. So the
cases `k ≤ 2` are easy, a fact that the paper's "NP-complete for `k > 2`" leaves implicit. When `P ≠ Q`,
this also shows that the `argmin` of Eq. (1) need not be unique. -/
theorem isMedian_of_two (P Q : Clustering V) : IsMedian ![P, Q] P ∧ IsMedian ![P, Q] Q := by
  constructor
  · intro C'
    simp only [totalDistance, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      mirkin_self, zero_add]
    rw [mirkin_comm C' P]
    exact mirkin_triangle P C' Q
  · intro C'
    simp only [totalDistance, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      mirkin_self, add_zero]
    rw [mirkin_comm C' P, mirkin_comm Q P]
    exact mirkin_triangle P C' Q

/-- The disagreements between the input partitions on the pairs inside the clusters of `C`. The
published paper uses the phrase without defining it; this definition, and the next, are reconstructed
from a passage that its arXiv TeX source leaves commented out. -/
def intraDisagreements (Ps : Fin k → Clustering V) (C : Clustering V) : ℤ :=
  ∑ p ∈ coPairs C, deltaTotal Ps p.1 p.2

/-- The total co-clustering distance on the pairs between the clusters of `C`. -/
def interDisagreements (Ps : Fin k → Clustering V) (C : Clustering V) : ℤ :=
  ∑ p ∈ sepPairs C, deltaTotal Ps p.1 p.2

/-- **Methods** (`claim:intra-inter`). How `∑_i d(C, P_i)` splits over the clusters of `C`: besides
`intra - inter`, there is the term `k · #(sepPairs C)`. The paper's phrase "minimizing intra-cluster
disagreements and maximizing inter-cluster disagreements" leaves this term out, whereas Eq. (4) itself
is correct and contains it. -/
theorem totalDistance_eq_intra_sub_inter (Ps : Fin k → Clustering V) (C : Clustering V) :
    (totalDistance Ps C : ℤ) =
      intraDisagreements Ps C - interDisagreements Ps C + k * #(sepPairs C) := by
  have hsplit : ∀ f : V × V → ℤ,
      ∑ p ∈ pairs V, f p = ∑ p ∈ coPairs C, f p + ∑ p ∈ sepPairs C, f p :=
    fun f => (sum_filter_add_sum_filter_not _ _ _).symm
  have hobj : objective Ps C =
      ∑ p ∈ sepPairs C, ((k : ℤ) - 2 * deltaTotal Ps p.1 p.2) := by
    rw [objective, hsplit]
    have h0 : ∑ p ∈ coPairs C, ((k : ℤ) - 2 * deltaTotal Ps p.1 p.2) * delta C p.1 p.2 = 0 := by
      refine sum_eq_zero fun p hp => ?_
      rw [equation2, ite_eq_left (mem_filter.1 hp).2, mul_zero]
    rw [h0, zero_add]
    refine sum_congr rfl fun p hp => ?_
    rw [equation2, ite_eq_right (mem_filter.1 hp).2, mul_one]
  rw [appendix_identity, hobj, hsplit, sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum,
    intraDisagreements, interDisagreements]
  ring

/-- Without that term, the verbal description has a trivial solution for all inputs: the singleton
partition minimizes the first quantity and maximizes the second. This bears only on the phrase, not on
Eq. (4). -/
theorem bot_minimizes_intra_maximizes_inter (Ps : Fin k → Clustering V) (C : Clustering V) :
    intraDisagreements Ps ⊥ ≤ intraDisagreements Ps C ∧
      interDisagreements Ps C ≤ interDisagreements Ps ⊥ := by
  have hnonneg : ∀ p : V × V, 0 ≤ deltaTotal Ps p.1 p.2 := fun p => by
    rw [equation3]; exact Int.natCast_nonneg _
  have hco : coPairs (⊥ : Clustering V) = ∅ := by
    refine filter_eq_empty_iff.2 fun p hp => ?_
    rw [coClustered_bot]
    exact (mem_filter.1 hp).2.ne
  have hsep : sepPairs (⊥ : Clustering V) = pairs V := by
    refine filter_true_of_mem fun p hp => ?_
    rw [coClustered_bot]
    exact (mem_filter.1 hp).2.ne
  constructor
  · rw [intraDisagreements, hco, sum_empty]
    exact sum_nonneg fun p _ => hnonneg p
  · rw [interDisagreements, interDisagreements, hsep]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ => hnonneg p

/-- The singleton partition is not a median partition in general. -/
theorem exists_bot_not_isMedian :
    ∃ Ps : Fin 1 → Clustering (Fin 2), ¬IsMedian Ps ⊥ := by
  let P : Clustering (Fin 2) := ofLabels fun _ => (0 : Fin 1)
  refine ⟨fun _ => P, fun h => ?_⟩
  have h0 : totalDistance (fun _ : Fin 1 => P) (⊥ : Clustering (Fin 2)) ≤ 0 := by
    have := h P
    simpa [totalDistance, mirkin_self] using this
  have h1 : mirkin (⊥ : Clustering (Fin 2)) P = 0 := by
    simpa [totalDistance] using h0
  rw [mirkin_eq_zero_iff] at h1
  have h2 : CoClustered P 0 1 := (coClustered_ofLabels _ _ _).2 rfl
  rw [← h1, coClustered_bot] at h2
  exact absurd h2 (by decide)

end MedianConsensus
