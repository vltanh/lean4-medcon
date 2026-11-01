module

public import MedianConsensus.Problem.Mirkin

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
  sorry

/-- **Equation (4)** (`eq:objective2`). `∑_{uv} δ_uv` does not depend on `C`, so the minimizers of
`∑_i d(C, P_i)` are the minimizers of `∑_{uv} [k - 2 δ_uv] δ_uv(C)`. -/
theorem equation4 (Ps : Fin k → Clustering V) (C : Clustering V) :
    IsMedian Ps C ↔ ∀ C', objective Ps C ≤ objective Ps C' := by
  sorry

/-- **Equation (1)** (`eq:objective1`). A median partition exists: there are finitely many
partitions. -/
theorem equation1 (Ps : Fin k → Clustering V) : ∃ C, IsMedian Ps C := by
  sorry

/-- The objective can be computed over ordered pairs: it does not depend on the order on `V`. -/
theorem two_mul_objective (Ps : Fin k → Clustering V) (C : Clustering V) :
    2 * objective Ps C =
      ∑ p ∈ (univ : Finset V).offDiag, ((k : ℤ) - 2 * deltaTotal Ps p.1 p.2) * delta C p.1 p.2 := by
  sorry

/-- For one input partition, the input is a median partition. -/
theorem isMedian_of_one (P : Clustering V) : IsMedian ![P] P := by
  sorry

/-- For two input partitions, each input is a median partition. This is why the problem is hard only
for `k > 2`, in the paper's words. It also shows that the `argmin` of Eq. (1) need not be unique. -/
theorem isMedian_of_two (P Q : Clustering V) : IsMedian ![P, Q] P := by
  sorry

/-- The disagreements between the input partitions on the pairs inside the clusters of `C`. -/
def intraDisagreements (Ps : Fin k → Clustering V) (C : Clustering V) : ℤ :=
  ∑ p ∈ coPairs C, deltaTotal Ps p.1 p.2

/-- The total co-clustering distance on the pairs between the clusters of `C`. -/
def interDisagreements (Ps : Fin k → Clustering V) (C : Clustering V) : ℤ :=
  ∑ p ∈ sepPairs C, deltaTotal Ps p.1 p.2

/-- **Methods** (`claim:intra-inter`). How `∑_i d(C, P_i)` splits over the clusters of `C`: besides
`intra - inter`, there is the term `k · #(sepPairs C)`. The paper's phrase "minimizing intra-cluster
disagreements and maximizing inter-cluster disagreements" leaves this term out. -/
theorem totalDistance_eq_intra_sub_inter (Ps : Fin k → Clustering V) (C : Clustering V) :
    (totalDistance Ps C : ℤ) =
      intraDisagreements Ps C - interDisagreements Ps C + k * #(sepPairs C) := by
  sorry

/-- Without that term, the phrase has a trivial solution for all inputs: the singleton partition
minimizes the first quantity and maximizes the second. -/
theorem bot_minimizes_intra_maximizes_inter (Ps : Fin k → Clustering V) (C : Clustering V) :
    intraDisagreements Ps ⊥ ≤ intraDisagreements Ps C ∧
      interDisagreements Ps C ≤ interDisagreements Ps ⊥ := by
  sorry

/-- The singleton partition is not a median partition in general. -/
theorem exists_bot_not_isMedian :
    ∃ Ps : Fin 1 → Clustering (Fin 2), ¬IsMedian Ps ⊥ := by
  sorry

end MedianConsensus
