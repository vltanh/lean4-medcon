module

public import MedianConsensus.Problem.Objective
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Cast.Order

/-!
# The Rand distance

Section "Evaluation metrics" of the paper: "rand distance is a normalized form of mirkin distance,
hence they are equivalent". Together with Fig. 10, whose four entries `a, b, c, d` count all pairs.
-/

@[expose] public section

open Finset

namespace MedianConsensus

variable {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ}

/-- The entry `a` of Fig. 10: the pairs in the same cluster of both partitions. -/
def contingencyA (P Q : Clustering V) : ℕ :=
  #{p ∈ pairs V | CoClustered P p.1 p.2 ∧ CoClustered Q p.1 p.2}

/-- The entry `d` of Fig. 10: the pairs in different clusters of both partitions. -/
def contingencyD (P Q : Clustering V) : ℕ :=
  #{p ∈ pairs V | ¬CoClustered P p.1 p.2 ∧ ¬CoClustered Q p.1 p.2}

/-- **Fig. 10** (`fig:disagreement-scheme`). The four entries of the contingency table count all
`n choose 2` pairs. -/
theorem contingency_sum (P Q : Clustering V) :
    contingencyA P Q + contingencyB P Q + contingencyC P Q + contingencyD P Q =
      (Fintype.card V).choose 2 := by
  sorry

/-- The Rand index of Rand (1971): the fraction of the pairs on which the partitions agree. -/
noncomputable def randIndex (P Q : Clustering V) : ℚ :=
  ((contingencyA P Q + contingencyD P Q : ℕ) : ℚ) / ((Fintype.card V).choose 2 : ℕ)

/-- The Rand distance, `1 - R`. -/
noncomputable def randDistance (P Q : Clustering V) : ℚ := 1 - randIndex P Q

/-- **Evaluation metrics** (`claim:rand-normalized`). "Rand distance is a normalized form of mirkin
distance". This needs `n ≥ 2`, for the denominator not to vanish. -/
theorem randDistance_eq_mirkin_div (hV : 2 ≤ Fintype.card V) (P Q : Clustering V) :
    randDistance P Q = (mirkin P Q : ℚ) / ((Fintype.card V).choose 2 : ℕ) := by
  sorry

/-- "Hence they are equivalent": the median partitions for the two distances coincide. -/
theorem isMedian_iff_randDistance (hV : 2 ≤ Fintype.card V) (Ps : Fin k → Clustering V)
    (C : Clustering V) :
    IsMedian Ps C ↔ ∀ C', ∑ i, randDistance C (Ps i) ≤ ∑ i, randDistance C' (Ps i) := by
  sorry

end MedianConsensus
