module

public import MedianConsensus.Problem.Objective
public import Mathlib.Algebra.BigOperators.Field
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
  have hcount : ∀ R S : V × V → Prop, [DecidablePred R] → [DecidablePred S] →
      #{p ∈ pairs V | R p ∧ S p} + #{p ∈ pairs V | R p ∧ ¬S p} = #{p ∈ pairs V | R p} := by
    intro R S _ _
    rw [← filter_filter, ← filter_filter]
    exact card_filter_add_card_filter_not _
  have h1 := hcount (fun p => CoClustered P p.1 p.2) (fun p => CoClustered Q p.1 p.2)
  have h2 := hcount (fun p => ¬CoClustered P p.1 p.2) (fun p => CoClustered Q p.1 p.2)
  have h3 := card_filter_add_card_filter_not (s := pairs V) (fun p => CoClustered P p.1 p.2)
  have h4 : #(pairs V) = (Fintype.card V).choose 2 := card_filter_lt
  unfold contingencyA contingencyB contingencyC contingencyD
  omega

/-- The Rand index of Rand (1971): the fraction of the pairs on which the partitions agree. -/
noncomputable def randIndex (P Q : Clustering V) : ℚ :=
  ((contingencyA P Q + contingencyD P Q : ℕ) : ℚ) / ((Fintype.card V).choose 2 : ℕ)

/-- The Rand distance, `1 - R`. -/
noncomputable def randDistance (P Q : Clustering V) : ℚ := 1 - randIndex P Q

/-- **Evaluation metrics** (`claim:rand-normalized`). "Rand distance is a normalized form of mirkin
distance". This needs `n ≥ 2`, for the denominator not to vanish. -/
theorem randDistance_eq_mirkin_div (hV : 2 ≤ Fintype.card V) (P Q : Clustering V) :
    randDistance P Q = (mirkin P Q : ℚ) / ((Fintype.card V).choose 2 : ℕ) := by
  have hN : (0 : ℚ) < ((Fintype.card V).choose 2 : ℕ) := by
    exact_mod_cast Nat.choose_pos hV
  have hsum := contingency_sum P Q
  have hsum' : (contingencyA P Q : ℚ) + contingencyB P Q + contingencyC P Q + contingencyD P Q =
      ((Fintype.card V).choose 2 : ℕ) := by
    exact_mod_cast hsum
  rw [randDistance, randIndex, mirkin, eq_div_iff hN.ne', sub_mul, div_mul_cancel₀ _ hN.ne']
  push_cast
  linarith

/-- **Evaluation metrics** (`claim:rand-metric`). The Rand distance is a true distance metric, when
`n ≥ 2`. -/
theorem randDistance_isMetric (hV : 2 ≤ Fintype.card V) :
    (∀ P Q : Clustering V, randDistance P Q = 0 ↔ P = Q) ∧
      (∀ P Q : Clustering V, randDistance P Q = randDistance Q P) ∧
        ∀ P Q R : Clustering V, randDistance P R ≤ randDistance P Q + randDistance Q R := by
  have hN : (0 : ℚ) < ((Fintype.card V).choose 2 : ℕ) := by
    exact_mod_cast Nat.choose_pos hV
  refine ⟨fun P Q => ?_, fun P Q => ?_, fun P Q R => ?_⟩
  · rw [randDistance_eq_mirkin_div hV, div_eq_zero_iff, or_iff_left hN.ne', Nat.cast_eq_zero,
      mirkin_eq_zero_iff]
  · rw [randDistance_eq_mirkin_div hV, randDistance_eq_mirkin_div hV, mirkin_comm]
  · simp only [randDistance_eq_mirkin_div hV]
    rw [← add_div, div_le_div_iff_of_pos_right hN]
    exact_mod_cast mirkin_triangle P Q R

/-- "Hence they are equivalent": the median partitions for the two distances coincide. -/
theorem isMedian_iff_randDistance (hV : 2 ≤ Fintype.card V) (Ps : Fin k → Clustering V)
    (C : Clustering V) :
    IsMedian Ps C ↔ ∀ C', ∑ i, randDistance C (Ps i) ≤ ∑ i, randDistance C' (Ps i) := by
  have hN : (0 : ℚ) < ((Fintype.card V).choose 2 : ℕ) := by
    exact_mod_cast Nat.choose_pos hV
  have htotal : ∀ D : Clustering V, ∑ i, randDistance D (Ps i) =
      (totalDistance Ps D : ℚ) / ((Fintype.card V).choose 2 : ℕ) := by
    intro D
    simp only [randDistance_eq_mirkin_div hV, totalDistance, Nat.cast_sum, sum_div]
  refine forall_congr' fun C' => ?_
  rw [htotal, htotal, div_le_div_iff_of_pos_right hN, Nat.cast_le]

end MedianConsensus
