module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.SymmDiff

/-!
# Cardinality of a symmetric difference

General facts about `A ∆ B` for finite sets, as used in the appendix of the paper. They could be
contributed to `Mathlib/Data/Finset/SymmDiff.lean`.
-/

@[expose] public section

open scoped symmDiff

namespace Finset

variable {α : Type*} [DecidableEq α]

/-- The identity `|A △ B| = |A| + |B| - 2 |A ∩ B|`, written without subtraction. -/
theorem card_symmDiff_add_two_mul_card_inter (A B : Finset α) :
    #(A ∆ B) + 2 * #(A ∩ B) = #A + #B := by
  have h1 : #(A ∆ B) = #(A \ B) + #(B \ A) := by
    rw [symmDiff_def, sup_eq_union, card_union_of_disjoint disjoint_sdiff_sdiff]
  have h2 := card_sdiff_add_card_inter A B
  have h3 := card_sdiff_add_card_inter B A
  rw [inter_comm] at h3
  omega

/-- The triangle inequality for the symmetric difference distance on finite sets. -/
theorem card_symmDiff_triangle (A B C : Finset α) : #(A ∆ C) ≤ #(A ∆ B) + #(B ∆ C) :=
  (card_le_card (symmDiff_triangle A B C)).trans (card_union_le _ _)

end Finset
