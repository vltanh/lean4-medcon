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
  sorry

/-- The triangle inequality for the symmetric difference distance on finite sets. -/
theorem card_symmDiff_triangle (A B C : Finset α) : #(A ∆ C) ≤ #(A ∆ B) + #(B ∆ C) := by
  sorry

end Finset
