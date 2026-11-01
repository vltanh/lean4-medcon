module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Sums over pairs `x < y`

The pairs `(x, y)` with `x < y` of a finite linear order list the unordered pairs of distinct
elements once each. These lemmas compare sums over them with sums over ordered pairs.
-/

@[expose] public section

open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

namespace Finset

/-- A sum over the pairs `x < y` of a symmetric function that vanishes on the pairs avoiding `v` is
the sum over the pairs containing `v`. -/
theorem sum_filter_lt_eq_sum_erase {M : Type*} [AddCommMonoid M] (F : V → V → M)
    (hsymm : ∀ x y, F x y = F y x) (v : V) (h : ∀ x y, x ≠ v → y ≠ v → F x y = 0) :
    ∑ p ∈ ({p | p.1 < p.2} : Finset (V × V)), F p.1 p.2 = ∑ u ∈ univ.erase v, F u v := by
  sorry

/-- A symmetric relation holds on twice as many ordered pairs of distinct elements as there are
pairs `x < y` satisfying it. -/
theorem card_offDiag_filter_eq_two_mul (R : V → V → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y ↔ R y x) :
    #{p ∈ (univ : Finset V).offDiag | R p.1 p.2} = 2 * #{p : V × V | p.1 < p.2 ∧ R p.1 p.2} := by
  sorry

/-- A symmetric function sums to twice as much over the ordered pairs of distinct elements as over
the pairs `x < y`. -/
theorem sum_offDiag_eq_two_mul {M : Type*} [AddCommMonoid M] (F : V → V → M)
    (hsymm : ∀ x y, F x y = F y x) :
    ∑ p ∈ (univ : Finset V).offDiag, F p.1 p.2 =
      2 • ∑ p ∈ ({p | p.1 < p.2} : Finset (V × V)), F p.1 p.2 := by
  sorry

/-- The number of pairs `x < y` is `n choose 2`. -/
theorem card_filter_lt : #({p | p.1 < p.2} : Finset (V × V)) = (Fintype.card V).choose 2 := by
  sorry

end Finset

/-- The edges of a simple graph on a linear order are the pairs `x < y` that are adjacent. -/
theorem SimpleGraph.card_filter_lt_adj (G : SimpleGraph V) [DecidableRel G.Adj] :
    #{p : V × V | p.1 < p.2 ∧ G.Adj p.1 p.2} = #G.edgeFinset := by
  sorry
