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
  have hS : ∑ p ∈ ({p | p.1 < p.2} : Finset (V × V)), F p.1 p.2 =
      ∑ p ∈ ({p | p.1 < p.2 ∧ (p.1 = v ∨ p.2 = v)} : Finset (V × V)), F p.1 p.2 := by
    symm
    apply Finset.sum_subset
    · intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp ⊢
      exact hp.1
    · intro p hp hp'
      simp only [mem_filter, mem_univ, true_and, not_and, not_or] at hp hp'
      exact h _ _ (hp' hp).1 (hp' hp).2
  rw [hS]
  refine Finset.sum_nbij' (fun p => if p.1 = v then p.2 else p.1)
    (fun u => if u < v then (u, v) else (v, u)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [mem_filter, mem_univ, true_and] at hp
    simp only [mem_erase, mem_univ, and_true]
    obtain ⟨hab, rfl | rfl⟩ := hp
    · simpa using hab.ne'
    · simpa using hab.ne
  · intro u hu
    have hu' : u ≠ v := by simpa using hu
    simp only [mem_filter, mem_univ, true_and]
    split_ifs with h'
    · exact ⟨h', Or.inr rfl⟩
    · exact ⟨lt_of_le_of_ne (not_lt.1 h') hu'.symm, Or.inl rfl⟩
  · rintro ⟨a, b⟩ hp
    simp only [mem_filter, mem_univ, true_and] at hp
    obtain ⟨hab, rfl | rfl⟩ := hp
    · simp [not_lt_of_gt hab]
    · simp [hab.ne, hab]
  · intro u hu
    have hu' : u ≠ v := by simpa using hu
    by_cases h' : u < v
    · simp [h', hu']
    · simp [h']
  · rintro ⟨a, b⟩ hp
    simp only [mem_filter, mem_univ, true_and] at hp
    obtain ⟨hab, rfl | rfl⟩ := hp
    · simp [hsymm]
    · simp [hab.ne]

/-- A symmetric function sums to twice as much over the ordered pairs of distinct elements as over
the pairs `x < y`. -/
theorem sum_offDiag_eq_two_mul {M : Type*} [AddCommMonoid M] (F : V → V → M)
    (hsymm : ∀ x y, F x y = F y x) :
    ∑ p ∈ (univ : Finset V).offDiag, F p.1 p.2 =
      2 • ∑ p ∈ ({p | p.1 < p.2} : Finset (V × V)), F p.1 p.2 := by
  have hsplit : (univ : Finset V).offDiag =
      ({p | p.1 < p.2} : Finset (V × V)) ∪ ({p | p.2 < p.1} : Finset (V × V)) := by
    ext ⟨a, b⟩
    simp only [mem_offDiag, mem_univ, true_and, mem_union, mem_filter]
    exact lt_or_lt_iff_ne.symm
  have hdisj : Disjoint ({p | p.1 < p.2} : Finset (V × V)) ({p | p.2 < p.1} : Finset (V × V)) := by
    rw [disjoint_left]
    intro p hp hp'
    simp only [mem_filter, mem_univ, true_and] at hp hp'
    exact lt_asymm hp hp'
  have hswap : ∑ p ∈ ({p | p.2 < p.1} : Finset (V × V)), F p.1 p.2 =
      ∑ p ∈ ({p | p.1 < p.2} : Finset (V × V)), F p.1 p.2 := by
    refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simpa using hp
    · intro p hp
      simpa using hp
    · simp
    · simp
    · intro p _
      exact hsymm _ _
  rw [hsplit, sum_union hdisj, hswap, two_nsmul]

/-- A symmetric relation holds on twice as many ordered pairs of distinct elements as there are
pairs `x < y` satisfying it. -/
theorem card_offDiag_filter_eq_two_mul (R : V → V → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y ↔ R y x) :
    #{p ∈ (univ : Finset V).offDiag | R p.1 p.2} = 2 * #{p : V × V | p.1 < p.2 ∧ R p.1 p.2} := by
  have h := sum_offDiag_eq_two_mul (fun x y => if R x y then 1 else 0)
    (fun x y => by simp only [hsymm x y])
  rw [← card_filter] at h
  rw [h, smul_eq_mul, ← card_filter, filter_filter]

/-- The number of pairs `x < y` is `n choose 2`. -/
theorem card_filter_lt : #({p | p.1 < p.2} : Finset (V × V)) = (Fintype.card V).choose 2 := by
  have h := sum_offDiag_eq_two_mul (V := V) (fun _ _ => (1 : ℕ)) (fun _ _ => rfl)
  simp only [sum_const, smul_eq_mul, mul_one, offDiag_card, card_univ] at h
  rw [Nat.choose_two_right, Nat.mul_sub_one, h, Nat.mul_div_cancel_left _ Nat.zero_lt_two]

end Finset

/-- The edges of a simple graph on a linear order are the pairs `x < y` that are adjacent. -/
theorem SimpleGraph.card_filter_lt_adj (G : SimpleGraph V) [DecidableRel G.Adj] :
    #{p : V × V | p.1 < p.2 ∧ G.Adj p.1 p.2} = #G.edgeFinset := by
  refine card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    simpa using hp.2
  · rintro ⟨a, b⟩ hp ⟨c, d⟩ hq h
    simp only [mem_filter, mem_univ, true_and] at hp hq
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := Sym2.eq_iff.1 h
    · rfl
    · exact absurd hp.1 (lt_asymm hq.1)
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hadj : G.Adj x y := by simpa using he
      rcases lt_or_gt_of_ne hadj.ne with h | h
      · exact ⟨(x, y), by simp [h, hadj], rfl⟩
      · exact ⟨(y, x), by simp [h, hadj.symm], Sym2.eq_swap⟩
