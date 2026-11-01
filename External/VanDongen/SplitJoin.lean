module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Partition.Finpartition

/-!
# The split-join distance is a metric

S. van Dongen, *Performance criteria for graph clustering and Markov cluster experiments*, CWI
report INS-R0012 (2000). The paper uses this distance to group homogeneous partitions and to
evaluate its results, and calls it a true distance metric, citing this source. See `README.md` in
this directory.

For partitions `P` and `Q` of an `n`-element set, the projection number of `P` on `Q` is
`p_P(Q) = ∑_{c ∈ P} max_{c' ∈ Q} |c ∩ c'|`, and the distance is `2 n - p_P(Q) - p_Q(P)`.
-/

@[expose] public section

open Finset

namespace External.VanDongen

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The projection number `p_P(Q) = ∑_{c ∈ P} max_{c' ∈ Q} |c ∩ c'|`. -/
def projection (P Q : Finpartition (univ : Finset V)) : ℕ :=
  ∑ c ∈ P.parts, Q.parts.sup fun c' => #(c ∩ c')

/-- The split-join distance `d(P, Q) = 2 n - p_P(Q) - p_Q(P)`. The subtraction does not truncate:
see `splitJoin_add_projection_add_projection`. -/
def splitJoin (P Q : Finpartition (univ : Finset V)) : ℕ :=
  2 * Fintype.card V - projection P Q - projection Q P

/-- The projection number of a partition of an `n`-element set is at most `n`. -/
theorem projection_le (P Q : Finpartition (univ : Finset V)) :
    projection P Q ≤ Fintype.card V := by
  calc projection P Q ≤ ∑ c ∈ P.parts, #c :=
        sum_le_sum fun c _ => Finset.sup_le fun c' _ => card_le_card inter_subset_left
    _ = Fintype.card V := by rw [P.sum_card_parts, card_univ]

/-- The subtraction in `splitJoin` does not truncate. -/
theorem splitJoin_add_projection_add_projection (P Q : Finpartition (univ : Finset V)) :
    splitJoin P Q + projection P Q + projection Q P = 2 * Fintype.card V := by
  have h1 := projection_le P Q
  have h2 := projection_le Q P
  unfold splitJoin
  omega

/-- The projection numbers satisfy `p_A(B) + p_B(C) ≤ p_A(C) + n`. -/
theorem projection_add_projection_le (A B C : Finpartition (univ : Finset V)) :
    projection A B + projection B C ≤ projection A C + Fintype.card V := by
  -- A best cluster of `B` for each cluster of `A`, and a best cluster of `C` for each of `B`.
  have hbest : ∀ (P Q : Finpartition (univ : Finset V)) (c : Finset V), c ∈ P.parts →
      ∃ c' ∈ Q.parts, Q.parts.sup (fun c' => #(c ∩ c')) = #(c ∩ c') := by
    intro P Q c hc
    obtain ⟨x, -⟩ := P.nonempty_of_mem_parts hc
    exact exists_mem_eq_sup _ ⟨Q.part x, Q.part_mem.2 (mem_univ x)⟩ _
  choose! fb hfb hfb' using hbest A B
  choose! fc hfc hfc' using hbest B C
  -- The vertices outside the chosen cluster of `C`, and those inside it.
  let T : Finset V := {x | x ∉ fc (B.part x)}
  let U : Finset V := {x | x ∈ fc (B.part x)}
  have hTU : #T + #U = Fintype.card V := by
    have := card_filter_add_card_filter_not (s := (univ : Finset V)) (fun x => x ∉ fc (B.part x))
    simpa [T, U, card_univ] using this
  have hU : projection B C ≤ #U := by
    have hdisj : (B.parts : Set (Finset V)).PairwiseDisjoint fun b => b ∩ fc b := fun b hb b' hb' hne =>
      (B.disjoint hb hb' hne).mono inter_subset_left inter_subset_left
    calc projection B C = ∑ b ∈ B.parts, #(b ∩ fc b) :=
          sum_congr rfl fun b hb => hfc' b hb
      _ = #(B.parts.biUnion fun b => b ∩ fc b) := (card_biUnion hdisj).symm
      _ ≤ #U := card_le_card fun x hx => by
          obtain ⟨b, hb, hxb⟩ := mem_biUnion.1 hx
          have hxb' := mem_inter.1 hxb
          simpa [U, B.part_eq_of_mem hb hxb'.1] using hxb'.2
  have hT : ∑ a ∈ A.parts, #((a ∩ fb a) \ fc (fb a)) ≤ #T := by
    have hdisj : (A.parts : Set (Finset V)).PairwiseDisjoint
        fun a => (a ∩ fb a) \ fc (fb a) := fun a ha a' ha' hne =>
      (A.disjoint ha ha' hne).mono (sdiff_subset.trans inter_subset_left)
        (sdiff_subset.trans inter_subset_left)
    rw [← card_biUnion hdisj]
    refine card_le_card fun x hx => ?_
    obtain ⟨a, ha, hxa⟩ := mem_biUnion.1 hx
    have hxa' := mem_sdiff.1 hxa
    have hb : B.part x = fb a := B.part_eq_of_mem (hfb a ha) (mem_inter.1 hxa'.1).2
    simpa [T, hb] using hxa'.2
  have hAB : projection A B ≤ ∑ a ∈ A.parts, #(a ∩ fc (fb a)) +
      ∑ a ∈ A.parts, #((a ∩ fb a) \ fc (fb a)) := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun a ha => ?_
    rw [hfb' a ha]
    have hcover : a ∩ fb a ⊆ (a ∩ fc (fb a)) ∪ ((a ∩ fb a) \ fc (fb a)) := by
      intro x hx
      by_cases hxc : x ∈ fc (fb a)
      · exact mem_union_left _ (mem_inter.2 ⟨(mem_inter.1 hx).1, hxc⟩)
      · exact mem_union_right _ (mem_sdiff.2 ⟨hx, hxc⟩)
    exact (card_le_card hcover).trans (card_union_le _ _)
  have hAC : ∑ a ∈ A.parts, #(a ∩ fc (fb a)) ≤ projection A C :=
    sum_le_sum fun a ha => Finset.le_sup (f := fun c' => #(a ∩ c')) (hfc _ (hfb a ha))
  omega

theorem splitJoin_comm (P Q : Finpartition (univ : Finset V)) : splitJoin P Q = splitJoin Q P := by
  unfold splitJoin
  omega

theorem splitJoin_triangle (P Q R : Finpartition (univ : Finset V)) :
    splitJoin P R ≤ splitJoin P Q + splitJoin Q R := by
  have h1 := splitJoin_add_projection_add_projection P R
  have h2 := splitJoin_add_projection_add_projection P Q
  have h3 := splitJoin_add_projection_add_projection Q R
  have h4 := projection_add_projection_le P Q R
  have h5 := projection_add_projection_le R Q P
  omega

theorem splitJoin_eq_zero_iff (P Q : Finpartition (univ : Finset V)) :
    splitJoin P Q = 0 ↔ P = Q := by
  -- If `p_P(Q) = n`, then every cluster of `P` lies in a cluster of `Q`.
  have hle : ∀ P Q : Finpartition (univ : Finset V), projection P Q = Fintype.card V → P ≤ Q := by
    intro P Q h c hc
    have hsum : ∑ c ∈ P.parts, Q.parts.sup (fun c' => #(c ∩ c')) = ∑ c ∈ P.parts, #c := by
      rw [P.sum_card_parts, card_univ]
      exact h
    have hterm := (sum_eq_sum_iff_of_le fun c _ =>
      Finset.sup_le fun c' _ => card_le_card inter_subset_left).1 hsum c hc
    obtain ⟨x, -⟩ := P.nonempty_of_mem_parts hc
    obtain ⟨c', hc', hsup⟩ := exists_mem_eq_sup Q.parts ⟨Q.part x, Q.part_mem.2 (mem_univ x)⟩
      (fun c' => #(c ∩ c'))
    refine ⟨c', hc', ?_⟩
    rw [hsup] at hterm
    exact inter_eq_left.1 (eq_of_subset_of_card_le inter_subset_left hterm.ge)
  constructor
  · intro h
    have h1 := splitJoin_add_projection_add_projection P Q
    have h2 := projection_le P Q
    have h3 := projection_le Q P
    exact le_antisymm (hle P Q (by omega)) (hle Q P (by omega))
  · rintro rfl
    have hself : projection P P = Fintype.card V := by
      refine le_antisymm (projection_le P P) ?_
      calc Fintype.card V = ∑ c ∈ P.parts, #c := by rw [P.sum_card_parts, card_univ]
        _ ≤ projection P P := sum_le_sum fun c hc => by
            simpa using Finset.le_sup (f := fun c' => #(c ∩ c')) hc
    have := splitJoin_add_projection_add_projection P P
    omega

/-- **Van Dongen (2000)** (`claim:split-join-metric`). The split-join distance is a metric on the
partitions of a finite set. -/
theorem splitJoin_isMetric :
    (∀ P Q : Finpartition (univ : Finset V), splitJoin P Q = 0 ↔ P = Q) ∧
      (∀ P Q : Finpartition (univ : Finset V), splitJoin P Q = splitJoin Q P) ∧
        ∀ P Q R : Finpartition (univ : Finset V), splitJoin P R ≤ splitJoin P Q + splitJoin Q R :=
  ⟨splitJoin_eq_zero_iff, splitJoin_comm, splitJoin_triangle⟩

end External.VanDongen
