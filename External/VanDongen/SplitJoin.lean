module

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
  sorry

/-- The subtraction in `splitJoin` does not truncate. -/
theorem splitJoin_add_projection_add_projection (P Q : Finpartition (univ : Finset V)) :
    splitJoin P Q + projection P Q + projection Q P = 2 * Fintype.card V := by
  sorry

/-- The projection numbers satisfy `p_A(B) + p_B(C) ≤ p_A(C) + n`. -/
theorem projection_add_projection_le (A B C : Finpartition (univ : Finset V)) :
    projection A B + projection B C ≤ projection A C + Fintype.card V := by
  sorry

theorem splitJoin_comm (P Q : Finpartition (univ : Finset V)) : splitJoin P Q = splitJoin Q P := by
  sorry

theorem splitJoin_triangle (P Q R : Finpartition (univ : Finset V)) :
    splitJoin P R ≤ splitJoin P Q + splitJoin Q R := by
  sorry

theorem splitJoin_eq_zero_iff (P Q : Finpartition (univ : Finset V)) :
    splitJoin P Q = 0 ↔ P = Q := by
  sorry

end External.VanDongen
