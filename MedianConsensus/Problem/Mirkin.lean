module

public import MedianConsensus.Problem.CoClustering
public import Basic.Data.Finset.SymmDiff
public import Basic.Algebra.BigOperators.OrderedPairs

/-!
# The Mirkin distance

The paper's appendix: Eq. (7), the description of the Mirkin distance as a symmetric difference, the
claim that it is a metric, and how the two counts in the paper ("counts (twice)" in the Methods and
`d = b + c` in the appendix) relate. The last theorem compares the definition with the classical
formula of the literature.
-/

@[expose] public section

open Finset
open scoped symmDiff

namespace MedianConsensus

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The set of pairs co-clustered in `P`. -/
def coPairs (P : Clustering V) : Finset (V × V) := {p ∈ pairs V | CoClustered P p.1 p.2}

/-- The set of pairs not co-clustered in `P`. -/
def sepPairs (P : Clustering V) : Finset (V × V) := {p ∈ pairs V | ¬CoClustered P p.1 p.2}

/-- The Mirkin distance "is equivalent to the symmetric difference between the sets of all
co-clustered pairs in `P₁` and `P₂`". -/
theorem mirkin_eq_card_symmDiff_coPairs (P Q : Clustering V) :
    mirkin P Q = #(coPairs P ∆ coPairs Q) := by
  sorry

/-- The Mirkin distance is also the symmetric difference of the sets of pairs that are not
co-clustered, which are the sets that `δ_uv(P)` indicates. -/
theorem mirkin_eq_card_symmDiff_sepPairs (P Q : Clustering V) :
    mirkin P Q = #(sepPairs P ∆ sepPairs Q) := by
  sorry

/-- **Equation (7)** (`eqx:distance`).
`d(P, Q) = b + c = ∑_{uv} (δ_uv(P) + δ_uv(Q) - 2 δ_uv(P) δ_uv(Q))`. -/
theorem equation7 (P Q : Clustering V) :
    (mirkin P Q : ℤ) =
      ∑ p ∈ pairs V, (delta P p.1 p.2 + delta Q p.1 p.2 - 2 * delta P p.1 p.2 * delta Q p.1 p.2) := by
  sorry

theorem mirkin_self (P : Clustering V) : mirkin P P = 0 := by
  sorry

theorem mirkin_comm (P Q : Clustering V) : mirkin P Q = mirkin Q P := by
  sorry

theorem mirkin_triangle (P Q R : Clustering V) : mirkin P R ≤ mirkin P Q + mirkin Q R := by
  sorry

theorem mirkin_eq_zero_iff (P Q : Clustering V) : mirkin P Q = 0 ↔ P = Q := by
  sorry

/-- **Appendix** (`claim:mirkin-metric`). "This distance is a metric". -/
theorem mirkin_isMetric :
    (∀ P Q : Clustering V, mirkin P Q = 0 ↔ P = Q) ∧
      (∀ P Q : Clustering V, mirkin P Q = mirkin Q P) ∧
        ∀ P Q R : Clustering V, mirkin P R ≤ mirkin P Q + mirkin Q R := by
  sorry

/-- **Methods** (`claim:mirkin-twice`). "The Mirkin distance … counts (twice) the number of vertex
pairs `(u, v)` that are grouped together in one partition but separated into different clusters in
the other": counting ordered pairs gives `2 (b + c)`. The appendix counts unordered pairs, and gets
`b + c`, which is `mirkin`. This statement also shows that `mirkin` does not depend on the order on
the vertices. -/
theorem card_ordered_disagreements (P Q : Clustering V) :
    #{p ∈ (univ : Finset V).offDiag | ¬(CoClustered P p.1 p.2 ↔ CoClustered Q p.1 p.2)} =
      2 * mirkin P Q := by
  sorry

/-- **The classical formula.** The Mirkin metric of the literature,
`∑_c |c|² + ∑_{c'} |c'|² - 2 ∑_c ∑_{c'} |c ∩ c'|²`, is `2 (b + c)`; written without subtraction. -/
theorem sum_sq_parts_add_sum_sq_parts (P Q : Clustering V) :
    ∑ c ∈ P.parts, #c ^ 2 + ∑ c ∈ Q.parts, #c ^ 2 =
      2 * mirkin P Q + 2 * ∑ c ∈ P.parts, ∑ c' ∈ Q.parts, #(c ∩ c') ^ 2 := by
  sorry

end MedianConsensus
