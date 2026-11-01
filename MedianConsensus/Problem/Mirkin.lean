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
  have hb : contingencyB P Q = #(coPairs P \ coPairs Q) := by
    unfold contingencyB coPairs
    congr 1
    ext p
    simp only [mem_filter, mem_sdiff]
    tauto
  have hc : contingencyC P Q = #(coPairs Q \ coPairs P) := by
    unfold contingencyC coPairs
    congr 1
    ext p
    simp only [mem_filter, mem_sdiff]
    tauto
  rw [mirkin, hb, hc, symmDiff_def, sup_eq_union, card_union_of_disjoint disjoint_sdiff_sdiff]

/-- The Mirkin distance is also the symmetric difference of the sets of pairs that are not
co-clustered, which are the sets that `δ_uv(P)` indicates. -/
theorem mirkin_eq_card_symmDiff_sepPairs (P Q : Clustering V) :
    mirkin P Q = #(sepPairs P ∆ sepPairs Q) := by
  rw [mirkin_eq_card_symmDiff_coPairs]
  congr 1
  ext p
  simp only [mem_symmDiff, coPairs, sepPairs, mem_filter]
  tauto

/-- **Equation (7)** (`eqx:distance`).
`d(P, Q) = b + c = ∑_{uv} (δ_uv(P) + δ_uv(Q) - 2 δ_uv(P) δ_uv(Q))`.

Departure from the paper: the appendix speaks of the sets of co-clustered pairs, but the identity for
`|A △ B|` gives Eq. (7) only for the sets that `δ` indicates, those of separated pairs. The proof applies
it to these, through `mirkin_eq_card_symmDiff_sepPairs`. This repairs a gap in the paper's step (`REPORT.md`,
E11); the argument is otherwise the paper's. -/
theorem equation7 (P Q : Clustering V) :
    (mirkin P Q : ℤ) =
      ∑ p ∈ pairs V, (delta P p.1 p.2 + delta Q p.1 p.2 - 2 * delta P p.1 p.2 * delta Q p.1 p.2) := by
  have hcard : ∀ R : Clustering V, (#(sepPairs R) : ℤ) = ∑ p ∈ pairs V, delta R p.1 p.2 := by
    intro R
    rw [sepPairs, card_filter]
    push_cast
    refine sum_congr rfl fun p _ => ?_
    rw [equation2]
    split_ifs <;> simp_all
  have hinter : (#(sepPairs P ∩ sepPairs Q) : ℤ) =
      ∑ p ∈ pairs V, delta P p.1 p.2 * delta Q p.1 p.2 := by
    have : sepPairs P ∩ sepPairs Q =
        {p ∈ pairs V | ¬CoClustered P p.1 p.2 ∧ ¬CoClustered Q p.1 p.2} := by
      ext p
      simp only [sepPairs, mem_inter, mem_filter]
      tauto
    rw [this, card_filter]
    push_cast
    refine sum_congr rfl fun p _ => ?_
    rw [equation2, equation2]
    split_ifs <;> simp_all
  have h := card_symmDiff_add_two_mul_card_inter (sepPairs P) (sepPairs Q)
  rw [← mirkin_eq_card_symmDiff_sepPairs] at h
  have h' : (mirkin P Q : ℤ) + 2 * #(sepPairs P ∩ sepPairs Q) = #(sepPairs P) + #(sepPairs Q) := by
    exact_mod_cast h
  rw [sum_sub_distrib, sum_add_distrib, ← hcard, ← hcard]
  simp only [mul_assoc]
  rw [← mul_sum, ← hinter]
  linarith

theorem mirkin_self (P : Clustering V) : mirkin P P = 0 := by
  rw [mirkin_eq_card_symmDiff_coPairs, symmDiff_self]
  rfl

theorem mirkin_comm (P Q : Clustering V) : mirkin P Q = mirkin Q P := by
  rw [mirkin_eq_card_symmDiff_coPairs, mirkin_eq_card_symmDiff_coPairs, symmDiff_comm]

theorem mirkin_triangle (P Q R : Clustering V) : mirkin P R ≤ mirkin P Q + mirkin Q R := by
  simp only [mirkin_eq_card_symmDiff_coPairs]
  exact card_symmDiff_triangle _ _ _

theorem mirkin_eq_zero_iff (P Q : Clustering V) : mirkin P Q = 0 ↔ P = Q := by
  constructor
  · intro h
    rw [mirkin_eq_card_symmDiff_coPairs, card_eq_zero] at h
    have hco : coPairs P = coPairs Q := symmDiff_eq_bot.1 h
    refine eq_of_coClustered_iff fun u v huv => ?_
    have hmem : ∀ R : Clustering V, (u, v) ∈ coPairs R ↔ CoClustered R u v := by
      intro R
      simp [coPairs, pairs, huv]
    rw [← hmem P, ← hmem Q, hco]
  · rintro rfl
    exact mirkin_self P

/-- **Appendix** (`claim:mirkin-metric`). "This distance is a metric". -/
theorem mirkin_isMetric :
    (∀ P Q : Clustering V, mirkin P Q = 0 ↔ P = Q) ∧
      (∀ P Q : Clustering V, mirkin P Q = mirkin Q P) ∧
        ∀ P Q R : Clustering V, mirkin P R ≤ mirkin P Q + mirkin Q R :=
  ⟨mirkin_eq_zero_iff, mirkin_comm, mirkin_triangle⟩

/-- **Methods** (`claim:mirkin-twice`). "The Mirkin distance … counts (twice) the number of vertex
pairs `(u, v)` that are grouped together in one partition but separated into different clusters in
the other": counting ordered pairs gives `2 (b + c)`. The appendix counts unordered pairs, and gets
`b + c`, which is `mirkin`. This statement also shows that `mirkin` does not depend on the order on
the vertices. -/
theorem card_ordered_disagreements (P Q : Clustering V) :
    #{p ∈ (univ : Finset V).offDiag | ¬(CoClustered P p.1 p.2 ↔ CoClustered Q p.1 p.2)} =
      2 * mirkin P Q := by
  rw [card_offDiag_filter_eq_two_mul (fun u v => ¬(CoClustered P u v ↔ CoClustered Q u v))
    (fun x y => by rw [coClustered_comm P, coClustered_comm Q]),
    mirkin_eq_card_symmDiff_coPairs]
  congr 2
  ext p
  simp only [mem_symmDiff, coPairs, pairs, mem_filter, mem_univ, true_and]
  tauto

/-- **The classical formula.** The Mirkin metric of the literature,
`∑_c |c|² + ∑_{c'} |c'|² - 2 ∑_c ∑_{c'} |c ∩ c'|²`, is `2 (b + c)`; written without subtraction. -/
theorem sum_sq_parts_add_sum_sq_parts (P Q : Clustering V) :
    ∑ c ∈ P.parts, #c ^ 2 + ∑ c ∈ Q.parts, #c ^ 2 =
      2 * mirkin P Q + 2 * ∑ c ∈ P.parts, ∑ c' ∈ Q.parts, #(c ∩ c') ^ 2 := by
  -- Every sum counts ordered pairs of vertices, the diagonal included.
  have hindicator : ∀ (R : Clustering V) (x y : V),
      ∑ c ∈ R.parts, (if x ∈ c ∧ y ∈ c then 1 else 0) = if CoClustered R x y then 1 else 0 := by
    intro R x y
    split_ifs with h
    · obtain ⟨c₀, hc₀, hx, hy⟩ := h
      rw [sum_eq_single c₀ (fun c hc hne => ite_eq_right fun h' => hne
        (R.eq_of_mem_parts hc hc₀ h'.1 hx)) (fun h' => absurd hc₀ h'), ite_eq_left ⟨hx, hy⟩]
    · exact sum_eq_zero fun c hc => ite_eq_right fun h' => h ⟨c, hc, h'.1, h'.2⟩
  have hsq : ∀ s : Finset V, #s ^ 2 = ∑ x, ∑ y, (if x ∈ s then 1 else 0) * (if y ∈ s then 1 else 0) := by
    intro s
    rw [← sum_mul_sum, sq, sum_boole, Nat.cast_id, filter_mem_eq_inter, univ_inter]
  have hP : ∀ R : Clustering V, ∑ c ∈ R.parts, #c ^ 2 = #{q : V × V | CoClustered R q.1 q.2} := by
    intro R
    simp only [hsq]
    rw [sum_comm]
    simp only [sum_comm (s := R.parts)]
    rw [card_filter, ← univ_product_univ, sum_product]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    rw [← hindicator]
    refine sum_congr rfl fun c _ => ?_
    by_cases hx : x ∈ c <;> by_cases hy : y ∈ c <;> simp [hx, hy]
  have hPQ : ∑ c ∈ P.parts, ∑ c' ∈ Q.parts, #(c ∩ c') ^ 2 =
      #{q : V × V | CoClustered P q.1 q.2 ∧ CoClustered Q q.1 q.2} := by
    simp only [hsq]
    rw [card_filter, ← univ_product_univ, sum_product]
    have : ∀ x y : V,
        (if CoClustered P x y ∧ CoClustered Q x y then 1 else 0) =
          ∑ c ∈ P.parts, ∑ c' ∈ Q.parts,
            (if x ∈ c ∩ c' then 1 else 0) * (if y ∈ c ∩ c' then 1 else 0) := by
      intro x y
      have h1 : ∀ c c' : Finset V, (if x ∈ c ∩ c' then 1 else 0) * (if y ∈ c ∩ c' then 1 else 0) =
          (if x ∈ c ∧ y ∈ c then 1 else 0) * (if x ∈ c' ∧ y ∈ c' then 1 else 0) := by
        intro c c'
        by_cases hx : x ∈ c <;> by_cases hy : y ∈ c <;> by_cases hx' : x ∈ c' <;>
          by_cases hy' : y ∈ c' <;> simp [hx, hy, hx', hy']
      simp only [h1]
      rw [← sum_mul_sum, hindicator, hindicator]
      split_ifs <;> simp_all
    simp only [this]
    calc _ = ∑ c ∈ P.parts, ∑ x, ∑ c' ∈ Q.parts, ∑ y,
          (if x ∈ c ∩ c' then 1 else 0) * (if y ∈ c ∩ c' then 1 else 0) :=
          sum_congr rfl fun _ _ => sum_comm
      _ = ∑ x, ∑ c ∈ P.parts, ∑ c' ∈ Q.parts, ∑ y,
          (if x ∈ c ∩ c' then 1 else 0) * (if y ∈ c ∩ c' then 1 else 0) := sum_comm
      _ = _ := sum_congr rfl fun x _ => (sum_congr rfl fun c _ => sum_comm).trans sum_comm
  have hsymm : ({q : V × V | CoClustered P q.1 q.2} : Finset (V × V)) ∆
      ({q : V × V | CoClustered Q q.1 q.2} : Finset (V × V)) =
      {q ∈ (univ : Finset V).offDiag | ¬(CoClustered P q.1 q.2 ↔ CoClustered Q q.1 q.2)} := by
    ext ⟨x, y⟩
    simp only [mem_symmDiff, mem_filter, mem_univ, true_and, mem_offDiag]
    constructor
    · intro h
      refine ⟨?_, by tauto⟩
      rintro rfl
      have := coClustered_self P x
      have := coClustered_self Q x
      tauto
    · rintro ⟨-, h⟩
      tauto
  have hcard := card_symmDiff_add_two_mul_card_inter
    ({q : V × V | CoClustered P q.1 q.2} : Finset (V × V))
    ({q : V × V | CoClustered Q q.1 q.2} : Finset (V × V))
  rw [hsymm, card_ordered_disagreements, ← filter_and] at hcard
  rw [hP, hP, hPQ, ← hcard]

end MedianConsensus
