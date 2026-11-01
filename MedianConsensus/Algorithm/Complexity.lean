module

public import MedianConsensus.Algorithm.Greedy
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Counting moves and computation

Section "Computation and memory complexity" of the paper. The paper's `O(·)` statements are informal.
This file makes the combinatorial content precise, for an explicit count of operations: to evaluate
one term of Eq. (5) for a cluster `c`, one computes `δ_uv` for each `u ∈ c`, at `k` comparisons each.
-/

@[expose] public section

open Finset

namespace MedianConsensus

variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Computation and memory complexity** (`claim:pairs-count`). The number of pairs of `n` objects
is `n (n - 1) / 2`, which is `k (k - 1) / 2` for the `k` input partitions. -/
theorem card_pairs : #(pairs V) = Fintype.card V * (Fintype.card V - 1) / 2 := by
  rw [pairs, card_filter_lt, Nat.choose_two_right]

/-- **Parallel algorithm** (`claim:moves-list`). "We first identify the inter-cluster edges, as these
edges provide a list of all potential moves." The potential moves are exactly what the two orientations
of the inter-cluster edges give. -/
theorem potentialMoves_eq_image (C : Clustering V) :
    potentialMoves G C = (interEdges G C ×ˢ (univ : Finset Bool)).image
      fun q => if q.2 then (q.1.1, C.part q.1.2) else (q.1.2, C.part q.1.1) := by
  ext ⟨v, c'⟩
  constructor
  · intro hm
    obtain ⟨-, hc', hne⟩ := mem_filter.1 hm
    obtain ⟨u, hadj, rfl⟩ := (mem_candidateClusters_iff G C v c').1 hc'
    have hsep : ¬CoClustered C v u := fun h => hne ((coClustered_iff_part_eq C v u).1 h).symm
    rw [mem_image]
    rcases lt_or_gt_of_ne hadj.ne with h | h
    · refine ⟨((v, u), true), ?_, rfl⟩
      simp [interEdges, pairs, h, hadj, hsep]
    · refine ⟨((u, v), false), ?_, rfl⟩
      have hsep' : ¬CoClustered C u v := fun h' => hsep h'.symm
      simp [interEdges, pairs, h, hadj.symm, hsep']
  · intro hm
    obtain ⟨⟨⟨x, y⟩, b⟩, hq, heq⟩ := mem_image.1 hm
    obtain ⟨hedge, -⟩ := mem_product.1 hq
    simp only [interEdges, mem_filter] at hedge
    obtain ⟨-, hadj, hsep⟩ := hedge
    have hmove : ∀ a a' : V, G.Adj a a' → ¬CoClustered C a a' →
        (a, C.part a') ∈ potentialMoves G C := by
      intro a a' hadj' hsep'
      refine mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, C.part_mem.2 (mem_univ _)⟩,
        (mem_candidateClusters_iff G C a _).2 ⟨a', hadj', rfl⟩, fun h => hsep' ?_⟩
      exact (coClustered_iff_part_eq C a a').2 h.symm
    cases b
    · simp only [Bool.false_eq_true, ite_false, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact hmove _ _ hadj.symm fun h => hsep h.symm
    · simp only [ite_true, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact hmove _ _ hadj hsep

/-- **Computation and memory complexity** (`claim:moves-at-most`). "If there are `m̂` inter-cluster
edges, the number of potential moves is at most `2 m̂`." -/
theorem card_potentialMoves_le (C : Clustering V) :
    #(potentialMoves G C) ≤ 2 * #(interEdges G C) := by
  rw [potentialMoves_eq_image]
  refine card_image_le.trans_eq ?_
  simp [card_product, mul_comm]

/-- The number `m̂` of inter-cluster edges is at most the number `m` of edges. -/
theorem card_interEdges_le (C : Clustering V) : #(interEdges G C) ≤ #G.edgeFinset := by
  rw [← SimpleGraph.card_filter_lt_adj]
  refine card_le_card fun p hp => ?_
  simp only [interEdges, pairs, mem_filter, mem_univ, true_and] at hp ⊢
  exact ⟨hp.1, hp.2.1⟩

/-- **Graph-aware consensus clustering** (`claim:moves-at-most-m`). "At most `O(m)` moves are
considered", in each iteration: at most `2 m`. -/
theorem card_potentialMoves_le_two_mul_edges (C : Clustering V) :
    #(potentialMoves G C) ≤ 2 * #G.edgeFinset :=
  (card_potentialMoves_le G C).trans (Nat.mul_le_mul_left 2 (card_interEdges_le G C))

/-- A vertex has at most `b - 1` potential moves, one per other cluster, so an iteration has at most
`n (b - 1)` potential moves, a bound independent of `m̂`. -/
theorem card_potentialMoves_le_mul (C : Clustering V) :
    #(potentialMoves G C) ≤ Fintype.card V * (#C.parts - 1) := by
  have hfibre : ∀ v ∈ (univ : Finset V),
      #{m ∈ potentialMoves G C | m.1 = v} ≤ #C.parts - 1 := by
    intro v _
    have hcard : #(C.parts.erase (C.part v)) = #C.parts - 1 :=
      card_erase_of_mem (C.part_mem.2 (mem_univ v))
    rw [← hcard]
    refine card_le_card_of_injOn Prod.snd ?_ ?_
    · rintro ⟨w, c'⟩ hm
      simp only [potentialMoves, mem_coe, mem_filter, mem_product, mem_univ, true_and] at hm
      obtain ⟨⟨hc, -, hne⟩, rfl⟩ := hm
      exact mem_coe.2 (mem_erase.2 ⟨hne, hc⟩)
    · rintro ⟨w, c'⟩ hm ⟨w', c''⟩ hm' heq
      simp only [mem_coe, mem_filter] at hm hm'
      exact Prod.ext (hm.2.trans hm'.2.symm) heq
  calc #(potentialMoves G C) ≤ (#C.parts - 1) * #(univ : Finset V) :=
        card_le_mul_card_image_of_maps_to (fun _ _ => mem_univ _) _ hfibre
    _ = Fintype.card V * (#C.parts - 1) := by rw [card_univ, mul_comm]

/-- The operations needed to evaluate the two terms of Eq. (5) for a move `m = (v, c')`, with `k`
comparisons per vertex of `c` and of `c'`. -/
def moveCost (C : Clustering V) (k : ℕ) (m : V × Finset V) : ℕ :=
  (#(C.part m.1) + #m.2) * k

/-- The operations of one iteration: the two terms of Eq. (5) for every potential move. -/
def iterationCost (C : Clustering V) (k : ℕ) : ℕ :=
  ∑ m ∈ potentialMoves G C, moveCost C k m

/-- "On average, each cluster then contains `n / b` vertices": the `b` clusters cover the `n`
vertices. -/
theorem sum_card_parts_eq (C : Clustering V) : ∑ c ∈ C.parts, #c = Fintype.card V := by
  rw [C.sum_card_parts, card_univ]

/-- Clusters of equal size `s`: `s = n / b`. -/
theorem card_parts_mul_of_equal_size {C : Clustering V} {s : ℕ} (hs : ∀ c ∈ C.parts, #c = s) :
    #C.parts * s = Fintype.card V := by
  rw [← card_univ, ← C.sum_card_parts]
  exact (sum_const_nat hs).symm

/-- For clusters of size `s`, each potential move costs `2 s k`. -/
theorem iterationCost_eq {C : Clustering V} {s : ℕ} (hs : ∀ c ∈ C.parts, #c = s) (k : ℕ) :
    iterationCost G C k = #(potentialMoves G C) * (2 * s * k) := by
  refine sum_const_nat fun m hm => ?_
  obtain ⟨hprod, -⟩ := mem_filter.1 hm
  rw [moveCost, hs _ (C.part_mem.2 (mem_univ _)), hs _ (mem_product.1 hprod).2]
  ring

/-- **Computation and memory complexity** (`claim:iteration-cost`). The bound `O(m̂ n k_h / b)`, with
its constant, for clusters of equal size: the cost of an iteration satisfies
`cost · b ≤ 4 m̂ n k_h`. -/
theorem iterationCost_mul_parts_le {C : Clustering V} {s : ℕ} (hs : ∀ c ∈ C.parts, #c = s) (k : ℕ) :
    iterationCost G C k * #C.parts ≤ 4 * #(interEdges G C) * Fintype.card V * k := by
  have hb := card_parts_mul_of_equal_size hs
  have hcost := iterationCost_eq G hs k
  have hmoves := card_potentialMoves_le G C
  rw [hcost, ← hb]
  calc #(potentialMoves G C) * (2 * s * k) * #C.parts
      ≤ (2 * #(interEdges G C)) * (2 * s * k) * #C.parts := by gcongr
    _ = 4 * #(interEdges G C) * (#C.parts * s) * k := by ring

/-- For clusters of equal size, the cost of an iteration is at most `2 n² k_h`, whatever `m̂` and `b`
are. -/
theorem iterationCost_le_quadratic {C : Clustering V} {s : ℕ} (hs : ∀ c ∈ C.parts, #c = s) (k : ℕ) :
    iterationCost G C k ≤ 2 * Fintype.card V ^ 2 * k := by
  have hb := card_parts_mul_of_equal_size hs
  have hcost := iterationCost_eq G hs k
  have hmoves := card_potentialMoves_le_mul G C
  have hsub : (#C.parts - 1) * s ≤ Fintype.card V := by
    rw [← hb]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  rw [hcost]
  calc #(potentialMoves G C) * (2 * s * k)
      ≤ Fintype.card V * (#C.parts - 1) * (2 * s * k) := by gcongr
    _ = 2 * (Fintype.card V * ((#C.parts - 1) * s)) * k := by ring
    _ ≤ 2 * (Fintype.card V * Fintype.card V) * k := by gcongr
    _ = 2 * Fintype.card V ^ 2 * k := by ring

/-- **Computation and memory complexity** (`claim:large-clusters`). "Large clusters having many
inter-cluster edges may enhance the computational cost": the quadratic bound fails without equal sizes.
On the complete graph on `10` vertices, with one cluster of `7` and three singletons, and `k_h = 1`, the
cost is `204`, against `2 n² k_h = 200`. -/
theorem iterationCost_large_cluster :
    2 * 10 ^ 2 * 1 <
      iterationCost (⊤ : SimpleGraph (Fin 10))
        (ofLabels (![0, 0, 0, 0, 0, 0, 0, 1, 2, 3] : Fin 10 → Fin 4)) 1 := by
  decide +kernel

section Halves

variable (s : ℕ)

/-- The half of `Fin (2 * s)` that a vertex lies in. -/
def halfSide (x : Fin (2 * s)) : Bool := decide (x.val < s)

/-- The clustering of `Fin (2 * s)` into its two halves. -/
def halves : Clustering (Fin (2 * s)) := ofLabels (halfSide s)

theorem coClustered_halves (x y : Fin (2 * s)) :
    CoClustered (halves s) x y ↔ halfSide s x = halfSide s y :=
  coClustered_ofLabels _ x y

/-- One of the two halves. -/
def halfSet (b : Bool) : Finset (Fin (2 * s)) := {y | halfSide s y = b}

variable {s}

theorem part_halves (x : Fin (2 * s)) : (halves s).part x = halfSet s (halfSide s x) := by
  ext y
  rw [mem_part_iff_coClustered, coClustered_halves]
  simp [halfSet]

variable (hs : 0 < s)
include hs

theorem parts_halves : (halves s).parts = {halfSet s true, halfSet s false} := by
  ext d
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hd
    obtain ⟨x, -, rfl⟩ := (halves s).part_surjOn hd
    rw [part_halves]
    cases halfSide s x
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    · have h : halfSide s ⟨0, by omega⟩ = true := by simp [halfSide, hs]
      rw [← h, ← part_halves]
      exact (halves s).part_mem.2 (mem_univ _)
    · have h : halfSide s ⟨s, by omega⟩ = false := by simp [halfSide]
      rw [← h, ← part_halves]
      exact (halves s).part_mem.2 (mem_univ _)

omit hs in
theorem card_halfSet_true : #(halfSet s true) = s := by
  obtain rfl | hs := Nat.eq_zero_or_pos s
  · simp [halfSet, halfSide]
  have : halfSet s true = Finset.Iio ⟨s, by omega⟩ := by
    ext y
    simp [halfSet, halfSide, Fin.lt_def]
  rw [this, Fin.card_Iio]

omit hs in
theorem card_halfSet_false : #(halfSet s false) = s := by
  obtain rfl | hs := Nat.eq_zero_or_pos s
  · simp [halfSet, halfSide]
  have : halfSet s false = Finset.Ici ⟨s, by omega⟩ := by
    ext y
    simp [halfSet, halfSide, Fin.le_def]
  rw [this, Fin.card_Ici]
  change 2 * s - s = s
  omega

theorem card_parts_halves : #(halves s).parts = 2 := by
  rw [parts_halves hs, card_pair]
  intro h
  have h0 : (⟨0, by omega⟩ : Fin (2 * s)) ∈ halfSet s true := by
    simp [halfSet, halfSide, hs]
  rw [h] at h0
  simp [halfSet, halfSide] at h0
  omega

theorem card_of_mem_parts_halves {c : Finset (Fin (2 * s))} (hc : c ∈ (halves s).parts) :
    #c = s := by
  rw [parts_halves hs, mem_insert, mem_singleton] at hc
  rcases hc with rfl | rfl
  · exact card_halfSet_true
  · exact card_halfSet_false

omit hs in
theorem card_interEdges_halves : #(interEdges ⊤ (halves s)) = s ^ 2 := by
  have hedges : interEdges ⊤ (halves s) = halfSet s true ×ˢ halfSet s false := by
    ext ⟨x, y⟩
    simp only [interEdges, pairs, halfSet, mem_filter, mem_univ, true_and, mem_product,
      coClustered_halves, SimpleGraph.top_adj]
    constructor
    · rintro ⟨hxy, -, hne'⟩
      have hxy' : x.val < y.val := hxy
      by_cases hxs : x.val < s
      · have hx : halfSide s x = true := by simp [halfSide, hxs]
        refine ⟨hx, ?_⟩
        cases hy : halfSide s y
        · rfl
        · exact absurd (hx.trans hy.symm) hne'
      · have hys : ¬y.val < s := by omega
        have hx : halfSide s x = false := by simp [halfSide, hxs]
        have hy : halfSide s y = false := by simp [halfSide, hys]
        exact absurd (hx.trans hy.symm) hne'
    · rintro ⟨hx, hy⟩
      have hxs : x.val < s := by simpa [halfSide] using hx
      have hys : ¬y.val < s := by simpa [halfSide] using hy
      have hxy : x < y := Fin.lt_def.2 (by omega)
      refine ⟨hxy, hxy.ne, ?_⟩
      rw [hx, hy]
      simp
  rw [hedges, card_product, card_halfSet_true, card_halfSet_false, sq]

omit hs in
/-- With the two halves as the one input, the weight `k - 2 δ_uv` is `1` inside a half, and `-1`
between the two. -/
theorem weight_halves (u v : Fin (2 * s)) :
    ((1 : ℕ) : ℤ) - 2 * deltaTotal (fun _ : Fin 1 => halves s) u v = if halfSide s u = halfSide s v then 1 else -1 := by
  have h : deltaTotal (fun _ : Fin 1 => halves s) u v = if halfSide s u = halfSide s v then 0 else 1 := by
    simp [deltaTotal, equation2, coClustered_halves]
  rw [h]
  split_ifs <;> norm_num

omit hs in
/-- A greedy move keeps the clusters inside the halves: a move into the other half has `ΔD ≥ 0`. -/
theorem pure_of_greedyStep {D D' : Clustering (Fin (2 * s))}
    (hD : ∀ x y, CoClustered D x y → halfSide s x = halfSide s y)
    (hstep : GreedyStep ⊤ (fun _ : Fin 1 => halves s) D D') (x y : Fin (2 * s)) (h : CoClustered D' x y) :
    halfSide s x = halfSide s y := by
  obtain ⟨v, c', hbest, hneg, rfl⟩ := hstep
  have hc' : c' ∈ D.parts := mem_parts_of_mem_candidateClusters _ hbest.1
  have htarget : ∀ y ∈ c', halfSide s y = halfSide s v := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y₀, hy₀, hy₀v⟩ := hcon
    have hforeign : ∀ u ∈ c', halfSide s u ≠ halfSide s v := by
      intro u hu
      rwa [hD u y₀ ⟨c', hc', hu, hy₀⟩]
    have hfirst : 0 ≤ ∑ u ∈ (D.part v).erase v, (((1 : ℕ) : ℤ) - 2 * deltaTotal (fun _ : Fin 1 => halves s) u v) := by
      refine sum_nonneg fun u hu => ?_
      have hu' : CoClustered D u v := (mem_part_iff_coClustered D u v).1 (mem_of_mem_erase hu)
      rw [weight_halves, ite_eq_left (hD u v hu')]
      norm_num
    have hsecond : ∑ u ∈ c'.erase v, (((1 : ℕ) : ℤ) - 2 * deltaTotal (fun _ : Fin 1 => halves s) u v) ≤ 0 := by
      refine sum_nonpos fun u hu => ?_
      rw [weight_halves, ite_eq_right (hforeign u (mem_of_mem_erase hu))]
      norm_num
    rw [deltaD_eq_sum_sub_sum] at hneg
    omega
  by_cases hx : x = v
  · subst hx
    by_cases hy : y = x
    · rw [hy]
    · exact (htarget y ((coClustered_moveVertex_self D hc' hy).1 h.symm)).symm
  · by_cases hy : y = v
    · subst hy
      exact htarget x ((coClustered_moveVertex_self D hc' hx).1 h)
    · exact hD x y ((coClustered_moveVertex_of_ne D c' hx hy).1 h)

omit hs in
/-- If the clusters lie inside the halves and no vertex can move, the clusters are the two halves: of
two clusters inside a half, a vertex of the smaller one has `ΔD < 0` for the larger one. -/
theorem eq_halves_of_stable {D : Clustering (Fin (2 * s))}
    (hD : ∀ x y, CoClustered D x y → halfSide s x = halfSide s y)
    (hstable : ¬CanMove ⊤ (fun _ : Fin 1 => halves s) D) : D = halves s := by
  have hstable' := (not_canMove_iff _ _ _).1 hstable
  have hsmall : ∀ x y, x ≠ y → halfSide s x = halfSide s y → #(D.part x) ≤ #(D.part y) →
      CoClustered D x y := by
    intro x y hxy hside hle
    by_contra hsep
    have hcand : D.part y ∈ candidateClusters ⊤ D x :=
      (mem_candidateClusters_iff _ D x _).2 ⟨y, hxy, rfl⟩
    have h0 := hstable' x _ hcand
    rw [deltaD_eq_sum_sub_sum] at h0
    have hxy' : x ∉ D.part y := fun h => hsep ((mem_part_iff_coClustered D x y).1 h)
    have hfirst : ∑ u ∈ (D.part x).erase x, (((1 : ℕ) : ℤ) - 2 * deltaTotal (fun _ : Fin 1 => halves s) u x) =
        #((D.part x).erase x) := by
      rw [sum_congr rfl (g := fun _ => (1 : ℤ)) fun u hu => by
        have hu' : CoClustered D u x := (mem_part_iff_coClustered D u x).1 (mem_of_mem_erase hu)
        rw [weight_halves, ite_eq_left (hD u x hu')]]
      simp
    have hsecond : ∑ u ∈ (D.part y).erase x, (((1 : ℕ) : ℤ) - 2 * deltaTotal (fun _ : Fin 1 => halves s) u x) =
        #(D.part y) := by
      rw [erase_eq_of_notMem hxy', sum_congr rfl (g := fun _ => (1 : ℤ)) fun u hu => by
        have hu' : CoClustered D u y := (mem_part_iff_coClustered D u y).1 hu
        rw [weight_halves, ite_eq_left ((hD u y hu').trans hside.symm)]]
      simp
    rw [hfirst, hsecond] at h0
    have hmem : x ∈ D.part x := D.mem_part (mem_univ x)
    rw [card_erase_of_mem hmem] at h0
    have hpos : 0 < #(D.part x) := card_pos.2 ⟨x, hmem⟩
    omega
  refine eq_of_coClustered_iff fun x y hxy => ?_
  rw [coClustered_halves]
  refine ⟨hD x y, fun hside => ?_⟩
  rcases le_total #(D.part x) #(D.part y) with hle | hle
  · exact hsmall x y hxy.ne hside hle
  · exact (hsmall y x hxy.ne' hside.symm hle).symm

omit hs in
/-- From the singletons, with the two halves as the one input, a run reaches the two halves. -/
theorem reachable_halves :
    Relation.ReflTransGen (GreedyStep ⊤ (fun _ : Fin 1 => halves s)) ⊥ (halves s) := by
  have hpure : ∀ D, Relation.ReflTransGen (GreedyStep ⊤ (fun _ : Fin 1 => halves s)) ⊥ D →
      ∀ x y, CoClustered D x y → halfSide s x = halfSide s y := by
    intro D hrun
    induction hrun with
    | refl =>
      intro x y h
      rw [(coClustered_bot x y).1 h]
    | tail _ hstep ih => exact pure_of_greedyStep ih hstep
  obtain ⟨D, hrun, hstable⟩ := exists_stable (G := ⊤) (fun _ : Fin 1 => halves s) ⊥
  rwa [eq_halves_of_stable (hpure D hrun) hstable] at hrun

end Halves

/-- **Computation and memory complexity** (`claim:both-conditions`). The paper says that `m̂` very high
and `b` very low "cannot occur simultaneously" for same-size clusters, since "we start from singleton
clusters". They can, in a state that the algorithm reaches. On the complete graph on `n = 2 s` vertices,
with the two halves as the one input, a run from the singletons reaches the two halves, where `b = 2`
and `m̂ = s² = n² / 4`. Then the paper's `O(m̂ n k_h / b)` is `n³ k_h / 8`, an overestimate: the bound
`iterationCost_le_quadratic` holds there, since an iteration has only `n (b - 1)` potential moves. So
the paper's conclusion that the cost stays at most quadratic for same-size clusters holds, for another
reason. -/
theorem both_conditions_occur (s : ℕ) (hs : 0 < s) :
    ∃ C : Clustering (Fin (2 * s)),
      #C.parts = 2 ∧ (∀ c ∈ C.parts, #c = s) ∧ #(interEdges ⊤ C) = s ^ 2 ∧
        Relation.ReflTransGen (GreedyStep ⊤ (fun _ : Fin 1 => C)) ⊥ C :=
  ⟨halves s, card_parts_halves hs, fun _ hc => card_of_mem_parts_halves hs hc,
    card_interEdges_halves, reachable_halves⟩

end MedianConsensus
