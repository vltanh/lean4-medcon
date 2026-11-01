module

public import MedianConsensus.Problem.Mirkin
public import External.VanDongen.SplitJoin
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Grouping homogeneous partitions

Section "Grouping homogeneous partitions" of the paper. The input partitions are the vertices of a
complete graph weighted by a distance; the edges of weight greater than `λ` are removed; the groups
are the connected components of what remains. The paper says that each component has
"inter-partition distances less than `λ`". Consecutive partitions along a path of the component have
distance at most `λ`, but two partitions of one component can be further apart.
`dist_le_of_reachable` gives the bound that holds instead.

The threshold is a natural number here, as both distances take natural values: `d ≤ λ` depends only on
`⌊λ⌋`. The paper's thresholds between `0.05` and `1` are for a normalized distance, which it does not
define. The authors' code uses `d / (2 n)`, and `d / (2 n) ≤ λ` is `d ≤ ⌊2 n λ⌋`, so the statements cover
this too.
-/

@[expose] public section

open Finset

namespace MedianConsensus

variable {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ}

/-- The graph on the input partitions left after removing the edges of weight greater than `lam`. -/
def thresholdGraph (d : Clustering V → Clustering V → ℕ) (Ps : Fin k → Clustering V) (lam : ℕ) :
    SimpleGraph (Fin k) :=
  SimpleGraph.fromRel fun i j => d (Ps i) (Ps j) ≤ lam

open Classical in
/-- **Grouping homogeneous partitions**, corrected. For a metric `d`, two
partitions of a component of `m` partitions are at distance at most `(m - 1) λ`. -/
theorem dist_le_of_reachable (d : Clustering V → Clustering V → ℕ)
    (hsymm : ∀ P Q, d P Q = d Q P) (hself : ∀ P, d P P = 0)
    (htri : ∀ P Q R, d P R ≤ d P Q + d Q R) (Ps : Fin k → Clustering V) (lam : ℕ) {i j : Fin k}
    (hij : (thresholdGraph d Ps lam).Reachable i j) :
    d (Ps i) (Ps j) ≤ (#{j' | (thresholdGraph d Ps lam).Reachable i j'} - 1) * lam := by
  set G := thresholdGraph d Ps lam with hG
  have hwalk : ∀ {x y : Fin k} (p : G.Walk x y), d (Ps x) (Ps y) ≤ p.length * lam := by
    intro x y p
    induction p with
    | nil => simp [hself]
    | @cons a b c hadj _ ih =>
      have hstep : d (Ps a) (Ps b) ≤ lam := by
        rw [hG, thresholdGraph, SimpleGraph.fromRel_adj] at hadj
        rcases hadj.2 with h | h
        · exact h
        · rwa [hsymm]
      rw [SimpleGraph.Walk.length_cons, add_mul, one_mul]
      exact (htri (Ps a) (Ps b) (Ps c)).trans (by omega)
  obtain ⟨p⟩ := hij
  obtain ⟨q, hq⟩ : ∃ q : G.Walk i j, q.IsPath := ⟨p.toPath.1, p.toPath.2⟩
  refine (hwalk q).trans (Nat.mul_le_mul_right _ ?_)
  have hsub : q.support.toFinset ⊆ ({j' | G.Reachable i j'} : Finset (Fin k)) := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact mem_filter.2 ⟨mem_univ _, (q.takeUntil x hx).reachable⟩
  have hcard := card_le_card hsub
  rw [List.toFinset_card_of_nodup hq.support_nodup, SimpleGraph.Walk.length_support] at hcard
  omega

open Classical in
/-- **Grouping homogeneous partitions** (`claim:group-distances-corrected`). `dist_le_of_reachable` for the
split-join distance that the paper uses. -/
theorem splitJoin_le_of_reachable (Ps : Fin k → Clustering V) (lam : ℕ) {i j : Fin k}
    (hij : (thresholdGraph External.VanDongen.splitJoin Ps lam).Reachable i j) :
    External.VanDongen.splitJoin (Ps i) (Ps j) ≤
      (#{j' | (thresholdGraph External.VanDongen.splitJoin Ps lam).Reachable i j'} - 1) * lam := by
  obtain ⟨hzero, hsymm, htri⟩ := External.VanDongen.splitJoin_isMetric (V := V)
  exact dist_le_of_reachable _ hsymm (fun P => (hzero P P).2 rfl) htri Ps lam hij

/-- **Grouping homogeneous partitions** (`claim:group-distances`). The paper's claim that the
components have "inter-partition distances less than `λ`" fails for the split-join distance that the
paper uses: three partitions of one component, the first and last at distance `2 > λ = 1`. -/
theorem group_distances_counterexample_splitJoin :
    ∃ Ps : Fin 3 → Clustering (Fin 3),
      (thresholdGraph External.VanDongen.splitJoin Ps 1).Reachable 0 2 ∧
        1 < External.VanDongen.splitJoin (Ps 0) (Ps 2) := by
  let Ps : Fin 3 → Clustering (Fin 3) :=
    ![ofLabels (![0, 0, 0] : Fin 3 → Fin 3), ofLabels (![0, 0, 1] : Fin 3 → Fin 3),
      ofLabels (![0, 1, 2] : Fin 3 → Fin 3)]
  have h01 : (thresholdGraph External.VanDongen.splitJoin Ps 1).Adj 0 1 := by
    rw [thresholdGraph, SimpleGraph.fromRel_adj]
    decide +kernel
  have h12 : (thresholdGraph External.VanDongen.splitJoin Ps 1).Adj 1 2 := by
    rw [thresholdGraph, SimpleGraph.fromRel_adj]
    decide +kernel
  exact ⟨Ps, h01.reachable.trans h12.reachable, by decide +kernel⟩

/-- The same claim fails for the Mirkin distance: `3 > λ = 2` on the same three partitions. -/
theorem group_distances_counterexample_mirkin :
    ∃ Ps : Fin 3 → Clustering (Fin 3),
      (thresholdGraph mirkin Ps 2).Reachable 0 2 ∧ 2 < mirkin (Ps 0) (Ps 2) := by
  let Ps : Fin 3 → Clustering (Fin 3) :=
    ![ofLabels (![0, 0, 0] : Fin 3 → Fin 3), ofLabels (![0, 0, 1] : Fin 3 → Fin 3),
      ofLabels (![0, 1, 2] : Fin 3 → Fin 3)]
  have h01 : (thresholdGraph mirkin Ps 2).Adj 0 1 := by
    rw [thresholdGraph, SimpleGraph.fromRel_adj]
    decide +kernel
  have h12 : (thresholdGraph mirkin Ps 2).Adj 1 2 := by
    rw [thresholdGraph, SimpleGraph.fromRel_adj]
    decide +kernel
  exact ⟨Ps, h01.reachable.trans h12.reachable, by decide +kernel⟩

/-- The graph on the input partitions gains edges as the threshold increases. -/
theorem thresholdGraph_mono (d : Clustering V → Clustering V → ℕ) (Ps : Fin k → Clustering V)
    {lam lam' : ℕ} (h : lam ≤ lam') : thresholdGraph d Ps lam ≤ thresholdGraph d Ps lam' := by
  intro i j hij
  rw [thresholdGraph, SimpleGraph.fromRel_adj] at hij ⊢
  exact ⟨hij.1, hij.2.imp (·.trans h) (·.trans h)⟩

/-- **Results** (`claim:groups-decrease`). "As the distance threshold increases, the number of groups
decreases", weakly: the number of connected components does not increase. -/
theorem card_components_antitone (d : Clustering V → Clustering V → ℕ) (Ps : Fin k → Clustering V)
    {lam lam' : ℕ} (h : lam ≤ lam') :
    Nat.card (thresholdGraph d Ps lam').ConnectedComponent ≤
      Nat.card (thresholdGraph d Ps lam).ConnectedComponent := by
  refine Nat.card_le_card_of_surjective
    (SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE (thresholdGraph_mono d Ps h))) ?_
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | _ v => exact ⟨(thresholdGraph d Ps lam).connectedComponentMk v, rfl⟩

/-- **Evaluation metrics** (`claim:split-join-operations`). The paper describes the split-join distance
as "the minimum number of split and join operations required to transform one partition into the
other". This is not the count of such operations: one split takes `{{0, 1, 2, 3}}` to
`{{0, 1}, {2, 3}}`, at split-join distance `2`. Van Dongen's reading counts moved elements. -/
theorem splitJoin_one_split :
    External.VanDongen.splitJoin (ofLabels (![0, 0, 0, 0] : Fin 4 → Fin 2))
      (ofLabels (![0, 0, 1, 1] : Fin 4 → Fin 2)) = 2 := by
  decide +kernel

end MedianConsensus
