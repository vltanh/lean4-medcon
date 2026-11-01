module

public import MedianConsensus.Algorithm.Greedy
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.FinCases

/-!
# Small examples of the greedy algorithm

Certified instances of the paper's remarks on the greedy policy, with small explicit inputs found by
exhaustive search.
-/

@[expose] public section

open Finset

namespace MedianConsensus

/-- **Methods** (`claim:greedy-not-optimal`). "This greedy moving policy, like any greedy algorithm,
does not guarantee an optimal solution." The instance has four vertices and three input partitions,
on the complete graph, so the graph is not the cause. The algorithm, started from the singletons,
stops, and *every* partition at which a run stops fails to be a median partition. So the order of
the moves is not the cause either, although the paper's "Consequently" derives this claim from it.
The runs stop at `{{0, 1}, {2, 3}}`, at total distance `8`, and the median `{{0, 1, 2, 3}}` has total
distance `4`. -/
theorem greedy_not_optimal :
    ∃ Ps : Fin 3 → Clustering (Fin 4),
      (∃ C, Relation.ReflTransGen (GreedyStep ⊤ Ps) ⊥ C ∧ ¬CanMove ⊤ Ps C) ∧
        ∀ C, Relation.ReflTransGen (GreedyStep ⊤ Ps) ⊥ C → ¬CanMove ⊤ Ps C → ¬IsMedian Ps C := by
  let Ps : Fin 3 → Clustering (Fin 4) :=
    ![ofLabels (![0, 0, 0, 0] : Fin 4 → Fin 2), ofLabels (![0, 0, 0, 0] : Fin 4 → Fin 2),
      ofLabels (![0, 0, 1, 1] : Fin 4 → Fin 2)]
  let stop : Clustering (Fin 4) := ofLabels (![0, 0, 1, 1] : Fin 4 → Fin 2)
  let C₁ : Clustering (Fin 4) := ofLabels (![0, 0, 1, 2] : Fin 4 → Fin 3)
  let C₂ : Clustering (Fin 4) := ofLabels (![0, 1, 2, 2] : Fin 4 → Fin 3)
  let R : List (Clustering (Fin 4)) := [⊥, C₁, C₂, stop]
  -- The condition of a greedy move, on the complete graph, with the target given by a vertex.
  let good : Clustering (Fin 4) → Prop := fun C => ∀ v u : Fin 4, u ≠ v →
    (∀ w, w ≠ v → deltaD Ps v (C.part v) (C.part u) ≤ deltaD Ps v (C.part v) (C.part w)) →
      deltaD Ps v (C.part v) (C.part u) < 0 → moveVertex C v (C.part u) ∈ R
  have hgood : ∀ C ∈ R, good C := by
    intro C hC
    simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl
    · change ∀ v u : Fin 4, _
      decide +kernel
    · change ∀ v u : Fin 4, _
      decide +kernel
    · change ∀ v u : Fin 4, _
      decide +kernel
    · change ∀ v u : Fin 4, _
      decide +kernel
  have hreach : ∀ C, Relation.ReflTransGen (GreedyStep ⊤ Ps) ⊥ C → C ∈ R := by
    intro C h
    induction h with
    | refl => exact List.mem_cons_self
    | tail _ h ih =>
      obtain ⟨v, c', hbest, hneg, rfl⟩ := h
      obtain ⟨u, hu, rfl⟩ := (mem_candidateClusters_iff _ _ v c').1 hbest.1
      refine hgood _ ih v u hu.ne' (fun w hw => hbest.2 _ ?_) hneg
      exact (mem_candidateClusters_iff _ _ v _).2 ⟨w, hw.symm, rfl⟩
  have hstop : ∀ C ∈ R, (∀ v, ∀ c' ∈ candidateClusters ⊤ C v, 0 ≤ deltaD Ps v (C.part v) c') →
      C = stop := by
    intro C hC hstable
    simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl
    · exact absurd (hstable 0 {1} (by decide +kernel)) (by decide +kernel)
    · exact absurd (hstable 2 {3} (by decide +kernel)) (by decide +kernel)
    · exact absurd (hstable 0 {1} (by decide +kernel)) (by decide +kernel)
    · rfl
  refine ⟨Ps, exists_stable Ps ⊥, fun C hrun hstable hmed => ?_⟩
  have hC := hstop C (hreach C hrun) ((not_canMove_iff _ _ _).1 hstable)
  subst hC
  exact absurd (hmed (ofLabels (![0, 0, 0, 0] : Fin 4 → Fin 2))) (by decide +kernel)

/-- **Methods** (`claim:order-dependence`). "The order in which vertices are moved influences the set
of potential moves for `v`." On the path `0 - 1 - 2`, with one input partition that puts all the
vertices together, `C_2` is `{{1}}` at the start. After `1` moves to `{0}`, a greedy move, it is
`{{0, 1}}`. -/
theorem order_influences_candidates :
    ∃ (G : SimpleGraph (Fin 3)) (_ : DecidableRel G.Adj) (Ps : Fin 1 → Clustering (Fin 3)),
      GreedyStep G Ps ⊥ (moveVertex ⊥ 1 {0}) ∧ candidateClusters G ⊥ 2 = {{1}} ∧
        candidateClusters G (moveVertex ⊥ 1 {0}) 2 = {{0, 1}} := by
  let G : SimpleGraph (Fin 3) :=
    SimpleGraph.fromRel fun a b => (a, b) ∈ ([(0, 1), (1, 2)] : List (Fin 3 × Fin 3))
  let Ps : Fin 1 → Clustering (Fin 3) := ![ofLabels (![0, 0, 0] : Fin 3 → Fin 1)]
  exact ⟨G, inferInstance, Ps, ⟨1, {0}, by decide +kernel, by decide +kernel, rfl⟩,
    by decide +kernel, by decide +kernel⟩

/-- A greedy move in which the best move of the moved vertex is unique: no tie is broken. -/
def UniqueGreedyStep {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] (Ps : Fin k → Clustering V) (C C' : Clustering V) : Prop :=
  ∃ v c', IsBestMove G Ps C v c' ∧ (∀ c'', IsBestMove G Ps C v c'' → c'' = c') ∧
    deltaD Ps v (C.part v) c' < 0 ∧ C' = moveVertex C v c'

/-- The order of the moves also influences the result. Two runs from the singletons on the same
inputs, on the complete graph, stop at partitions with different values of the objective, although
every move of both runs is the unique best move of its vertex: the runs differ only in which vertex
moves. They stop at total distances `13` and `12`, the second being the optimum. -/
theorem greedy_order_dependent :
    ∃ (Ps : Fin 5 → Clustering (Fin 4)) (C₁ C₂ : Clustering (Fin 4)),
      Relation.ReflTransGen (UniqueGreedyStep ⊤ Ps) ⊥ C₁ ∧ ¬CanMove ⊤ Ps C₁ ∧
        Relation.ReflTransGen (UniqueGreedyStep ⊤ Ps) ⊥ C₂ ∧ ¬CanMove ⊤ Ps C₂ ∧
          objective Ps C₁ ≠ objective Ps C₂ := by
  let Ps : Fin 5 → Clustering (Fin 4) :=
    ![ofLabels (![0, 1, 0, 2] : Fin 4 → Fin 3), ofLabels (![0, 0, 0, 0] : Fin 4 → Fin 3),
      ofLabels (![0, 0, 0, 0] : Fin 4 → Fin 3), ofLabels (![0, 1, 2, 0] : Fin 4 → Fin 3),
      ofLabels (![0, 0, 0, 1] : Fin 4 → Fin 3)]
  let C₀ := moveVertex (⊥ : Clustering (Fin 4)) 3 {0}
  have h0 : UniqueGreedyStep ⊤ Ps ⊥ C₀ :=
    ⟨3, {0}, by decide +kernel, by decide +kernel, by decide +kernel, rfl⟩
  let C₁₁ := moveVertex C₀ 2 {0, 3}
  have h11 : UniqueGreedyStep ⊤ Ps C₀ C₁₁ :=
    ⟨2, {0, 3}, by decide +kernel, by decide +kernel, by decide +kernel, rfl⟩
  have h12 : UniqueGreedyStep ⊤ Ps C₁₁ (moveVertex C₁₁ 1 {0, 2, 3}) :=
    ⟨1, {0, 2, 3}, by decide +kernel, by decide +kernel, by decide +kernel, rfl⟩
  let C₂₁ := moveVertex C₀ 1 {2}
  have h21 : UniqueGreedyStep ⊤ Ps C₀ C₂₁ :=
    ⟨1, {2}, by decide +kernel, by decide +kernel, by decide +kernel, rfl⟩
  have h22 : UniqueGreedyStep ⊤ Ps C₂₁ (moveVertex C₂₁ 0 {1, 2}) :=
    ⟨0, {1, 2}, by decide +kernel, by decide +kernel, by decide +kernel, rfl⟩
  exact ⟨Ps, moveVertex C₁₁ 1 {0, 2, 3}, moveVertex C₂₁ 0 {1, 2},
    .head h0 (.head h11 (.head h12 .refl)), (not_canMove_iff _ _ _).2 (by decide +kernel),
    .head h0 (.head h21 (.head h22 .refl)), (not_canMove_iff _ _ _).2 (by decide +kernel),
    by decide +kernel⟩

/-- The restriction to clusters containing a neighbour can stop the algorithm at the singletons, with
inputs in full agreement. Here `G` is the 4-cycle `0 - 2 - 1 - 3 - 0`, which is connected, and the one
input is `{{0, 1}, {2, 3}}`, whose clusters are disconnected in `G`. The median has distance `0` from
the input and the singletons have a positive distance, so this restriction alone has no approximation
guarantee. -/
theorem graph_restriction_stuck :
    ∃ (G : SimpleGraph (Fin 4)) (_ : DecidableRel G.Adj) (P : Clustering (Fin 4)),
      G.Connected ∧ ¬CanMove G ![P] ⊥ ∧ totalDistance ![P] P = 0 ∧ 0 < totalDistance ![P] ⊥ := by
  let G : SimpleGraph (Fin 4) :=
    SimpleGraph.fromRel fun a b => (a, b) ∈ ([(0, 2), (1, 2), (1, 3), (0, 3)] : List (Fin 4 × Fin 4))
  let P : Clustering (Fin 4) := ofLabels (![0, 0, 1, 1] : Fin 4 → Fin 2)
  have h02 : G.Adj 0 2 := by decide +kernel
  have h21 : G.Adj 2 1 := by decide +kernel
  have h03 : G.Adj 0 3 := by decide +kernel
  have hfrom0 : ∀ x, G.Reachable 0 x := by
    intro x
    fin_cases x
    · exact SimpleGraph.Reachable.refl _
    · exact h02.reachable.trans h21.reachable
    · exact h02.reachable
    · exact h03.reachable
  have hconn : G.Connected :=
    { preconnected := fun x y => (hfrom0 x).symm.trans (hfrom0 y)
      nonempty := ⟨0⟩ }
  exact ⟨G, inferInstance, P, hconn, (not_canMove_iff _ _ _).2 (by decide +kernel),
    by decide +kernel, by decide +kernel⟩

end MedianConsensus
