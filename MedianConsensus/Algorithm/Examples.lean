module

public import MedianConsensus.Algorithm.Greedy
public import Mathlib.Tactic.DeriveFintype

/-!
# Small examples of the greedy algorithm

Certified instances of the paper's remarks on the greedy policy. All three use small explicit
inputs, found by exhaustive search.
-/

@[expose] public section

open Finset

namespace MedianConsensus

/-- **Methods** (`claim:greedy-not-optimal`). "This greedy moving policy, like any greedy algorithm,
does not guarantee an optimal solution." The instance has four vertices and three input partitions,
on the complete graph, so the graph is not the cause: the algorithm, started from the singletons,
stops at a partition that is not a median partition. -/
theorem greedy_not_optimal :
    ∃ (Ps : Fin 3 → Clustering (Fin 4)) (C : Clustering (Fin 4)),
      Relation.ReflTransGen (GreedyStep ⊤ Ps) ⊥ C ∧ ¬CanMove ⊤ Ps C ∧ ¬IsMedian Ps C := by
  sorry

/-- **Methods** (`claim:order-dependence`). "The order in which vertices are moved influences the set
of potential moves": two runs from the singletons on the same inputs stop at partitions with
different values of the objective. -/
theorem greedy_order_dependent :
    ∃ (Ps : Fin 3 → Clustering (Fin 4)) (C₁ C₂ : Clustering (Fin 4)),
      Relation.ReflTransGen (GreedyStep ⊤ Ps) ⊥ C₁ ∧ ¬CanMove ⊤ Ps C₁ ∧
        Relation.ReflTransGen (GreedyStep ⊤ Ps) ⊥ C₂ ∧ ¬CanMove ⊤ Ps C₂ ∧
          objective Ps C₁ ≠ objective Ps C₂ := by
  sorry

/-- The restriction to clusters containing a neighbour can stop the algorithm at the singletons,
with inputs in full agreement. Here `G` is the 4-cycle `0 - 2 - 1 - 3 - 0`, and the input is
`{{0, 1}, {2, 3}}`: each input cluster is disconnected in `G`. The median has distance `0` from the
input and the singletons have a positive distance, so this restriction has no approximation
guarantee. -/
theorem graph_restriction_stuck :
    ∃ (G : SimpleGraph (Fin 4)) (_ : DecidableRel G.Adj) (P : Clustering (Fin 4)),
      ¬CanMove G ![P] ⊥ ∧ totalDistance ![P] P = 0 ∧ 0 < totalDistance ![P] ⊥ := by
  sorry

end MedianConsensus
