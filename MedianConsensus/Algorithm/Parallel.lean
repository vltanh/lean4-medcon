module

public import MedianConsensus.Algorithm.Greedy

/-!
# Moves performed together

Section "Parallel algorithm" of the paper: "identifies the best possible move for every vertex
considering the consensus partition at the beginning of the iteration. After some validation checks
of the identified moves, all moves are performed together at the end of the iteration."

The paper does not say what the validation checks are, so this file formalizes the iteration
without them. Its one theorem shows that some checks are needed: the unchecked iteration can raise
the objective, and can then never stop.
-/

@[expose] public section

open Finset

namespace MedianConsensus

variable {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ}
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The target of each vertex in an iteration: a best move of Eq. (6) with `ΔD < 0`, if it has one,
and otherwise its current cluster. -/
def IsBatchTarget (Ps : Fin k → Clustering V) (C : Clustering V) (t : V → Finset V) : Prop :=
  ∀ v, (IsBestMove G Ps C v (t v) ∧ deltaD Ps v (C.part v) (t v) < 0) ∨
    (t v = C.part v ∧ ∀ c', IsBestMove G Ps C v c' → 0 ≤ deltaD Ps v (C.part v) c')

/-- One iteration without validation checks: all the moves are performed together. -/
def BatchStep (Ps : Fin k → Clustering V) (C C' : Clustering V) : Prop :=
  ∃ t, IsBatchTarget G Ps C t ∧ C' = ofLabels t

/-- **Parallel algorithm** (`claim:batch`). Without validation checks, performing all the best moves
together can raise the objective and then never stop. The instance has three vertices and three
input partitions, on the complete graph. From the singletons, whichever minimizers are chosen,
every iteration leads to one partition `C₁`, with a larger objective. From `C₁`, every iteration
leads back to `C₁`, although vertices can still be moved there. -/
theorem batch_counterexample :
    ∃ (Ps : Fin 3 → Clustering (Fin 3)) (C₁ : Clustering (Fin 3)),
      BatchStep ⊤ Ps ⊥ C₁ ∧ (∀ C', BatchStep ⊤ Ps ⊥ C' → C' = C₁) ∧
        objective Ps ⊥ < objective Ps C₁ ∧
          BatchStep ⊤ Ps C₁ C₁ ∧ (∀ C', BatchStep ⊤ Ps C₁ C' → C' = C₁) ∧ CanMove ⊤ Ps C₁ := by
  sorry

end MedianConsensus
