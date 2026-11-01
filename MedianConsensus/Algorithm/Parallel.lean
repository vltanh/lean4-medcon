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

instance (Ps : Fin k → Clustering V) (C : Clustering V) (t : V → Finset V) :
    Decidable (IsBatchTarget G Ps C t) :=
  inferInstanceAs (Decidable (∀ _, _))

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
  let Ps : Fin 3 → Clustering (Fin 3) :=
    ![ofLabels (![0, 0, 0] : Fin 3 → Fin 2), ofLabels (![0, 0, 1] : Fin 3 → Fin 2),
      ofLabels (![0, 1, 0] : Fin 3 → Fin 2)]
  let t₀ : Fin 3 → Finset (Fin 3) := ![{1}, {0}, {0}]
  let t₀' : Fin 3 → Finset (Fin 3) := ![{2}, {0}, {0}]
  let t₁ : Fin 3 → Finset (Fin 3) := ![{1, 2}, {0}, {0}]
  let C₁ : Clustering (Fin 3) := ofLabels t₀
  have heq' : ofLabels t₀' = C₁ := eq_of_coClustered_iff fun u v _ => by
    simp only [C₁, coClustered_ofLabels]
    revert u v
    decide
  have heq₁ : ofLabels t₁ = C₁ := eq_of_coClustered_iff fun u v _ => by
    simp only [C₁, coClustered_ofLabels]
    revert u v
    decide
  have hfirst : ∀ v c', (IsBestMove ⊤ Ps ⊥ v c' ∧ deltaD Ps v ((⊥ : Clustering (Fin 3)).part v) c' < 0) ∨
      (c' = (⊥ : Clustering (Fin 3)).part v ∧ ∀ c'', IsBestMove ⊤ Ps ⊥ v c'' →
        0 ≤ deltaD Ps v ((⊥ : Clustering (Fin 3)).part v) c'') → c' = t₀ v ∨ c' = t₀' v := by
    decide +kernel
  have hsecond : ∀ v c', (IsBestMove ⊤ Ps C₁ v c' ∧ deltaD Ps v (C₁.part v) c' < 0) ∨
      (c' = C₁.part v ∧ ∀ c'', IsBestMove ⊤ Ps C₁ v c'' → 0 ≤ deltaD Ps v (C₁.part v) c'') →
      c' = t₁ v := by
    decide +kernel
  refine ⟨Ps, C₁, ⟨t₀, by decide +kernel, rfl⟩, ?_, by decide +kernel,
    ⟨t₁, by decide +kernel, heq₁.symm⟩, ?_, ⟨1, {0}, by decide +kernel, by decide +kernel⟩⟩
  · rintro C' ⟨t, ht, rfl⟩
    have h0 := hfirst 0 (t 0) (ht 0)
    have h1 := hfirst 1 (t 1) (ht 1)
    have h2 := hfirst 2 (t 2) (ht 2)
    have h1' : t 1 = {0} := by simpa [t₀, t₀'] using h1
    have h2' : t 2 = {0} := by simpa [t₀, t₀'] using h2
    rcases h0 with h0 | h0
    · congr 1
      funext x
      fin_cases x
      · exact h0
      · exact h1'
      · exact h2'
    · rw [← heq']
      congr 1
      funext x
      fin_cases x
      · exact h0
      · exact h1'
      · exact h2'
  · rintro C' ⟨t, ht, rfl⟩
    rw [← heq₁]
    congr 1
    funext x
    exact hsecond x (t x) (ht x)

end MedianConsensus
