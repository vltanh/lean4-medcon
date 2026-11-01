module

public import MedianConsensus.GraphAware.BestMove
public import Mathlib.Logic.Relation

/-!
# The greedy algorithm

Section "The algorithm" of the paper, for the moves made one at a time. The paper gives no proof
that the algorithm stops; this file proves that every run from any partition is finite and bounds
its length. The moves performed together are in `MedianConsensus.Algorithm.Parallel`.
-/

@[expose] public section

open Finset

namespace MedianConsensus

variable {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Each greedy move strictly decreases the objective of Eq. (4). -/
theorem objective_lt_of_greedyStep {Ps : Fin k → Clustering V} {C C' : Clustering V}
    (h : GreedyStep G Ps C C') : objective Ps C' < objective Ps C := by
  obtain ⟨v, c', hbest, hneg, rfl⟩ := h
  have := (equation5 Ps C v (mem_parts_of_mem_candidateClusters G hbest.1)).1
  omega

/-- Each greedy move strictly decreases the total distance `∑_i d(C, P_i)`. -/
theorem totalDistance_lt_of_greedyStep {Ps : Fin k → Clustering V} {C C' : Clustering V}
    (h : GreedyStep G Ps C C') : totalDistance Ps C' < totalDistance Ps C := by
  obtain ⟨v, c', hbest, hneg, rfl⟩ := h
  exact moveVertex_reduces Ps C v (mem_parts_of_mem_candidateClusters G hbest.1) hneg

/-- **The algorithm stops** (`claim:terminates`). There is no infinite sequence of greedy moves. -/
theorem greedyStep_wellFounded (Ps : Fin k → Clustering V) :
    WellFounded fun C' C => GreedyStep G Ps C C' :=
  Subrelation.wf (fun {_ _} h => totalDistance_lt_of_greedyStep h)
    (InvImage.wf (totalDistance Ps) Nat.lt_wfRel.wf)

/-- From every partition, in particular from the singletons of the initialization, some sequence of
greedy moves reaches a partition in which no vertex can be moved. -/
theorem exists_stable (Ps : Fin k → Clustering V) (C₀ : Clustering V) :
    ∃ C, Relation.ReflTransGen (GreedyStep G Ps) C₀ C ∧ ¬CanMove G Ps C := by
  induction C₀ using (greedyStep_wellFounded (G := G) Ps).induction with
  | _ C₀ ih =>
    by_cases hmove : CanMove G Ps C₀
    · obtain ⟨v, c', hbest, hneg⟩ := hmove
      have hstep : GreedyStep G Ps C₀ (moveVertex C₀ v c') := ⟨v, c', hbest, hneg, rfl⟩
      obtain ⟨C, hrun, hstable⟩ := ih _ hstep
      exact ⟨C, Relation.ReflTransGen.head hstep hrun, hstable⟩
    · exact ⟨C₀, Relation.ReflTransGen.refl, hmove⟩

/-- A sequence of greedy moves has at most `k n (n - 1) / 2` moves: the total distance is a natural
number, at most `k` times the number of pairs, and each move decreases it. -/
theorem greedy_run_length_le {Ps : Fin k → Clustering V} {s : ℕ → Clustering V} {m : ℕ}
    (h : ∀ i < m, GreedyStep G Ps (s i) (s (i + 1))) :
    2 * m ≤ k * (Fintype.card V * (Fintype.card V - 1)) := by
  have hbound : totalDistance Ps (s 0) ≤ k * #(pairs V) := by
    calc totalDistance Ps (s 0) ≤ #(univ : Finset (Fin k)) • #(pairs V) := by
          refine sum_le_card_nsmul _ _ _ fun i _ => ?_
          rw [mirkin_eq_card_symmDiff_coPairs]
          refine card_le_card fun p hp => ?_
          rcases mem_symmDiff.1 hp with hp | hp <;> exact (mem_filter.1 hp.1).1
      _ = k * #(pairs V) := by simp
  have hstep : ∀ i ≤ m, totalDistance Ps (s i) + i ≤ totalDistance Ps (s 0) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro hi
      have := totalDistance_lt_of_greedyStep (h i (by omega))
      have := ih (by omega)
      omega
  have hm := hstep m le_rfl
  have hpairs : 2 * #(pairs V) = Fintype.card V * (Fintype.card V - 1) := by
    rw [pairs, card_filter_lt, Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd
  rw [← hpairs]
  nlinarith

end MedianConsensus
