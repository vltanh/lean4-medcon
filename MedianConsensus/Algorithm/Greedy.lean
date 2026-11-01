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
  sorry

/-- Each greedy move strictly decreases the total distance `∑_i d(C, P_i)`. -/
theorem totalDistance_lt_of_greedyStep {Ps : Fin k → Clustering V} {C C' : Clustering V}
    (h : GreedyStep G Ps C C') : totalDistance Ps C' < totalDistance Ps C := by
  sorry

/-- **The algorithm stops** (`claim:terminates`). There is no infinite sequence of greedy moves. -/
theorem greedyStep_wellFounded (Ps : Fin k → Clustering V) :
    WellFounded fun C' C => GreedyStep G Ps C C' := by
  sorry

/-- From every partition, in particular from the singletons of the initialization, some sequence of
greedy moves reaches a partition in which no vertex can be moved. -/
theorem exists_stable (Ps : Fin k → Clustering V) (C₀ : Clustering V) :
    ∃ C, Relation.ReflTransGen (GreedyStep G Ps) C₀ C ∧ ¬CanMove G Ps C := by
  sorry

/-- A sequence of greedy moves has at most `k n (n - 1)` moves, since the objective is an integer
of absolute value at most `k n (n - 1) / 2`. -/
theorem greedy_run_length_le {Ps : Fin k → Clustering V} {s : ℕ → Clustering V} {m : ℕ}
    (h : ∀ i < m, GreedyStep G Ps (s i) (s (i + 1))) :
    m ≤ k * (Fintype.card V * (Fintype.card V - 1)) := by
  sorry

end MedianConsensus
