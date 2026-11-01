module

public import MedianConsensus.GraphAware.Move

/-!
# The best move of a vertex: Eq. (6)
-/

@[expose] public section

open Finset

namespace MedianConsensus

variable {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ}
variable (G : SimpleGraph V) [DecidableRel G.Adj]

instance (Ps : Fin k → Clustering V) (C : Clustering V) (v : V) (c' : Finset V) :
    Decidable (IsBestMove G Ps C v c') :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The clusters of `C_v` are the clusters of the neighbours of `v`. -/
theorem mem_candidateClusters_iff (C : Clustering V) (v : V) (c' : Finset V) :
    c' ∈ candidateClusters G C v ↔ ∃ u, G.Adj v u ∧ c' = C.part u := by
  simp only [candidateClusters, mem_filter]
  constructor
  · rintro ⟨hc, u, hu, hadj⟩
    exact ⟨u, hadj, (C.part_eq_of_mem hc hu).symm⟩
  · rintro ⟨u, hadj, rfl⟩
    exact ⟨C.part_mem.2 (mem_univ u), u, C.mem_part (mem_univ u), hadj⟩

/-- The clusters of `C_v` are clusters of `C`. -/
theorem mem_parts_of_mem_candidateClusters {C : Clustering V} {v : V} {c' : Finset V}
    (h : c' ∈ candidateClusters G C v) : c' ∈ C.parts :=
  (mem_filter.1 h).1

/-- **Equation (6)** (`eq:objective4`). The `argmin` of Eq. (6) exists exactly when `C_v` is nonempty,
that is, when `v` has a neighbour. -/
theorem equation6 (Ps : Fin k → Clustering V) (C : Clustering V) (v : V) :
    (∃ c', IsBestMove G Ps C v c') ↔ ∃ u, G.Adj v u := by
  constructor
  · rintro ⟨c', hc', -⟩
    obtain ⟨u, hu, -⟩ := (mem_candidateClusters_iff G C v c').1 hc'
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    have hne : (candidateClusters G C v).Nonempty :=
      ⟨C.part u, (mem_candidateClusters_iff G C v _).2 ⟨u, hu, rfl⟩⟩
    obtain ⟨c', hc', hmin⟩ := exists_min_image _ (fun c' => deltaD Ps v (C.part v) c') hne
    exact ⟨c', hc', hmin⟩

/-- **The stopping condition** (`claim:stopping`). No vertex can be moved exactly when no candidate
cluster of any vertex has `ΔD < 0`. -/
theorem not_canMove_iff (Ps : Fin k → Clustering V) (C : Clustering V) :
    ¬CanMove G Ps C ↔ ∀ v, ∀ c' ∈ candidateClusters G C v, 0 ≤ deltaD Ps v (C.part v) c' := by
  constructor
  · intro h v c' hc'
    by_contra hneg
    obtain ⟨c'', hc'', hmin⟩ :=
      exists_min_image _ (fun d => deltaD Ps v (C.part v) d) ⟨c', hc'⟩
    exact h ⟨v, c'', ⟨hc'', hmin⟩, lt_of_le_of_lt (hmin c' hc') (not_le.1 hneg)⟩
  · rintro h ⟨v, c', hbest, hneg⟩
    exact absurd hneg (not_lt.2 (h v c' hbest.1))

end MedianConsensus
