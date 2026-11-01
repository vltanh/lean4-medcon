module

public import MedianConsensus.Problem.Objective

/-!
# Moving a vertex: Eq. (5)

Section "Graph-aware consensus clustering" of the paper and the end of its appendix: the move of a
vertex between clusters, and the change `ΔD` in the objective.
-/

@[expose] public section

open Finset

namespace MedianConsensus

variable {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ}

/-- A move changes nothing between two vertices other than `v`. -/
theorem coClustered_moveVertex_of_ne (C : Clustering V) {v x y : V} (c' : Finset V) (hx : x ≠ v)
    (hy : y ≠ v) : CoClustered (moveVertex C v c') x y ↔ CoClustered C x y := by
  rw [moveVertex, coClustered_ofLabels, Function.update_of_ne hx, Function.update_of_ne hy,
    coClustered_iff_part_eq]

/-- After `v` moves to the cluster `c'`, the vertices co-clustered with `v` are those of `c'`. -/
theorem coClustered_moveVertex_self (C : Clustering V) {v u : V} {c' : Finset V}
    (hc' : c' ∈ C.parts) (hu : u ≠ v) : CoClustered (moveVertex C v c') u v ↔ u ∈ c' := by
  rw [moveVertex, coClustered_ofLabels, Function.update_of_ne hu, Function.update_self,
    C.part_eq_iff_mem hc']

/-- Moving `v` to its own cluster changes nothing. -/
theorem moveVertex_part_self (C : Clustering V) (v : V) : moveVertex C v (C.part v) = C := by
  rw [moveVertex, Function.update_eq_self, ofLabels_part]

/-- A bridge for the representation of a move by labels. If `v` moves from its cluster `c` to another
cluster `c'`, the clusters of the result are those of `C` other than `c` and `c'`, then
`c' ∪ {v}`, and `c \ {v}` unless it is empty. -/
theorem parts_moveVertex (C : Clustering V) {v : V} {c' : Finset V} (hc' : c' ∈ C.parts)
    (hne : c' ≠ C.part v) :
    (moveVertex C v c').parts =
      insert (insert v c')
        (((C.parts.erase (C.part v)).erase c') ∪
          (if (C.part v).erase v = ∅ then ∅ else {(C.part v).erase v})) := by
  set C' := moveVertex C v c' with hC'
  have hvc' : v ∉ c' := fun h => hne (C.part_eq_of_mem hc' h).symm
  have hself : C'.part v = insert v c' := by
    ext y
    rw [mem_part_iff_coClustered, mem_insert]
    by_cases hy : y = v
    · subst hy
      simp [coClustered_self]
    · simp [hy, hC', coClustered_moveVertex_self C hc' hy]
  have hmem : ∀ x, x ≠ v → x ∉ c' → C'.part x = (C.part x).erase v := by
    intro x hx hxc'
    ext y
    rw [mem_part_iff_coClustered, mem_erase]
    by_cases hy : y = v
    · subst hy
      simpa [hC', coClustered_comm, coClustered_moveVertex_self C hc' hx] using hxc'
    · rw [hC', coClustered_moveVertex_of_ne C c' hy hx, mem_part_iff_coClustered]
      simp [hy]
  have hother : ∀ d ∈ C.parts, d ≠ C.part v → d.erase v = d := by
    intro d hd hdne
    refine erase_eq_of_notMem fun h => hdne (C.part_eq_of_mem hd h).symm
  ext d
  simp only [mem_insert, mem_union, mem_erase]
  constructor
  · intro hd
    obtain ⟨x, -, rfl⟩ := C'.part_surjOn hd
    by_cases hx : x = v
    · subst hx
      exact Or.inl hself
    by_cases hxc' : x ∈ c'
    · left
      rw [← hself]
      exact C'.part_eq_of_mem (C'.part_mem.2 (mem_univ v))
        ((mem_part_iff_coClustered _ _ _).2 ((hC' ▸ coClustered_moveVertex_self C hc' hx).2 hxc'))
    · right
      rw [hmem x hx hxc']
      by_cases hxc : C.part x = C.part v
      · right
        rw [hxc]
        have hxe : x ∈ (C.part v).erase v := mem_erase.2
          ⟨hx, hxc ▸ C.mem_part (mem_univ x)⟩
        rw [ite_eq_right (Finset.ne_empty_of_mem hxe)]
        simp
      · left
        have hxpart : C.part x ∈ C.parts := C.part_mem.2 (mem_univ x)
        rw [hother _ hxpart hxc]
        refine ⟨fun h => hxc' ?_, hxc, hxpart⟩
        exact h ▸ C.mem_part (mem_univ x)
  · rintro (rfl | ⟨hne', hnec, hd⟩ | hd)
    · rw [← hself]
      exact C'.part_mem.2 (mem_univ v)
    · obtain ⟨x, hx⟩ := C.nonempty_of_mem_parts hd
      have hxv : x ≠ v := fun h => hnec (C.part_eq_of_mem hd (h ▸ hx)).symm
      have hxc' : x ∉ c' := fun h => hne' (C.eq_of_mem_parts hd hc' hx h)
      have := hmem x hxv hxc'
      rw [C.part_eq_of_mem hd hx, hother d hd hnec] at this
      rw [← this]
      exact C'.part_mem.2 (mem_univ x)
    · split_ifs at hd with h
      · simp at hd
      · rw [mem_singleton] at hd
        subst hd
        obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 h
        have hx' := mem_erase.1 hx
        have hxc' : x ∉ c' := fun h' =>
          hne (C.eq_of_mem_parts hc' (C.part_mem.2 (mem_univ v)) h' hx'.2)
        have := hmem x hx'.1 hxc'
        rw [C.part_eq_of_mem (C.part_mem.2 (mem_univ v)) hx'.2] at this
        rw [← this]
        exact C'.part_mem.2 (mem_univ x)

/-- The two right-hand sides of Eq. (5) are equal. -/
theorem deltaD_eq_second_form (Ps : Fin k → Clustering V) (v : V) (c c' : Finset V) :
    deltaD Ps v c c' =
      ∑ u ∈ univ.erase v, (sigma u c' - sigma u c) * (2 * deltaTotal Ps u v - k) :=
  sum_congr rfl fun _ _ => by ring

/-- The first line of the derivation of `ΔD` in the appendix,
`∑_{u ∈ c} (k - 2 δ_uv) - ∑_{u ∈ c'} (k - 2 δ_uv)`, with the sums over `u ≠ v`. -/
theorem deltaD_eq_sum_sub_sum (Ps : Fin k → Clustering V) (v : V) (c c' : Finset V) :
    deltaD Ps v c c' =
      ∑ u ∈ c.erase v, ((k : ℤ) - 2 * deltaTotal Ps u v) -
        ∑ u ∈ c'.erase v, ((k : ℤ) - 2 * deltaTotal Ps u v) := by
  have h : ∀ d : Finset V, ∑ u ∈ univ.erase v, ((k : ℤ) - 2 * deltaTotal Ps u v) * sigma u d =
      ∑ u ∈ d.erase v, ((k : ℤ) - 2 * deltaTotal Ps u v) := by
    intro d
    simp only [sigma, mul_ite, mul_one, mul_zero]
    rw [sum_ite_mem]
    congr 1
    ext u
    simp only [mem_inter, mem_erase, mem_univ, and_true]
  rw [deltaD, sum_sub_distrib, h, h]

/-- The term `u = v` of the sum in Eq. (5), which the sum `deltaD` leaves out. -/
theorem deltaD_self_term (Ps : Fin k → Clustering V) (v : V) (c c' : Finset V) :
    ((k : ℤ) - 2 * deltaTotal Ps v v) * sigma v c - ((k : ℤ) - 2 * deltaTotal Ps v v) * sigma v c' =
      k * (sigma v c - sigma v c') := by
  rw [deltaTotal_self]
  ring

/-- The sum of Eq. (5) read literally, over all `u` including `u = v`, differs from `ΔD` by `k` when
`v ∈ c` and `v ∉ c'`. The sum must run over `u ≠ v`. -/
theorem sum_all_eq_deltaD_add (Ps : Fin k → Clustering V) (v : V) (c c' : Finset V) :
    ∑ u, (((k : ℤ) - 2 * deltaTotal Ps u v) * sigma u c -
        ((k : ℤ) - 2 * deltaTotal Ps u v) * sigma u c') =
      deltaD Ps v c c' + k * (sigma v c - sigma v c') := by
  rw [← add_sum_erase univ _ (mem_univ v), deltaD_self_term, add_comm]
  rfl

theorem deltaD_self (Ps : Fin k → Clustering V) (v : V) (c : Finset V) : deltaD Ps v c c = 0 :=
  sum_eq_zero fun _ _ => sub_self _

/-- **Equation (5)** (`eq:objective3`). "The change in the objective function": when `v` moves from
its cluster `c` to a cluster `c'`, the objective of Eq. (4) changes by exactly `ΔD_{v : c → c'}`,
which is given by either side of Eq. (5).

Departure from the paper: the appendix asserts the change as its first line, and the rest of its
derivation is algebra. The proof shows the change directly, from the pairs that contain `v`, for the first
form of Eq. (5), and the appendix's first line is `deltaD_eq_sum_sub_sum`. This repairs a gap (`REPORT.md`,
E11), since the paper gives no argument to follow at this step. -/
theorem equation5 (Ps : Fin k → Clustering V) (C : Clustering V) (v : V) {c' : Finset V}
    (hc' : c' ∈ C.parts) :
    objective Ps (moveVertex C v c') - objective Ps C = deltaD Ps v (C.part v) c' ∧
      deltaD Ps v (C.part v) c' =
        ∑ u ∈ univ.erase v, (sigma u c' - sigma u (C.part v)) * (2 * deltaTotal Ps u v - k) := by
  refine ⟨?_, deltaD_eq_second_form Ps v _ _⟩
  set C' := moveVertex C v c' with hC'
  have hsum := sum_filter_lt_eq_sum_erase
    (fun x y => ((k : ℤ) - 2 * deltaTotal Ps x y) * (delta C' x y - delta C x y))
    (fun x y => by rw [deltaTotal_comm, delta_comm C', delta_comm C]) v
    (fun x y hx hy => by
      simp only [equation2, hC', coClustered_moveVertex_of_ne C c' hx hy, sub_self, mul_zero])
  rw [objective, objective, ← sum_sub_distrib]
  have hrewrite : ∀ p : V × V,
      ((k : ℤ) - 2 * deltaTotal Ps p.1 p.2) * delta C' p.1 p.2 -
        ((k : ℤ) - 2 * deltaTotal Ps p.1 p.2) * delta C p.1 p.2 =
      ((k : ℤ) - 2 * deltaTotal Ps p.1 p.2) * (delta C' p.1 p.2 - delta C p.1 p.2) :=
    fun p => by ring
  simp only [hrewrite]
  rw [pairs, hsum, deltaD]
  refine sum_congr rfl fun u hu => ?_
  have hu' : u ≠ v := by simpa using hu
  have h1 : delta C' u v = 1 - sigma u c' := by
    rw [equation2, hC', sigma]
    by_cases h : u ∈ c'
    · rw [ite_eq_left ((coClustered_moveVertex_self C hc' hu').2 h), ite_eq_left h, sub_self]
    · rw [ite_eq_right (mt (coClustered_moveVertex_self C hc' hu').1 h), ite_eq_right h, sub_zero]
  have h2 : delta C u v = 1 - sigma u (C.part v) := by
    rw [equation2, sigma]
    by_cases h : u ∈ C.part v
    · rw [ite_eq_left ((mem_part_iff_coClustered C u v).1 h), ite_eq_left h, sub_self]
    · rw [ite_eq_right (mt (mem_part_iff_coClustered C u v).2 h), ite_eq_right h, sub_zero]
  rw [h1, h2]
  ring

/-- The change in the total distance `∑_i d(C, P_i)` is also exactly `ΔD`. -/
theorem totalDistance_moveVertex (Ps : Fin k → Clustering V) (C : Clustering V) (v : V)
    {c' : Finset V} (hc' : c' ∈ C.parts) :
    (totalDistance Ps (moveVertex C v c') : ℤ) =
      totalDistance Ps C + deltaD Ps v (C.part v) c' := by
  rw [appendix_identity, appendix_identity, ← (equation5 Ps C v hc').1]
  ring

/-- **Methods** (`claim:negative-reduces`). "When `ΔD_{v : c → c'}` is negative, moving `v` to the
new cluster `c'` reduces the overall disagreements." -/
theorem moveVertex_reduces (Ps : Fin k → Clustering V) (C : Clustering V) (v : V) {c' : Finset V}
    (hc' : c' ∈ C.parts) (h : deltaD Ps v (C.part v) c' < 0) :
    totalDistance Ps (moveVertex C v c') < totalDistance Ps C := by
  have := totalDistance_moveVertex Ps C v hc'
  omega

end MedianConsensus
