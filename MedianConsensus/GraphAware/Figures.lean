module

public import MedianConsensus.GraphAware.BestMove
public import Mathlib.Tactic.DeriveFintype

/-!
# The worked example of Figs. 1 and 2

The paper's own example, computed from the definitions. The partitions and the graph are read from
Fig. 1, and the consensus clustering from Fig. 2.
-/

@[expose] public section

open Finset

namespace MedianConsensus

/-- **Fig. 1** (`fig:input`). `δ_{v₀v₁} = 1`, `δ_{v₀v₄} = 0` and `δ_{v₃v₉} = 2`. -/
theorem figure1 :
    deltaTotal figurePartitions 0 1 = 1 ∧ deltaTotal figurePartitions 0 4 = 0 ∧
      deltaTotal figurePartitions 3 9 = 2 := by
  decide +kernel

/-- **Fig. 2** (`fig:moves`). The clusters of the consensus are `c₁, …, c₄`; `v₃` lies in `c₁`;
`c₄` contains no neighbour of `v₃`, so `C_{v₃} = {c₁, c₂, c₃}`; the sums over `c₁, c₂, c₃` are `0`,
`4`, `2`, with `v₃` itself left out of the first; hence `ΔD_{v₃ : c₁ → c₂} = -4` and
`ΔD_{v₃ : c₁ → c₃} = -2`; the best move is to `c₂`, and "it reduces the total distance by 4". -/
theorem figure2 :
    figureConsensus.parts = {figureC1, figureC2, figureC3, figureC4} ∧
      figureConsensus.part 3 = figureC1 ∧
      candidateClusters figureGraph figureConsensus 3 = {figureC1, figureC2, figureC3} ∧
      ∑ u ∈ figureC1.erase 3, ((4 : ℤ) - 2 * deltaTotal figurePartitions u 3) = 0 ∧
      ∑ u ∈ figureC2, ((4 : ℤ) - 2 * deltaTotal figurePartitions u 3) = 4 ∧
      ∑ u ∈ figureC3, ((4 : ℤ) - 2 * deltaTotal figurePartitions u 3) = 2 ∧
      deltaD figurePartitions 3 figureC1 figureC2 = -4 ∧
      deltaD figurePartitions 3 figureC1 figureC3 = -2 ∧
      IsBestMove figureGraph figurePartitions figureConsensus 3 figureC2 ∧
      (totalDistance figurePartitions figureConsensus : ℤ) -
        totalDistance figurePartitions (moveVertex figureConsensus 3 figureC2) = 4 := by
  have hpart : figureConsensus.part 3 = figureC1 := by decide +kernel
  have hcand : candidateClusters figureGraph figureConsensus 3 =
      {figureC1, figureC2, figureC3} := by decide +kernel
  have h2 : deltaD figurePartitions 3 figureC1 figureC2 = -4 := by decide +kernel
  have h3 : deltaD figurePartitions 3 figureC1 figureC3 = -2 := by decide +kernel
  refine ⟨by decide +kernel, hpart, hcand, by decide +kernel, by decide +kernel, by decide +kernel,
    h2, h3, ⟨by rw [hcand]; simp, fun c'' hc'' => ?_⟩, by decide +kernel⟩
  rw [hpart, h2]
  rw [hcand, mem_insert, mem_insert, mem_singleton] at hc''
  rcases hc'' with rfl | rfl | rfl
  · rw [deltaD_self]
    decide
  · rw [h2]
  · rw [h3]
    decide

/-- The literal reading of Eq. (5), with `u = v` included in the sum, contradicts Fig. 2: it gives
`0` for the move of `v₃` to `c₂`, which would then not be made. -/
theorem figure2_literal :
    ∑ u, (((4 : ℤ) - 2 * deltaTotal figurePartitions u 3) * sigma u figureC1 -
        ((4 : ℤ) - 2 * deltaTotal figurePartitions u 3) * sigma u figureC2) = 0 := by
  decide +kernel

end MedianConsensus
