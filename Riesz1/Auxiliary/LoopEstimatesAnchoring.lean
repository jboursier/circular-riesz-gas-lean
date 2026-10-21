/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopEstimatesInput
public import Riesz1.Auxiliary.LoopAnchoringComplete

/-!
# Discharging the anchoring input

The anchoring theorem supplies exactly `LoopAnchoringL2Input`.
The coordinate identity already proved for preceding particles identifies
its anchored vector with the vector used in that input.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz1.Internal

/-- The conditional input is now supplied by the anchoring result,
with only the Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler inequality
`External.PrekopaLeindler` as hypotheses. -/
theorem loopAnchoringL2Input_of_externals
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler) : LoopAnchoringL2Input := by
  intro s α γ hs hs1 hα hα2 hγ
  obtain ⟨ε₀, hε₀, κ, hκ, h⟩ := loopAnchoring_uniform hs hs1 hα hα2 hγ
  refine ⟨ε₀, κ, hε₀, hκ, ?_⟩
  intro β hβ hs' hs1' χ hχ hχc hχs hχ1 hχ01 ε hε hε1
  obtain ⟨C, hC, hc⟩ := h β hβ hBE hPL χ hχ hχc hχs hχ1 hχ01 ε hε hε1
  refine ⟨C, hC, ?_⟩
  intro C₀ hC₀ n ℓ ψ hℓ hℓ1 hK hψ hper hd hdd
  obtain ⟨hF, hFw, hE, hnorm, hvar⟩ := hc n ℓ C₀ ψ hℓ hℓ1 hK hC₀ hψ hper hd hdd
  simpa only [loopPrecedingY_eq_anchorVector, Nat.succPNat_coe, Nat.succ_sub_one] using hnorm

end Riesz1.Internal

end
