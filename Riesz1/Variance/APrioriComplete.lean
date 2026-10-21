/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriFinalCircle
public import Riesz1.Bridges.InputConsolidation

/-!
# The a priori variance bound

Lemma 5.2, every assertion. It takes the Bakry–Émery criterion `External.BakryEmery` and the
Prékopa–Leindler inequality `External.PrekopaLeindler` as hypotheses and nothing else.
`Riesz1.Internal.aPrioriConclusion_of_externals` proves the `Prop`
`Riesz1.Internal.APrioriConclusion`, and `Riesz1.a_priori` is the statement.
The anchored bound is asserted at centre zero and every radius, and the non-anchored bound at
every centre and radius. The constant of each part comes from
`Riesz1.a_priori_at_origin_circle` and `Riesz1.a_priori_plain_translate`. Their maximum serves
both.
-/

public section

open MeasureTheory

namespace Riesz1.Internal

/-- Lemma 5.2, from `External.BakryEmery` and `External.PrekopaLeindler` only. -/
theorem aPrioriConclusion_of_externals (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) : APrioriConclusion := by
  intro P lam hlam ε hε R hR c
  obtain ⟨C₁, hC₁, h₁⟩ := a_priori_at_origin_circle hBE hPL P lam ε R hlam hε hR
  obtain ⟨C₂, hC₂, h₂⟩ := a_priori_plain_translate hBE hPL P lam ε R hlam hε hR
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, fun N ℓ hK M hM f hf hd => ⟨fun hc => ?_, ?_⟩⟩
  · subst hc
    obtain ⟨hA, hV⟩ := (h₁ N ℓ hK M hM f hf hd).1
    refine ⟨hA, hV.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    gcongr
    exact le_max_left _ _
  · obtain ⟨hB, hV⟩ := h₂ N ℓ hK M hM c f hf hd
    refine ⟨hB, hV.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    gcongr
    exact le_max_right _ _

/-- The input `ErrorTwoAPrioriInput` of the proof of Theorem 3, from `External.BakryEmery` and
`External.PrekopaLeindler` only. -/
theorem errorTwoAPrioriInput_of_externals (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) : ErrorTwoAPrioriInput :=
  errorTwoAPrioriInput_of_aPrioriConclusion (aPrioriConclusion_of_externals hBE hPL)

end Riesz1.Internal

namespace Riesz1

/-- **Lemma 5.2.** Let `0 < s < 1`, `β > 0`, `λ ≥ 0`, `ε > 0`, a radius
`R > 0` and a centre `c`. There is `C > 0` such that for every `N ≥ 1`, every scale `ℓ` with
`Nℓ ≥ 1`, every `M ≥ 0` and every `C¹` function `f` on the circle of length `ℓ⁻¹` whose
derivative is bounded by `M` times the envelope of radius `R` centred at `c`, the non-anchored
sum `Σ_i f(x_i/ℓ)` has variance at most `C M² (Nℓ)^{ε+max(2λ,s)}`, and so does the anchored sum
`Σ_i f((x_i - x_1)/ℓ)` when `c = 0`. -/
theorem a_priori (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler) :
    Internal.APrioriConclusion :=
  Internal.aPrioriConclusion_of_externals hBE hPL

end Riesz1
