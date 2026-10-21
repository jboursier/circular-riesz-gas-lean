/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.StrictConvRepresentation
public import Riesz1.HelfferSjostrand.EnergyComparisonsEnergy
public import Riesz1.ToMathlib.VarianceFrozenIntegral

/-!
# Comparison of anchored variances

Lemma 3.5, variance assertion, for the anchored law `μ*`. If
`F, G ∈ H¹(μ*)` satisfy `|∂_i F| ≤ ∂_i G` for every coordinate, then `Var_{μ*} F ≤ Var_{μ*} G`.

The proof identifies the variance with the anchored energy of the gradient. By the representation
of Remark 3.2, `Var F = ⟪∇F, T* ∇F⟫`, which is the energy `𝒥_{μ*}(∇F)`. The energy
assertion (`Riesz1.anchoredInverseEnergy_mono_of_abs_le`) then gives `𝒥_{μ*}(∇F) ≤ 𝒥_{μ*}(∇G)`.
The external Poincaré input enters as the hypothesis `External.PrekopaLeindler`.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- The anchored energy of the gradient of `F ∈ H¹(μ*)` is the variance `∫ (F - ∫F)²` of `F`. -/
theorem anchoredInverseEnergy_grad_eq_integral (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (hPL : External.PrekopaLeindler) (hn : 0 < n) {C_N : ℝ} (hadm : HsAdmissible χ C_N)
    (F : AnchoredSobolev χ) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    anchoredInverseEnergy χ hc F.val.2 =
      ∫ y, (F.val.1 y - ∫ x, F.val.1 x ∂(anchoredMeasureE χ)) ^ 2 ∂(anchoredMeasureE χ) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  obtain ⟨-, -, hFF⟩ := anchoredRepresentation χ hc hPL hn hadm F F
  show inner ℝ F.val.2 (anchoredVectorValues (anchoredMeasureE χ) χ (anchoredInverse χ hc F.val.2)) = _
  rw [L2.inner_def]
  simp only [pow_two]
  exact hFF.symm

/-- Lemma 3.5, variance assertion. Let `F, G ∈ H¹(μ*)` satisfy
`|∂_i F| ≤ ∂_i G` almost everywhere for every coordinate `i`. Then `Var_{μ*} F ≤ Var_{μ*} G`,
with the variance `Riesz1.variance`. -/
theorem anchoredVariance_mono_of_grad_abs_le (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (hPL : External.PrekopaLeindler) {C_N : ℝ} (hadm : HsAdmissible χ C_N)
    (F G : AnchoredSobolev χ)
    (hFG : ∀ i : Fin n, ∀ᵐ y ∂(anchoredMeasureE χ), |F.val.2 y i| ≤ G.val.2 y i) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    Riesz1.variance (anchoredMeasureE χ) ⇑F.val.1 ((Lp.memLp F.val.1).integrable one_le_two) ≤
      Riesz1.variance (anchoredMeasureE χ) ⇑G.val.1 ((Lp.memLp G.val.1).integrable one_le_two) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  -- The representation needs `0 < n`, which is `N ≥ 2` for `N = n + 1`.
  have hn : 0 < n := by
    obtain ⟨hN, -⟩ := hadm
    simp only [Nat.succPNat_coe] at hN
    omega
  rw [variance_eq_ofReal_integral_sq (anchoredMeasureE χ) ⇑F.val.1 (Lp.memLp F.val.1),
    variance_eq_ofReal_integral_sq (anchoredMeasureE χ) ⇑G.val.1 (Lp.memLp G.val.1)]
  apply ENNReal.ofReal_le_ofReal
  rw [← anchoredInverseEnergy_grad_eq_integral χ hc hPL hn hadm F,
    ← anchoredInverseEnergy_grad_eq_integral χ hc hPL hn hadm G]
  exact anchoredInverseEnergy_mono_of_abs_le χ hc F.val.2 G.val.2 hFG

end Riesz1

end
