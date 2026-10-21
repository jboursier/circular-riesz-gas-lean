/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.EnergyComparisonsEnergy

/-!
# Energy comparison for the a priori estimate

Homogeneity and the scaled instance of Lemma 3.5 needed by the comparison assertion
in the proof of Lemma 5.2, using coordinate domination for the anchored inverse.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace

namespace Riesz1.APrioriComparison

variable {n : ℕ} {c : ℝ}

/-- Homogeneity of the inverse energy. -/
theorem inverseEnergy_smul (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (t : ℝ) (w : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ)) :
    anchoredInverseEnergy χ hc (t • w) = t ^ 2 * anchoredInverseEnergy χ hc w := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  change inner ℝ (t • w)
    (anchoredVectorValues (anchoredMeasureE χ) χ (anchoredInverse χ hc (t • w))) =
      t ^ 2 * inner ℝ w (anchoredVectorValues (anchoredMeasureE χ) χ (anchoredInverse χ hc w))
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- The scaled coordinate comparison used for `ηv` and `η∇G`. -/
theorem inverseEnergy_le_scaled (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (v w : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ)) (t : ℝ)
    (hvw : ∀ i, ∀ᵐ y ∂anchoredMeasureE χ, |v y i| ≤ t * w y i) :
    anchoredInverseEnergy χ hc v ≤ t ^ 2 * anchoredInverseEnergy χ hc w := by
  rw [← inverseEnergy_smul χ hc]
  apply anchoredInverseEnergy_mono_of_abs_le χ hc
  intro i
  filter_upwards [hvw i, Lp.coeFn_smul t w] with y hy ht
  rw [ht]
  exact hy

end Riesz1.APrioriComparison

end
