/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Riesz1.ToMathlib.LintegralWeightedHolder

/-!
# Lower `L^q` moments and products

Tools for the `L^p` bound of the arcs part of Lemma B.2:

* `lintegral_enorm_rpow_le_of_eLpNorm`: an `eLpNorm` bound at exponent `q` gives the bound
  `∫⁻ ‖f‖ₑ^q ≤ c^q` on the lower integral.
* `lintegral_enorm_rpow_mul_le`: Cauchy–Schwarz for the `p`-th power of a product,
  `∫⁻ ‖f‖ₑ^p ‖g‖ₑ^p ≤ (∫⁻ ‖f‖ₑ^{2p})^{1/2} (∫⁻ ‖g‖ₑ^{2p})^{1/2}`.

The moments are lower integrals, so they need no measurability beyond that of the functions
themselves.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- An `eLpNorm` bound at a finite exponent `q ≥ 1` gives the lower integral bound
`∫⁻ ‖f‖ₑ^q ≤ c^q`. -/
theorem lintegral_enorm_rpow_le_of_eLpNorm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} {q c : ℝ} (hq : 1 ≤ q) (h : eLpNorm f (ENNReal.ofReal q) μ ≤ ENNReal.ofReal c) :
    ∫⁻ x, ‖f x‖ₑ ^ q ∂μ ≤ ENNReal.ofReal c ^ q := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hne : eLpNorm f (ENNReal.ofReal q) μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hmeas := aestronglyMeasurable_of_eLpNorm_ne_top hne
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hq0).ne'
    ENNReal.ofReal_ne_top hmeas, ENNReal.toReal_ofReal hq0.le, one_div] at h
  exact (ENNReal.rpow_inv_le_iff hq0).mp h

/-- **Cauchy–Schwarz for `p`-th powers.** For measurable real functions `f`, `g` and `1 ≤ p`,
`∫⁻ ‖f‖ₑ^p ‖g‖ₑ^p ≤ (∫⁻ ‖f‖ₑ^{2p})^{1/2} (∫⁻ ‖g‖ₑ^{2p})^{1/2}`. -/
theorem lintegral_enorm_rpow_mul_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) {p : ℝ} (_hp : 1 ≤ p) :
    ∫⁻ x, ‖f x‖ₑ ^ p * ‖g x‖ₑ ^ p ∂μ
      ≤ (∫⁻ x, ‖f x‖ₑ ^ (2 * p) ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, ‖g x‖ₑ ^ (2 * p) ∂μ) ^ (1 / 2 : ℝ) := by
  have hF : Measurable fun x => ‖f x‖ₑ ^ p := (hf.enorm).pow_const p
  have hG : Measurable fun x => ‖g x‖ₑ ^ p := (hg.enorm).pow_const p
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun x => ‖f x‖ₑ ^ p) (g := fun x => ‖g x‖ₑ ^ p) hF.aemeasurable hG.aemeasurable
  have hF2 : ∀ x, (‖f x‖ₑ ^ p) ^ (2 : ℝ) = ‖f x‖ₑ ^ (2 * p) := fun x => by
    rw [← ENNReal.rpow_mul, mul_comm]
  have hG2 : ∀ x, (‖g x‖ₑ ^ p) ^ (2 : ℝ) = ‖g x‖ₑ ^ (2 * p) := fun x => by
    rw [← ENNReal.rpow_mul, mul_comm]
  simp only [Pi.mul_apply, hF2, hG2] at H
  exact H

end Riesz1

end
end
