/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Weighted Hölder inequality for lower Lebesgue integrals

For a measure `ν` on `Θ`, a nonnegative measurable `F` and a positive finite weight `w`, and
for `1 ≤ p`:

`(∫⁻ F dν)^p ≤ (∫⁻ w dν)^(p-1) * ∫⁻ F^p w^(1-p) dν`.

This is Hölder's inequality for the measure `w ν`, applied to the integrand `F / w`. It replaces
Minkowski's integral inequality, which Mathlib does not state for parameter integrals. The
Tonelli form `lintegral_rpow_le_weighted_lintegral` integrates this bound over a second variable
`x`, which is the form used for `L^p` norms of parameter integrals.

No constant depends on the size of the parameter space beyond the weight, which is the point of
the weight: the loop-arc cells use a weight that makes the bound uniform in `N`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- Hölder's inequality for a lower Lebesgue integral against a single measure:
`(∫⁻ G dρ)^p ≤ (ρ univ)^(p-1) * ∫⁻ G^p dρ` for `1 ≤ p` and measurable `G`. -/
theorem lintegral_rpow_le_measure_mul {Θ : Type*} [MeasurableSpace Θ] (ρ : Measure Θ)
    {G : Θ → ℝ≥0∞} (hG : Measurable G) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ θ, G θ ∂ρ) ^ p ≤ ρ Set.univ ^ (p - 1) * ∫⁻ θ, G θ ^ p ∂ρ := by
  rcases eq_or_lt_of_le hp with rfl | hp1
  · simp
  · have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp1
    have hinv : 1 / p.conjExponent = 1 - 1 / p := by
      have h := hpq.inv_add_inv_eq_one
      rw [one_div, one_div]
      linarith
    have hp0 : (0 : ℝ) < p := by linarith
    have H := ENNReal.lintegral_mul_le_Lp_mul_Lq ρ hpq (f := G) (g := fun _ => (1 : ℝ≥0∞))
      hG.aemeasurable aemeasurable_const
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at H
    calc (∫⁻ θ, G θ ∂ρ) ^ p
        ≤ ((∫⁻ θ, G θ ^ p ∂ρ) ^ (1 / p) * ρ Set.univ ^ (1 / p.conjExponent)) ^ p :=
          ENNReal.rpow_le_rpow H hp0.le
      _ = (∫⁻ θ, G θ ^ p ∂ρ) * ρ Set.univ ^ (p - 1) := by
          have e1 : 1 / p * p = 1 := by field_simp
          have e2 : 1 / p.conjExponent * p = p - 1 := by
            rw [hinv]
            field_simp
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
            e1, e2, ENNReal.rpow_one]
      _ = ρ Set.univ ^ (p - 1) * ∫⁻ θ, G θ ^ p ∂ρ := mul_comm _ _

/-- Weighted Hölder inequality. For a measurable `F ≥ 0` and a measurable weight `w` with
`0 < w < ∞` pointwise, `(∫⁻ F dν)^p ≤ (∫⁻ w dν)^(p-1) * ∫⁻ F^p w^(1-p) dν` for `1 ≤ p`. -/
theorem lintegral_rpow_le_weighted {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ)
    {F w : Θ → ℝ≥0∞} (hF : Measurable F) (hw : Measurable w) (hw0 : ∀ θ, w θ ≠ 0)
    (hwt : ∀ θ, w θ ≠ ∞) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ θ, F θ ∂ν) ^ p ≤ (∫⁻ θ, w θ ∂ν) ^ (p - 1) * ∫⁻ θ, F θ ^ p * w θ ^ (1 - p) ∂ν := by
  set ρ := ν.withDensity w with hρ
  have hG : Measurable (fun θ => F θ * (w θ)⁻¹) := hF.mul hw.inv
  have h1 : ∫⁻ θ, F θ * (w θ)⁻¹ ∂ρ = ∫⁻ θ, F θ ∂ν := by
    rw [hρ, lintegral_withDensity_eq_lintegral_mul ν hw hG]
    refine lintegral_congr fun θ => ?_
    simp only [Pi.mul_apply]
    rw [← mul_assoc, mul_comm (w θ), mul_assoc, ENNReal.mul_inv_cancel (hw0 θ) (hwt θ), mul_one]
  have h2 : ρ Set.univ = ∫⁻ θ, w θ ∂ν := by
    rw [hρ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h3 : ∫⁻ θ, (F θ * (w θ)⁻¹) ^ p ∂ρ = ∫⁻ θ, F θ ^ p * w θ ^ (1 - p) ∂ν := by
    have hGp : Measurable (fun θ => (F θ * (w θ)⁻¹) ^ p) := (hF.mul hw.inv).pow_const p
    rw [hρ, lintegral_withDensity_eq_lintegral_mul ν hw hGp]
    refine lintegral_congr fun θ => ?_
    simp only [Pi.mul_apply]
    have hp0 : (0 : ℝ) ≤ p := by linarith
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, ENNReal.inv_rpow,
      ENNReal.rpow_sub _ _ (hw0 θ) (hwt θ), ENNReal.rpow_one, ENNReal.div_eq_inv_mul]
    ring
  have key := lintegral_rpow_le_measure_mul ρ hG hp
  rw [h1, h2] at key
  rw [h3] at key
  exact key

/-- Tonelli form of the weighted Hölder inequality. For a jointly measurable `F`, the `L^p`
integral over `x` of the parameter integral `∫⁻ θ, F θ x ∂ν` is bounded by a weighted integral
over the parameter `θ` of the `L^p` moments of `F θ · `. -/
theorem lintegral_lintegral_rpow_le_weighted {Ω Θ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Θ] (μ : Measure Ω) (ν : Measure Θ) [SFinite μ] [SFinite ν]
    {F : Θ → Ω → ℝ≥0∞} (hF : Measurable (Function.uncurry F))
    {w : Θ → ℝ≥0∞} (hw : Measurable w) (hw0 : ∀ θ, w θ ≠ 0) (hwt : ∀ θ, w θ ≠ ∞)
    {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, (∫⁻ θ, F θ x ∂ν) ^ p ∂μ
      ≤ (∫⁻ θ, w θ ∂ν) ^ (p - 1) * ∫⁻ θ, (∫⁻ x, F θ x ^ p ∂μ) * w θ ^ (1 - p) ∂ν := by
  have hθ : ∀ x, Measurable (fun θ => F θ x) := fun x =>
    hF.comp (measurable_id.prodMk measurable_const)
  have hpt : ∀ x, (∫⁻ θ, F θ x ∂ν) ^ p
      ≤ (∫⁻ θ, w θ ∂ν) ^ (p - 1) * ∫⁻ θ, F θ x ^ p * w θ ^ (1 - p) ∂ν := fun x =>
    lintegral_rpow_le_weighted ν (hθ x) hw hw0 hwt hp
  have hpar : Measurable fun x => ∫⁻ θ, F θ x ^ p * w θ ^ (1 - p) ∂ν := by
    refine Measurable.lintegral_prod_right (f := fun x θ => F θ x ^ p * w θ ^ (1 - p)) ?_
    have hF' : Measurable (fun z : Ω × Θ => F z.2 z.1) := hF.comp measurable_swap
    exact (hF'.pow_const p).mul ((hw.comp measurable_snd).pow_const _)
  calc ∫⁻ x, (∫⁻ θ, F θ x ∂ν) ^ p ∂μ
      ≤ ∫⁻ x, (∫⁻ θ, w θ ∂ν) ^ (p - 1) * ∫⁻ θ, F θ x ^ p * w θ ^ (1 - p) ∂ν ∂μ :=
        lintegral_mono fun x => hpt x
    _ = (∫⁻ θ, w θ ∂ν) ^ (p - 1) * ∫⁻ x, ∫⁻ θ, F θ x ^ p * w θ ^ (1 - p) ∂ν ∂μ :=
        lintegral_const_mul _ hpar
    _ = (∫⁻ θ, w θ ∂ν) ^ (p - 1) * ∫⁻ θ, ∫⁻ x, F θ x ^ p * w θ ^ (1 - p) ∂μ ∂ν := by
        congr 1
        refine lintegral_lintegral_swap ?_
        have hF' : Measurable (fun z : Ω × Θ => F z.2 z.1) := hF.comp measurable_swap
        exact ((hF'.pow_const p).mul ((hw.comp measurable_snd).pow_const _)).aemeasurable
    _ = (∫⁻ θ, w θ ∂ν) ^ (p - 1) * ∫⁻ θ, (∫⁻ x, F θ x ^ p ∂μ) * w θ ^ (1 - p) ∂ν := by
        congr 1
        refine lintegral_congr fun θ => ?_
        have hx : Measurable (fun x => F θ x) :=
          hF.comp (measurable_const.prodMk measurable_id)
        rw [lintegral_mul_const _ ((hx.pow_const p))]

end Riesz1

end
end
