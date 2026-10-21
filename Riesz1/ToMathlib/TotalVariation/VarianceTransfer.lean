/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ForcingComparison
public import Riesz1.ToMathlib.TotalVariation.Event
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Integrals and variances under two probability measures at total-variation distance `δ`

For probability measures `μ ν` on a measurable space and a bounded measurable function `f` with
`|f| ≤ B`, the integrals differ by at most `2 B δ`, where `δ = totalVariation μ ν`
(`abs_integral_sub_le_of_abs_le`). Applied to `f = T²` and `f = T`, this gives the variance transfer
`|Var_μ T - Var_ν T| ≤ 6 B² δ` (`abs_variance_sub_le_of_abs_le`), which is the general step of
Lemma 5.2, variance claim.

The layer-cake formula writes `∫ f dμ` as an integral of the event probabilities `μ {t ≤ f}` over
`(0, 2B]`. Each event probability differs from its `ν` counterpart by at most `δ`, and the interval
has length `2B`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace Riesz1

/-- The total variation distance is nonnegative. -/
lemma totalVariation_nonneg {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) :
    0 ≤ totalVariation μ ν :=
  div_nonneg ENNReal.toReal_nonneg (by norm_num)

/-- The discrepancy of two probability measures on one event is at most their total variation. -/
lemma abs_measureReal_sub_le_totalVariation {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {A : Set Ω} (hA : MeasurableSet A) :
    |μ.real A - ν.real A| ≤ totalVariation μ ν :=
  abs_measureReal_sub_le_etvDist_div_two μ ν hA

/-- The integrals of a bounded measurable function under two probability measures differ by at most
`2 B` times their total variation. -/
theorem abs_integral_sub_le_of_abs_le {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : Ω → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : 0 ≤ B) (hfB : ∀ ω, |f ω| ≤ B) :
    |∫ ω, f ω ∂μ - ∫ ω, f ω ∂ν| ≤ 2 * B * totalVariation μ ν := by
  -- Shift `f` to the nonnegative function `g = f + B`, which takes values in `[0, 2B]`.
  set g : Ω → ℝ := fun ω => f ω + B with hgdef
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => by
    have := neg_abs_le (f ω)
    have := hfB ω
    simp only [hgdef]
    linarith
  have hg2 : ∀ ω, g ω ≤ 2 * B := fun ω => by
    have := le_abs_self (f ω)
    have := hfB ω
    simp only [hgdef]
    linarith
  have hgm : Measurable g := hf.add_const B
  have hbdd : ∀ ρ : Measure Ω, [IsProbabilityMeasure ρ] → Integrable f ρ := fun ρ _ =>
    Integrable.mono' (integrable_const B) hf.aestronglyMeasurable
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hfB ω)
  -- `∫ g = ∫ f + B` under a probability measure.
  have hshift : ∀ ρ : Measure Ω, [IsProbabilityMeasure ρ] → ∫ ω, g ω ∂ρ = ∫ ω, f ω ∂ρ + B :=
    fun ρ _ => by
      simp only [hgdef]
      rw [integral_add (hbdd ρ) (integrable_const B), integral_const]
      simp
  -- The layer-cake formula for `g` on `(0, 2B]`.
  have hgint : ∀ ρ : Measure Ω, [IsProbabilityMeasure ρ] → Integrable g ρ := fun ρ _ =>
    Integrable.mono' (integrable_const (2 * B)) hgm.aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 ω)]
        exact hg2 ω)
  have hlc : ∀ ρ : Measure Ω, [IsProbabilityMeasure ρ] →
      ∫ ω, g ω ∂ρ = ∫ t in Ioc 0 (2 * B), ρ.real {a | t ≤ g a} := fun ρ _ =>
    Integrable.integral_eq_integral_Ioc_meas_le (hgint ρ) (ae_of_all _ hg0) (ae_of_all _ hg2)
  -- Each event probability is antitone in the level, hence measurable, and bounded by one.
  have hanti : ∀ ρ : Measure Ω, [IsProbabilityMeasure ρ] →
      Antitone (fun t : ℝ => ρ.real {a | t ≤ g a}) := fun ρ _ s t hst =>
    measureReal_mono (fun a ha => le_trans hst ha) (measure_ne_top ρ _)
  have hint : ∀ ρ : Measure Ω, [IsProbabilityMeasure ρ] →
      IntegrableOn (fun t : ℝ => ρ.real {a | t ≤ g a}) (Ioc 0 (2 * B)) := fun ρ _ =>
    Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne (hanti ρ).measurable.aestronglyMeasurable
      (M := 1) (ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg)]
        exact measureReal_le_one)
  have hdiff : ∫ ω, f ω ∂μ - ∫ ω, f ω ∂ν =
      ∫ t in Ioc 0 (2 * B), (μ.real {a | t ≤ g a} - ν.real {a | t ≤ g a}) := by
    rw [integral_sub (hint μ) (hint ν)]
    have h1 := hshift μ
    have h2 := hshift ν
    rw [hlc μ] at h1
    rw [hlc ν] at h2
    linarith
  have hbound : ‖∫ t in Ioc 0 (2 * B), (μ.real {a | t ≤ g a} - ν.real {a | t ≤ g a})‖ ≤
      totalVariation μ ν * volume.real (Ioc 0 (2 * B)) := by
    apply norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top
    intro t _
    rw [Real.norm_eq_abs]
    exact abs_measureReal_sub_le_totalVariation μ ν (measurableSet_le measurable_const hgm)
  rw [hdiff, ← Real.norm_eq_abs]
  have hvol : volume.real (Ioc 0 (2 * B)) = 2 * B := by
    rw [Real.volume_real_Ioc_of_le (by linarith)]
    ring
  rw [hvol] at hbound
  linarith [hbound]

/-- **Variance transfer.** For a bounded measurable `T` with `|T| ≤ B`, the variances of `T` under two
probability measures differ by at most `6 B²` times their total variation. -/
theorem abs_variance_sub_le_of_abs_le {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {T : Ω → ℝ} (hT : Measurable T) {B : ℝ}
    (hB : 0 ≤ B) (hTB : ∀ ω, |T ω| ≤ B) :
    |variance T μ - variance T ν| ≤ 6 * B ^ 2 * totalVariation μ ν := by
  have hmemμ : MemLp T 2 μ :=
    MemLp.of_bound hT.aestronglyMeasurable B (ae_of_all _ fun ω => by
      simpa [Real.norm_eq_abs] using hTB ω)
  have hmemν : MemLp T 2 ν :=
    MemLp.of_bound hT.aestronglyMeasurable B (ae_of_all _ fun ω => by
      simpa [Real.norm_eq_abs] using hTB ω)
  rw [variance_eq_sub hmemμ, variance_eq_sub hmemν]
  simp only [Pi.pow_apply]
  have hsq : ∀ ω, |T ω ^ 2| ≤ B ^ 2 := fun ω => by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg (T ω), sq_abs (T ω), hTB ω]
  have h1 : |∫ ω, T ω ^ 2 ∂μ - ∫ ω, T ω ^ 2 ∂ν| ≤ 2 * B ^ 2 * totalVariation μ ν :=
    abs_integral_sub_le_of_abs_le μ ν (hT.pow_const 2) (by positivity) hsq
  have h2 : |∫ ω, T ω ∂μ - ∫ ω, T ω ∂ν| ≤ 2 * B * totalVariation μ ν :=
    abs_integral_sub_le_of_abs_le μ ν hT hB hTB
  have hmean : ∀ ρ : Measure Ω, [IsProbabilityMeasure ρ] → |∫ ω, T ω ∂ρ| ≤ B := fun ρ _ => by
    have h := norm_integral_le_of_norm_le_const (μ := ρ) (f := T) (C := B)
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hTB ω)
    simpa [Real.norm_eq_abs] using h
  have hsum : |∫ ω, T ω ∂μ + ∫ ω, T ω ∂ν| ≤ 2 * B :=
    (abs_add_le _ _).trans (by linarith [hmean μ, hmean ν])
  have key : (∫ ω, T ω ^ 2 ∂μ) - (∫ ω, T ω ∂μ) ^ 2 - ((∫ ω, T ω ^ 2 ∂ν) - (∫ ω, T ω ∂ν) ^ 2) =
      ((∫ ω, T ω ^ 2 ∂μ) - ∫ ω, T ω ^ 2 ∂ν) -
        (∫ ω, T ω ∂μ - ∫ ω, T ω ∂ν) * (∫ ω, T ω ∂μ + ∫ ω, T ω ∂ν) := by
    ring
  rw [key]
  calc |((∫ ω, T ω ^ 2 ∂μ) - ∫ ω, T ω ^ 2 ∂ν) -
        (∫ ω, T ω ∂μ - ∫ ω, T ω ∂ν) * (∫ ω, T ω ∂μ + ∫ ω, T ω ∂ν)|
      ≤ |(∫ ω, T ω ^ 2 ∂μ) - ∫ ω, T ω ^ 2 ∂ν| +
          |(∫ ω, T ω ∂μ - ∫ ω, T ω ∂ν) * (∫ ω, T ω ∂μ + ∫ ω, T ω ∂ν)| := abs_sub _ _
    _ = |(∫ ω, T ω ^ 2 ∂μ) - ∫ ω, T ω ^ 2 ∂ν| +
          |∫ ω, T ω ∂μ - ∫ ω, T ω ∂ν| * |∫ ω, T ω ∂μ + ∫ ω, T ω ∂ν| := by rw [abs_mul]
    _ ≤ 2 * B ^ 2 * totalVariation μ ν + (2 * B * totalVariation μ ν) * (2 * B) :=
        add_le_add h1 (mul_le_mul h2 hsum (abs_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) hB) (totalVariation_nonneg μ ν)))
    _ = 6 * B ^ 2 * totalVariation μ ν := by ring

end Riesz1

end
