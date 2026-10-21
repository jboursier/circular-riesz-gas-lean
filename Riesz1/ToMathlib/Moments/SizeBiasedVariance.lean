/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Variance under a size-biased probability measure

For a probability measure `μ` and a nonnegative integrable weight `w` with `∫ w dμ = 1`, the measure
`w μ = μ.withDensity (ofReal ∘ w)` is again a probability measure. Its variance for a bounded
function `T` is controlled by the variance under `μ` and by the weighted tail of `w` above a
threshold `κ`:

`Var_{w μ}(T) ≤ κ Var_μ(T) + 4 M² E_μ[w 1_{w > κ}]`, when `|T| ≤ M` and `κ > 0`.

This is the size-biasing step of Lemma 5.2, variance claim, with
`κ = K^ε`, `T` a bounded anchored function and `μ` the anchored law.

* `isProbabilityMeasure_withDensity_ofReal`: `w μ` is a probability measure.
* `integral_withDensity_ofReal`: `∫ g d(w μ) = ∫ w g dμ`.
* `variance_sizeBiased_le`: the variance inequality.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace Riesz1

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The size-biased measure `w μ` is a probability measure when `w ≥ 0` is integrable with
`∫ w dμ = 1`. -/
theorem isProbabilityMeasure_withDensity_ofReal (μ : Measure Ω) [IsProbabilityMeasure μ]
    {w : Ω → ℝ} (hwint : Integrable w μ) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (w x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hwint (Filter.Eventually.of_forall hw0), hw1,
    ENNReal.ofReal_one]

/-- Integration against the size-biased measure: `∫ g d(w μ) = ∫ w g dμ` for a measurable
nonnegative weight `w`. -/
theorem integral_withDensity_ofReal (μ : Measure Ω) {w : Ω → ℝ} (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (g : Ω → ℝ) :
    ∫ x, g x ∂(μ.withDensity fun x => ENNReal.ofReal (w x)) = ∫ x, w x * g x ∂μ := by
  have hf : Measurable fun x => ENNReal.ofReal (w x) := ENNReal.measurable_ofReal.comp hw
  rw [integral_withDensity_eq_integral_toReal_smul hf
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) g]
  simp [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul]

/-- **Variance under a size-biased measure.** Let `μ` be a probability measure, and let
`w ≥ 0` be a measurable integrable function with `∫ w dμ = 1`. Let `T` be measurable with
`|T| ≤ M` everywhere, and let `κ > 0`. Then the variance of `T` under `w μ` satisfies
`Var_{wμ}(T) ≤ κ Var_μ(T) + 4 M² ∫_{w > κ} w dμ`. -/
theorem variance_sizeBiased_le (μ : Measure Ω) [IsProbabilityMeasure μ] {w T : Ω → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hwint : Integrable w μ)
    (hw1 : ∫ x, w x ∂μ = 1) (hT : Measurable T) {M : ℝ} (hTM : ∀ x, |T x| ≤ M) {κ : ℝ}
    (hκ : 0 < κ) :
    variance T (μ.withDensity fun x => ENNReal.ofReal (w x)) ≤
      κ * variance T μ + 4 * M ^ 2 * ∫ x in {x | κ < w x}, w x ∂μ := by
  have : IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (w x)) :=
    isProbabilityMeasure_withDensity_ofReal μ hwint hw0 hw1
  -- The centre `c` is the mean under `μ`. It satisfies `|c| ≤ M`.
  set c : ℝ := ∫ x, T x ∂μ with hc
  have hcM : |c| ≤ M := by
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := T) (C := M)
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hTM x)
    simpa [hc, Real.norm_eq_abs] using h
  -- The squared deviation `(T - c)²` is bounded by `4 M²`.
  have hsq : ∀ x, (T x - c) ^ 2 ≤ 4 * M ^ 2 := by
    intro x
    have h1 : |T x - c| ≤ 2 * M := by
      calc |T x - c| ≤ |T x| + |c| := abs_sub _ _
        _ ≤ M + M := add_le_add (hTM x) hcM
        _ = 2 * M := by ring
    calc (T x - c) ^ 2 = |T x - c| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * M) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = 4 * M ^ 2 := by ring
  -- Step 1: the variance under `w μ` is at most the second moment about `c`.
  have hstep1 : variance T (μ.withDensity fun x => ENNReal.ofReal (w x)) ≤
      ∫ x, w x * (T x - c) ^ 2 ∂μ := by
    have h := variance_le_expectation_sq (μ := μ.withDensity fun x => ENNReal.ofReal (w x))
      (X := fun x => T x - c) (hT.sub_const c).aestronglyMeasurable
    rw [variance_sub_const hT.aestronglyMeasurable c] at h
    have hdens : ∫ x, (T x - c) ^ 2 ∂(μ.withDensity fun x => ENNReal.ofReal (w x)) =
        ∫ x, w x * (T x - c) ^ 2 ∂μ :=
      integral_withDensity_ofReal μ hw hw0 (fun x => (T x - c) ^ 2)
    rw [← hdens]
    simpa [Pi.pow_apply] using h
  -- Step 2: a pointwise bound, splitting at `w = κ`.
  have hpt : ∀ x, w x * (T x - c) ^ 2 ≤
      κ * (T x - c) ^ 2 + 4 * M ^ 2 * ({x | κ < w x}.indicator w x) := by
    intro x
    by_cases hx : κ < w x
    · rw [indicator_of_mem (show x ∈ {x | κ < w x} from hx)]
      have h1 : w x * (T x - c) ^ 2 ≤ w x * (4 * M ^ 2) :=
        mul_le_mul_of_nonneg_left (hsq x) (hw0 x)
      have h2 : 0 ≤ κ * (T x - c) ^ 2 := mul_nonneg hκ.le (sq_nonneg _)
      nlinarith
    · rw [indicator_of_notMem (show x ∉ {x | κ < w x} from hx)]
      have h1 : w x ≤ κ := not_lt.1 hx
      have h2 : w x * (T x - c) ^ 2 ≤ κ * (T x - c) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      linarith
  have hmeas_set : MeasurableSet {x | κ < w x} := measurableSet_lt measurable_const hw
  have hsqInt : Integrable (fun x => (T x - c) ^ 2) μ :=
    Integrable.of_bound ((hT.sub_const c).pow_const 2).aestronglyMeasurable (4 * M ^ 2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hsq x)
  have hind : Integrable ({x | κ < w x}.indicator w) μ := hwint.indicator hmeas_set
  have hint1 : Integrable (fun x => w x * (T x - c) ^ 2) μ := by
    refine Integrable.mono' (hwint.const_mul (4 * M ^ 2)) ?_ ?_
    · exact (hw.mul ((hT.sub_const c).pow_const 2)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 x) (sq_nonneg _))]
      calc w x * (T x - c) ^ 2 ≤ w x * (4 * M ^ 2) :=
            mul_le_mul_of_nonneg_left (hsq x) (hw0 x)
        _ = 4 * M ^ 2 * w x := by ring
  have hint2 : Integrable
      (fun x => κ * (T x - c) ^ 2 + 4 * M ^ 2 * ({x | κ < w x}.indicator w x)) μ :=
    (hsqInt.const_mul κ).add (hind.const_mul (4 * M ^ 2))
  have hstep2 : ∫ x, w x * (T x - c) ^ 2 ∂μ ≤
      κ * ∫ x, (T x - c) ^ 2 ∂μ + 4 * M ^ 2 * ∫ x, {x | κ < w x}.indicator w x ∂μ := by
    calc ∫ x, w x * (T x - c) ^ 2 ∂μ
        ≤ ∫ x, (κ * (T x - c) ^ 2 + 4 * M ^ 2 * ({x | κ < w x}.indicator w x)) ∂μ :=
          integral_mono hint1 hint2 hpt
      _ = κ * ∫ x, (T x - c) ^ 2 ∂μ + 4 * M ^ 2 * ∫ x, {x | κ < w x}.indicator w x ∂μ := by
          rw [integral_add (hsqInt.const_mul κ) (hind.const_mul _), integral_const_mul,
            integral_const_mul]
  -- Step 3: identify the two integrals with `Var_μ T` and the weighted tail.
  have hvar : variance T μ = ∫ x, (T x - c) ^ 2 ∂μ := variance_eq_integral hT.aemeasurable
  calc variance T (μ.withDensity fun x => ENNReal.ofReal (w x))
      ≤ ∫ x, w x * (T x - c) ^ 2 ∂μ := hstep1
    _ ≤ κ * ∫ x, (T x - c) ^ 2 ∂μ + 4 * M ^ 2 * ∫ x, {x | κ < w x}.indicator w x ∂μ := hstep2
    _ = κ * variance T μ + 4 * M ^ 2 * ∫ x in {x | κ < w x}, w x ∂μ := by
        rw [hvar, integral_indicator hmeas_set]

end Riesz1

end
