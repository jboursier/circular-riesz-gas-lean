/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian integrals for the Stein equation

For the standard Gaussian law `gaussianReal 0 1`, this file proves the absolute first moment
`E |Z| = √(2/π)`, the derivative in the mean of `t ↦ E h (t + c Z)` for a bounded continuous
`h`, and the rescaling `E f (σ Z)` to the law `gaussianReal 0 (σ ^ 2)`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal

namespace Riesz1

/-- The standard normal density, written with the explicit exponential. -/
lemma stein_gaussianPDFReal_std (u : ℝ) :
    gaussianPDFReal 0 1 u = (√(2 * π))⁻¹ * rexp (-u ^ 2 / 2) := by
  simp [gaussianPDFReal]

/-- The derivative of the standard normal density is `-u` times the density. -/
lemma stein_hasDerivAt_gaussianPDFReal_std (u : ℝ) :
    HasDerivAt (fun v => gaussianPDFReal 0 1 v) (-u * gaussianPDFReal 0 1 u) u := by
  have h1 : HasDerivAt (fun v : ℝ => -v ^ 2 / 2) (-u) u := by
    have := ((hasDerivAt_pow 2 u).neg).div_const 2
    convert this using 1
    norm_num
    ring
  have h2 := (h1.exp).const_mul (√(2 * π))⁻¹
  convert h2 using 1
  · ext v
    rw [stein_gaussianPDFReal_std]
  · rw [stein_gaussianPDFReal_std]
    ring

/-- Expectations under the standard Gaussian law as Lebesgue integrals against the density. -/
lemma stein_integral_std {f : ℝ → ℝ} :
    ∫ z, f z ∂(gaussianReal 0 1) = ∫ z, gaussianPDFReal 0 1 z * f z := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp [smul_eq_mul]

/-- The absolute value is integrable for the standard Gaussian law. -/
lemma stein_integrable_abs_std : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by simp)
  exact h.abs

/-- The integral of `|t| exp(-t²/2)` over the whole line equals `2`. -/
lemma stein_integral_abs_mul_exp :
    ∫ z : ℝ, |z| * rexp (-(z ^ 2 / 2)) = 2 := by
  have hcomp := integral_comp_abs (f := fun t : ℝ => t * rexp (-(t ^ 2 / 2)))
  have hsq : ∀ z : ℝ, |z| * rexp (-(|z| ^ 2 / 2)) = |z| * rexp (-(z ^ 2 / 2)) := by
    intro z
    rw [sq_abs]
  simp only [hsq] at hcomp
  rw [hcomp]
  have hint : IntegrableOn (fun t : ℝ => t * rexp (-(t ^ 2 / 2))) (Ioi 0) := by
    have h := integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    apply Integrable.integrableOn
    convert h using 2 with t
    ring_nf
  have hFTC : ∫ t in Ioi (0 : ℝ), t * rexp (-(t ^ 2 / 2)) = 1 := by
    have htend : Tendsto (fun t : ℝ => -rexp (-(t ^ 2 / 2))) atTop (𝓝 0) := by
      have h2 : Tendsto (fun t : ℝ => t ^ 2 / 2) atTop atTop :=
        (tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
      have h3 : Tendsto (fun t : ℝ => -(t ^ 2 / 2)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp h2
      simpa using (Real.tendsto_exp_atBot.comp h3).neg
    have := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t : ℝ => -rexp (-(t ^ 2 / 2)))
      (f' := fun t : ℝ => t * rexp (-(t ^ 2 / 2))) (a := 0)
      (by fun_prop)
      (fun t _ => by
        have h1 : HasDerivAt (fun t : ℝ => -(t ^ 2 / 2)) (-t) t := by
          have := ((hasDerivAt_pow 2 t).div_const 2).neg
          convert this using 1
          ring
        have h2 := (h1.exp).neg
        convert h2 using 1
        ring)
      hint htend
    simpa using this
  rw [hFTC]
  norm_num

/-- The first absolute moment of the standard Gaussian: `E |Z| = √(2/π)`. -/
lemma stein_integral_abs_std : ∫ z, |z| ∂(gaussianReal 0 1) = √(2 / π) := by
  rw [stein_integral_std]
  have hfun : (fun z : ℝ => gaussianPDFReal 0 1 z * |z|)
      = fun z => (√(2 * π))⁻¹ * (|z| * rexp (-(z ^ 2 / 2))) := by
    ext z
    rw [stein_gaussianPDFReal_std]
    ring_nf
  rw [hfun, integral_const_mul, stein_integral_abs_mul_exp]
  have hpos : (0 : ℝ) < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  have hsq : (2 / √(2 * π)) ^ 2 = 2 / π := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have hnn : 0 ≤ 2 / √(2 * π) := by positivity
  rw [← hsq, Real.sqrt_sq hnn]
  field_simp

/-- The bound `|h| ≤ C` makes `z ↦ z h(t + c z)` integrable against the standard Gaussian. -/
lemma stein_integrable_mul_id {h : ℝ → ℝ} (hcont : Continuous h) {C : ℝ}
    (hC : ∀ y, |h y| ≤ C) (t c : ℝ) :
    Integrable (fun z : ℝ => z * h (t + c * z)) (gaussianReal 0 1) := by
  refine Integrable.mono' (stein_integrable_abs_std.const_mul C) ?_ ?_
  · exact (continuous_id.mul (hcont.comp (continuous_const.add
      (continuous_const.mul continuous_id)))).aestronglyMeasurable
  · refine Eventually.of_forall (fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg z)

/-- The bound `|∫ z h(t + c z)| ≤ C √(2/π)` for `|h| ≤ C` and `E |Z| = √(2/π)`. -/
lemma stein_abs_integral_mul_id_le {h : ℝ → ℝ} {C : ℝ}
    (hC : ∀ y, |h y| ≤ C) (t c : ℝ) :
    |∫ z, z * h (t + c * z) ∂(gaussianReal 0 1)| ≤ C * √(2 / π) := by
  have hbound : ∀ z : ℝ, ‖z * h (t + c * z)‖ ≤ C * |z| := by
    intro z
    rw [Real.norm_eq_abs, abs_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg z)
  have key := norm_integral_le_of_norm_le (μ := gaussianReal 0 1)
    (f := fun z : ℝ => z * h (t + c * z)) (stein_integrable_abs_std.const_mul C)
    (Eventually.of_forall hbound)
  rw [integral_const_mul, stein_integral_abs_std, Real.norm_eq_abs] at key
  simpa using key

/-- The pointwise bound behind the dominated derivative in the mean: for `|δ| ≤ 1`,
`|y + δ| exp(-(y + δ)² / 2) ≤ 4 exp(1/2) exp(-y²/8)`. -/
lemma stein_abs_mul_gaussian_shift_le {y δ : ℝ} (hδ : |δ| ≤ 1) :
    |y + δ| * rexp (-(y + δ) ^ 2 / 2) ≤ 4 * rexp (1 / 2) * rexp (-(1 / 8) * y ^ 2) := by
  have hδ2 : δ ^ 2 ≤ 1 := by
    have := sq_abs δ
    nlinarith [abs_nonneg δ]
  have h1 : rexp (-(y + δ) ^ 2 / 2) ≤ rexp (1 / 2) * rexp (-(1 / 4) * y ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [sq_nonneg (y + 2 * δ)]
  have h2 : (|y| + 1) * rexp (-(1 / 4) * y ^ 2) ≤ 4 * rexp (-(1 / 8) * y ^ 2) := by
    have e1 : 1 + y ^ 2 / 8 ≤ rexp (y ^ 2 / 8) := by
      linarith [Real.add_one_le_exp (y ^ 2 / 8)]
    have e2 : |y| + 1 ≤ 4 * (1 + y ^ 2 / 8) := by
      nlinarith [sq_abs y, sq_nonneg (|y| - 1)]
    have e3 : rexp (y ^ 2 / 8) * rexp (-(1 / 4) * y ^ 2) = rexp (-(1 / 8) * y ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hexp : 0 ≤ rexp (-(1 / 4) * y ^ 2) := (Real.exp_pos _).le
    calc (|y| + 1) * rexp (-(1 / 4) * y ^ 2)
        ≤ (4 * (1 + y ^ 2 / 8)) * rexp (-(1 / 4) * y ^ 2) :=
          mul_le_mul_of_nonneg_right e2 hexp
      _ ≤ (4 * rexp (y ^ 2 / 8)) * rexp (-(1 / 4) * y ^ 2) := by gcongr
      _ = 4 * rexp (-(1 / 8) * y ^ 2) := by rw [mul_assoc, e3]
  have habs : |y + δ| ≤ |y| + 1 := by
    calc |y + δ| ≤ |y| + |δ| := abs_add_le _ _
      _ ≤ |y| + 1 := by linarith
  have hnn : 0 ≤ rexp (-(y + δ) ^ 2 / 2) := (Real.exp_pos _).le
  calc |y + δ| * rexp (-(y + δ) ^ 2 / 2)
      ≤ (|y| + 1) * (rexp (1 / 2) * rexp (-(1 / 4) * y ^ 2)) :=
        mul_le_mul habs h1 hnn (by positivity)
    _ = rexp (1 / 2) * ((|y| + 1) * rexp (-(1 / 4) * y ^ 2)) := by ring
    _ ≤ rexp (1 / 2) * (4 * rexp (-(1 / 8) * y ^ 2)) := by gcongr
    _ = 4 * rexp (1 / 2) * rexp (-(1 / 8) * y ^ 2) := by ring

/-- Rescaling: the Gaussian law of variance `σ²` is the image of the standard one under `z ↦ σ z`. -/
lemma stein_integral_gaussian_scale (σ : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ y, f y ∂(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) = ∫ z, f (σ * z) ∂(gaussianReal 0 1) := by
  have hmap : (gaussianReal 0 1).map (fun z : ℝ => σ * z) = gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    rfl
  rw [← hmap, integral_map (measurable_const_mul σ).aemeasurable hf.aestronglyMeasurable]

/-- Derivative in the mean of a Gaussian average.

For a bounded continuous `h` and `c > 0`, the map `t ↦ E h (t + c Z)` is differentiable with
derivative `c⁻¹ E [Z h (t + c Z)]`. -/
lemma stein_hasDerivAt_gaussian_mean {h : ℝ → ℝ} (hcont : Continuous h) {C : ℝ}
    (hC : ∀ y, |h y| ≤ C) {c : ℝ} (hc : 0 < c) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ z, h (t + c * z) ∂(gaussianReal 0 1))
      ((1 / c) * ∫ z, z * h (t₀ + c * z) ∂(gaussianReal 0 1)) t₀ := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  -- Step 1: substitute `w = z + t / c`, so that the mean moves into the Gaussian density.
  have hrep : ∀ t : ℝ, ∫ z, h (t + c * z) ∂(gaussianReal 0 1)
      = ∫ w, h (c * w) * gaussianPDFReal 0 1 (w - t / c) := by
    intro t
    rw [stein_integral_std]
    have hsub : ∫ w, gaussianPDFReal 0 1 (w - t / c) * h (t + c * (w - t / c))
        = ∫ z, gaussianPDFReal 0 1 z * h (t + c * z) :=
      integral_sub_right_eq_self (μ := volume) (fun z => gaussianPDFReal 0 1 z * h (t + c * z))
        (t / c)
    rw [← hsub]
    have hpt : ∀ w : ℝ, gaussianPDFReal 0 1 (w - t / c) * h (t + c * (w - t / c))
        = h (c * w) * gaussianPDFReal 0 1 (w - t / c) := by
      intro w
      rw [show t + c * (w - t / c) = c * w by field_simp; ring, mul_comm]
    simp only [hpt]
  -- Step 2: the bound on the derivative of the integrand, uniform for `t` near `t₀`.
  set K : ℝ := C * (√(2 * π))⁻¹ / c * (4 * rexp (1 / 2)) with hK
  have hpdf : ∀ u : ℝ, gaussianPDFReal 0 1 u = (√(2 * π))⁻¹ * rexp (-u ^ 2 / 2) :=
    stein_gaussianPDFReal_std
  have hbound_pt : ∀ w : ℝ, ∀ t ∈ Metric.ball t₀ c,
      ‖h (c * w) * ((w - t / c) / c * gaussianPDFReal 0 1 (w - t / c))‖
        ≤ K * rexp (-(1 / 8) * (w - t₀ / c) ^ 2) := by
    intro w t ht
    have hδ : |t₀ / c - t / c| ≤ 1 := by
      rw [show t₀ / c - t / c = -(t - t₀) / c by ring, abs_div, abs_neg, abs_of_pos hc,
        div_le_one hc]
      have := Metric.mem_ball.1 ht
      rw [Real.dist_eq] at this
      linarith [abs_sub_comm t t₀]
    have hsplit : w - t / c = (w - t₀ / c) + (t₀ / c - t / c) := by ring
    have hpdf_nn : 0 ≤ gaussianPDFReal 0 1 (w - t / c) := gaussianPDFReal_nonneg _ _ _
    have hkey := stein_abs_mul_gaussian_shift_le (y := w - t₀ / c) hδ
    rw [← hsplit] at hkey
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_of_pos hc, abs_of_nonneg hpdf_nn, hpdf]
    have hh : |h (c * w)| ≤ C := hC _
    calc |h (c * w)| * (|w - t / c| / c * ((√(2 * π))⁻¹ * rexp (-(w - t / c) ^ 2 / 2)))
        = (|h (c * w)| * (√(2 * π))⁻¹ / c) * (|w - t / c| * rexp (-(w - t / c) ^ 2 / 2)) := by
          ring
      _ ≤ (C * (√(2 * π))⁻¹ / c) * (4 * rexp (1 / 2) * rexp (-(1 / 8) * (w - t₀ / c) ^ 2)) := by
          gcongr
      _ = K * rexp (-(1 / 8) * (w - t₀ / c) ^ 2) := by
          rw [hK]
          ring
  -- Step 3: the derivative of each integrand in `t`.
  have hF : ∀ w t : ℝ, HasDerivAt (fun t : ℝ => h (c * w) * gaussianPDFReal 0 1 (w - t / c))
      (h (c * w) * ((w - t / c) / c * gaussianPDFReal 0 1 (w - t / c))) t := by
    intro w t
    have hu : HasDerivAt (fun t : ℝ => w - t / c) (-(1 / c)) t := by
      have := ((hasDerivAt_id t).div_const c).const_sub w
      simpa using this
    have := ((stein_hasDerivAt_gaussianPDFReal_std (w - t / c)).comp t hu).const_mul (h (c * w))
    exact this.congr_deriv (by ring)
  -- Step 4: differentiate under the integral sign, with the uniform bound `hbound_pt`.
  have hmeasF : ∀ t : ℝ, Measurable (fun w : ℝ => h (c * w) * gaussianPDFReal 0 1 (w - t / c)) :=
    fun t => (hcont.comp (continuous_const.mul continuous_id)).measurable.mul
      ((measurable_gaussianPDFReal 0 1).comp (measurable_id.sub_const (t / c)))
  have hint : ∀ t : ℝ, Integrable (fun w : ℝ => h (c * w) * gaussianPDFReal 0 1 (w - t / c)) := by
    intro t
    refine Integrable.bdd_mul (c := C) ((integrable_gaussianPDFReal 0 1).comp_sub_right (t / c))
      (hcont.comp (continuous_const.mul continuous_id)).aestronglyMeasurable ?_
    exact Eventually.of_forall (fun w => by rw [Real.norm_eq_abs]; exact hC _)
  have hmain : HasDerivAt (fun t : ℝ => ∫ w, h (c * w) * gaussianPDFReal 0 1 (w - t / c))
      (∫ w, h (c * w) * ((w - t₀ / c) / c * gaussianPDFReal 0 1 (w - t₀ / c))) t₀ := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun t w => h (c * w) * gaussianPDFReal 0 1 (w - t / c))
      (F' := fun t w => h (c * w) * ((w - t / c) / c * gaussianPDFReal 0 1 (w - t / c)))
      (bound := fun w => K * rexp (-(1 / 8) * (w - t₀ / c) ^ 2))
      (s := Metric.ball t₀ c) (x₀ := t₀) (Metric.ball_mem_nhds t₀ hc)
      (Eventually.of_forall fun t => (hmeasF t).aestronglyMeasurable) (hint t₀) ?_
      ?_ ?_ ?_).2
    · exact (((hcont.comp (continuous_const.mul continuous_id)).measurable.mul
        (((measurable_id.sub_const _).div_const c).mul
          ((measurable_gaussianPDFReal 0 1).comp (measurable_id.sub_const _))))).aestronglyMeasurable
    · exact Eventually.of_forall (fun w t ht => hbound_pt w t ht)
    · exact ((integrable_exp_neg_mul_sq (b := 1 / 8) (by norm_num)).comp_sub_right (t₀ / c)).const_mul K
    · exact Eventually.of_forall (fun w t _ => hF w t)
  -- Step 5: identify the integral with the Gaussian expectation `c⁻¹ E [Z h (t₀ + c Z)]`.
  have e1 : ∫ w, h (c * w) * ((w - t₀ / c) / c * gaussianPDFReal 0 1 (w - t₀ / c))
      = ∫ x, h (t₀ + c * x) * (x / c * gaussianPDFReal 0 1 x) := by
    calc ∫ w, h (c * w) * ((w - t₀ / c) / c * gaussianPDFReal 0 1 (w - t₀ / c))
        = ∫ x, h (c * (x + t₀ / c)) * (((x + t₀ / c) - t₀ / c) / c
            * gaussianPDFReal 0 1 ((x + t₀ / c) - t₀ / c)) :=
          (integral_add_right_eq_self (μ := volume)
            (fun w => h (c * w) * ((w - t₀ / c) / c * gaussianPDFReal 0 1 (w - t₀ / c)))
            (t₀ / c)).symm
      _ = ∫ x, h (t₀ + c * x) * (x / c * gaussianPDFReal 0 1 x) := by
          congr 1
          ext x
          rw [show c * (x + t₀ / c) = t₀ + c * x by field_simp; ring,
            show x + t₀ / c - t₀ / c = x by ring]
  have e2 : (1 / c) * ∫ z, z * h (t₀ + c * z) ∂(gaussianReal 0 1)
      = ∫ x, h (t₀ + c * x) * (x / c * gaussianPDFReal 0 1 x) := by
    rw [stein_integral_std, ← integral_const_mul]
    congr 1
    ext x
    ring
  have hfun : (fun t : ℝ => ∫ z, h (t + c * z) ∂(gaussianReal 0 1))
      = fun t : ℝ => ∫ w, h (c * w) * gaussianPDFReal 0 1 (w - t / c) :=
    funext hrep
  rw [hfun]
  exact hmain.congr_deriv (e1.trans e2.symm)

end Riesz1
