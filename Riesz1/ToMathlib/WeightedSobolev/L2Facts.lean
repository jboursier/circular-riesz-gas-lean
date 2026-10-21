/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# L² facts for integrals against a measure

These are the measure-theoretic estimates used to pass Brascamp–Lieb inequalities to limits in
`L²`: the squared norm of a difference as a real integral, the Cauchy–Schwarz bound for real
functions, the identity `Var F = ∫ F² - (∫ F)²` for probability measures, and continuity of the
variance along `L²`-convergent sequences.
-/

public section

noncomputable section

open MeasureTheory Filter Topology

namespace Riesz1.WeightedSobolev

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The squared enorm of a real number is the nonnegative extended real square. -/
theorem enorm_sq_eq_ofReal_sq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

/-- The squared enorm of a vector is the nonnegative extended real square of its norm. -/
theorem enorm_sq_eq_ofReal_norm_sq {E : Type*} [NormedAddCommGroup E] (v : E) :
    ‖v‖ₑ ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg v)]

/-- The real square integral of an almost everywhere strongly measurable real function is the
real part of its extended-real `L²` integral. -/
theorem integral_sq_eq_toReal_lintegral {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) :
    ∫ x, f x ^ 2 ∂μ = ENNReal.toReal (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg (f x))
    (hf.pow 2)]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [enorm_sq_eq_ofReal_sq]

/-- The real square integral of an almost everywhere strongly measurable vector function is the
real part of its extended-real `L²` integral. -/
theorem integral_norm_sq_eq_toReal_lintegral {E : Type*} [NormedAddCommGroup E]
    {f : Ω → E} (hf : AEStronglyMeasurable f μ) :
    ∫ x, ‖f x‖ ^ 2 ∂μ = ENNReal.toReal (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg (‖f x‖))
    (hf.norm.pow 2)]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [enorm_sq_eq_ofReal_norm_sq]

/-- Convergence of the extended-real squared distances gives convergence of the real squared
distances, for real or vector valued functions. -/
theorem tendsto_integral_norm_sq_of_lintegral {E : Type*} [NormedAddCommGroup E]
    {f : ℕ → Ω → E} (hf : ∀ k, AEStronglyMeasurable (f k) μ)
    (h : Tendsto (fun k => ∫⁻ x, ‖f k x‖ₑ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖f k x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simp only [ENNReal.toReal_zero] at h'
  refine h'.congr fun k => ?_
  simp only [Function.comp_apply]
  rw [integral_norm_sq_eq_toReal_lintegral (hf k)]

/-- Convergence of the extended-real squared distances of real functions gives convergence of the
real squared distances. -/
theorem tendsto_integral_sq_of_lintegral {f : ℕ → Ω → ℝ} (hf : ∀ k, AEStronglyMeasurable (f k) μ)
    (h : Tendsto (fun k => ∫⁻ x, ‖f k x‖ₑ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, f k x ^ 2 ∂μ) atTop (𝓝 0) := by
  have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simp only [ENNReal.toReal_zero] at h'
  refine h'.congr fun k => ?_
  simp only [Function.comp_apply]
  rw [integral_sq_eq_toReal_lintegral (hf k)]

/-- Cauchy–Schwarz for real functions in `L²(μ)`, in the form of an absolute value bound. -/
theorem abs_integral_mul_le_sqrt {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    Real.HolderConjugate.two_two
    (f := fun x => |f x|) (g := fun x => |g x|)
    (Eventually.of_forall fun x => abs_nonneg _) (Eventually.of_forall fun x => abs_nonneg _)
    (by simpa only [ENNReal.ofReal_ofNat, Real.norm_eq_abs] using hf.norm)
    (by simpa only [ENNReal.ofReal_ofNat, Real.norm_eq_abs] using hg.norm)
  have hrpow : ∀ x : ℝ, |x| ^ (2 : ℝ) = x ^ 2 := fun x => by
    rw [Real.rpow_two, sq_abs]
  simp only [hrpow] at hHolder
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hHolder
  calc |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x| * |g x| ∂μ := by
        refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
        exact integral_congr_ae (Eventually.of_forall fun x => by simp [abs_mul])
    _ ≤ _ := hHolder

/-- Under a probability measure, the variance of an `L²` function is the difference of its second
moment and the square of its mean. -/
theorem integral_sub_mean_sq [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : MemLp F 2 μ) :
    ∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ = ∫ x, F x ^ 2 ∂μ - (∫ x, F x ∂μ) ^ 2 := by
  rw [← ProbabilityTheory.variance_eq_integral hF.aemeasurable, ProbabilityTheory.variance_eq_sub hF]
  rfl

/-- Convergence of the centred second moments under a probability measure, when the functions
converge in `L²(μ)` to a limit `F`. -/
theorem tendsto_integral_sub_mean_sq [IsProbabilityMeasure μ] {F : Ω → ℝ} {φ : ℕ → Ω → ℝ}
    (hF : MemLp F 2 μ) (hφ : ∀ k, MemLp (φ k) 2 μ)
    (hd : Tendsto (fun k => ∫ x, (φ k x - F x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, (φ k x - ∫ y, φ k y ∂μ) ^ 2 ∂μ) atTop
      (𝓝 (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ)) := by
  have hsqrt : Tendsto (fun k => Real.sqrt (∫ x, (φ k x - F x) ^ 2 ∂μ)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hd
    rw [Real.sqrt_zero] at h
    exact h
  -- The mean converges, by Cauchy–Schwarz against the constant function `1`.
  have hmean : Tendsto (fun k => ∫ x, φ k x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
    have hbound (k : ℕ) : |∫ x, φ k x ∂μ - ∫ x, F x ∂μ| ≤
        Real.sqrt (∫ x, (φ k x - F x) ^ 2 ∂μ) := by
      have hsub : MemLp (fun x => φ k x - F x) 2 μ := (hφ k).sub hF
      have hcs := abs_integral_mul_le_sqrt hsub (memLp_const (1 : ℝ))
      have hone : ∫ x, (1 : ℝ) ^ 2 ∂μ = 1 := by simp
      have hint : ∫ x, (φ k x - F x) * (1 : ℝ) ∂μ = ∫ x, φ k x ∂μ - ∫ x, F x ∂μ := by
        rw [← integral_sub ((hφ k).integrable one_le_two) (hF.integrable one_le_two)]
        simp
      rw [hint, hone, Real.sqrt_one, mul_one] at hcs
      exact hcs
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun k => norm_nonneg _) (fun k => by
      rw [Real.norm_eq_abs]
      exact hbound k) hsqrt
  -- The cross term `∫ (φ - F) F` vanishes, by Cauchy–Schwarz.
  have hcross : Tendsto (fun k => ∫ x, (φ k x - F x) * F x ∂μ) atTop (𝓝 0) := by
    have hsq_F : 0 ≤ ∫ x, F x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    refine squeeze_zero_norm (fun k => ?_) (a := fun k =>
      Real.sqrt (∫ x, (φ k x - F x) ^ 2 ∂μ) * Real.sqrt (∫ x, F x ^ 2 ∂μ)) ?_
    · rw [Real.norm_eq_abs]
      exact abs_integral_mul_le_sqrt ((hφ k).sub hF) hF
    · simpa only [zero_mul] using hsqrt.mul_const (Real.sqrt (∫ x, F x ^ 2 ∂μ))
  -- The second moment converges, from the expansion `φ² = F² + (φ - F)² + 2 (φ - F) F`.
  have hsq : Tendsto (fun k => ∫ x, φ k x ^ 2 ∂μ) atTop (𝓝 (∫ x, F x ^ 2 ∂μ)) := by
    have hexp (k : ℕ) : ∫ x, φ k x ^ 2 ∂μ = ∫ x, F x ^ 2 ∂μ +
        ∫ x, (φ k x - F x) ^ 2 ∂μ + 2 * ∫ x, (φ k x - F x) * F x ∂μ := by
      have hpt (x : Ω) : φ k x ^ 2 =
          F x ^ 2 + (φ k x - F x) ^ 2 + 2 * ((φ k x - F x) * F x) := by ring
      have hsub : MemLp (fun x => φ k x - F x) 2 μ := (hφ k).sub hF
      have h1 : Integrable (fun x => F x ^ 2) μ := hF.integrable_sq
      have h2 : Integrable (fun x => (φ k x - F x) ^ 2) μ := hsub.integrable_sq
      have h3 : Integrable (fun x => (φ k x - F x) * F x) μ := hsub.integrable_mul hF
      have h12 : Integrable (fun x => F x ^ 2 + (φ k x - F x) ^ 2) μ := h1.add h2
      have h3' : Integrable (fun x => 2 * ((φ k x - F x) * F x)) μ := h3.const_mul 2
      simp_rw [hpt]
      rw [integral_add h12 h3', integral_add h1 h2, integral_const_mul]
    have hlim : Tendsto (fun k => ∫ x, F x ^ 2 ∂μ +
        ∫ x, (φ k x - F x) ^ 2 ∂μ + 2 * ∫ x, (φ k x - F x) * F x ∂μ) atTop
        (𝓝 (∫ x, F x ^ 2 ∂μ + 0 + 2 * 0)) :=
      ((tendsto_const_nhds.add hd).add (hcross.const_mul 2))
    simp only [add_zero, mul_zero] at hlim
    exact (hlim.congr fun k => (hexp k).symm)
  rw [integral_sub_mean_sq hF]
  exact (hsq.sub (hmean.pow 2)).congr fun k => (integral_sub_mean_sq (hφ k)).symm

end Riesz1.WeightedSobolev

end

end
