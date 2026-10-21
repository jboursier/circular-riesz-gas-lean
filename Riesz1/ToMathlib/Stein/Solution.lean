/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Riesz1.ToMathlib.Stein.Gaussian

/-!
# Existence of the Stein solution for a centered Gaussian

For `f` continuously differentiable with `|f| ≤ 1` and `|f'| ≤ 1`, and `σ > 0`, the function
`u(x) = -∫₀¹ E f'(r x + σ √(1 - r²) Z) dr` solves `σ² u' - x u = f - E f(σ Z)`, with
`|u| ≤ 1` and `|u'| ≤ √(2/π)/σ`. The proof differentiates the semigroup representation in `r`
and `x`, using only the mean-derivative formula of `Gaussian.lean`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal

namespace Riesz1

/-- The Gaussian average `E g (r x + σ √(1 - r²) Z)` as a function of `r` and `x`. -/
noncomputable def steinKernel (σ : ℝ) (g : ℝ → ℝ) (r x : ℝ) : ℝ :=
  ∫ z, g (r * x + σ * √(1 - r ^ 2) * z) ∂(gaussianReal 0 1)

/-- The Stein solution `u(x) = -∫₀¹ E f'(r x + σ √(1 - r²) Z) dr`. -/
noncomputable def steinSolution (σ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -∫ r in (0 : ℝ)..1, steinKernel σ (deriv f) r x

/-- The set of parameters `r ≠ 1` has full Lebesgue measure. -/
lemma stein_ae_ne_one : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ 1 :=
  ae_iff.2 (by simp)

/-- Continuity in the time parameter `r` of a bounded Gaussian average. -/
lemma stein_continuous_kernel {σ x : ℝ} {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ y, |g y| ≤ C) : Continuous (fun r => steinKernel σ g r x) := by
  unfold steinKernel
  refine continuous_of_dominated (bound := fun _ => C) (fun r => ?_)
    (fun r => Eventually.of_forall fun z => ?_) (integrable_const C)
    (Eventually.of_forall fun z => ?_)
  · have hcz : Continuous (fun z : ℝ => r * x + σ * √(1 - r ^ 2) * z) := by fun_prop
    exact (hg.comp hcz).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact hC _
  · have hcr : Continuous (fun r : ℝ => r * x + σ * √(1 - r ^ 2) * z) := by fun_prop
    exact hg.comp hcr

/-- A Gaussian average of a function bounded by `1` is bounded by `1`. -/
lemma stein_abs_kernel_le {σ r x : ℝ} {g : ℝ → ℝ} (hg : ∀ y, |g y| ≤ 1) :
    |steinKernel σ g r x| ≤ 1 := by
  unfold steinKernel
  have h := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
    (f := fun z => g (r * x + σ * √(1 - r ^ 2) * z)) (C := 1)
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hg _)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact h

/-- Derivative in `r` of the Gaussian average of `f`, for `0 < r < 1`. -/
lemma stein_hasDerivAt_kernel_r {σ x r₀ : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hσ : 0 < σ)
    (hfb : ∀ y, |f y| ≤ 1) (hf' : ∀ y, |deriv f y| ≤ 1) (hr₀ : r₀ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun r => steinKernel σ f r x)
      (∫ z, deriv f (r₀ * x + σ * √(1 - r₀ ^ 2) * z) * (x - σ * r₀ * z / √(1 - r₀ ^ 2))
        ∂(gaussianReal 0 1)) r₀ := by
  obtain ⟨hr₀pos, hr₀lt⟩ := hr₀
  have hfc : Continuous f := hf.continuous
  have hdc : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  -- The parameters near `r₀` stay in `(r₀ / 2, r₁)` with `r₁ = (1 + r₀) / 2 < 1`.
  have hr₁lt : (1 + r₀) / 2 < 1 := by linarith
  have hr₁pos : 0 < (1 + r₀) / 2 := by linarith
  have hm : 0 < √(1 - ((1 + r₀) / 2) ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hs : Ioo (r₀ / 2) ((1 + r₀) / 2) ∈ 𝓝 r₀ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hcz : ∀ r : ℝ, Continuous (fun z : ℝ => r * x + σ * √(1 - r ^ 2) * z) := fun r => by
    fun_prop
  -- The derivative of the integrand in `r`.
  have hinner : ∀ z r : ℝ, 0 < r → r < 1 →
      HasDerivAt (fun r : ℝ => f (r * x + σ * √(1 - r ^ 2) * z))
        (deriv f (r * x + σ * √(1 - r ^ 2) * z) * (x - σ * r * z / √(1 - r ^ 2))) r := by
    intro z r hr0 hr1
    have hpos : 0 < 1 - r ^ 2 := by nlinarith
    have hq : HasDerivAt (fun r : ℝ => 1 - r ^ 2) (-(2 * r)) r := by
      have := (hasDerivAt_pow 2 r).const_sub 1
      convert this using 1
      norm_num
    have hs' : HasDerivAt (fun r : ℝ => √(1 - r ^ 2)) (-(2 * r) / (2 * √(1 - r ^ 2))) r :=
      hq.sqrt hpos.ne'
    have hin : HasDerivAt (fun r : ℝ => r * x + σ * √(1 - r ^ 2) * z)
        (1 * x + σ * (-(2 * r) / (2 * √(1 - r ^ 2))) * z) r :=
      ((hasDerivAt_id r).mul_const x).add ((hs'.const_mul σ).mul_const z)
    have hfr := (hfd (r * x + σ * √(1 - r ^ 2) * z)).hasDerivAt
    refine (hfr.comp r hin).congr_deriv ?_
    have hsq : √(1 - r ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    congr 1
    field_simp
    ring
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 1)
    (F := fun r z => f (r * x + σ * √(1 - r ^ 2) * z))
    (F' := fun r z => deriv f (r * x + σ * √(1 - r ^ 2) * z) * (x - σ * r * z / √(1 - r ^ 2)))
    (bound := fun z => |x| + σ / √(1 - ((1 + r₀) / 2) ^ 2) * |z|)
    (s := Ioo (r₀ / 2) ((1 + r₀) / 2)) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun r => (hfc.comp (hcz r)).aestronglyMeasurable
  · exact (integrable_const (1 : ℝ)).mono' (hfc.comp (hcz r₀)).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hfb _)
  · have hc : Continuous (fun z : ℝ => deriv f (r₀ * x + σ * √(1 - r₀ ^ 2) * z)
        * (x - σ * r₀ * z / √(1 - r₀ ^ 2))) := by
      have := hdc.comp (hcz r₀)
      fun_prop
    exact hc.aestronglyMeasurable
  · refine Eventually.of_forall fun z r hr => ?_
    obtain ⟨hr1, hr2⟩ := hr
    have hr0 : 0 < r := by linarith
    have hr1' : r ≤ 1 := by linarith
    have hpos : 0 < 1 - r ^ 2 := by nlinarith
    have hm_le : √(1 - ((1 + r₀) / 2) ^ 2) ≤ √(1 - r ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have hsr : 0 < √(1 - r ^ 2) := Real.sqrt_pos.2 hpos
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |deriv f (r * x + σ * √(1 - r ^ 2) * z)| ≤ 1 := hf' _
    have h2 : |x - σ * r * z / √(1 - r ^ 2)| ≤ |x| + σ / √(1 - ((1 + r₀) / 2) ^ 2) * |z| := by
      calc |x - σ * r * z / √(1 - r ^ 2)| ≤ |x| + |σ * r * z / √(1 - r ^ 2)| := abs_sub _ _
        _ ≤ |x| + σ / √(1 - ((1 + r₀) / 2) ^ 2) * |z| := by
          gcongr
          rw [abs_div, abs_mul, abs_mul, abs_of_pos hσ, abs_of_pos hr0, abs_of_pos hsr]
          have hz := abs_nonneg z
          calc σ * r * |z| / √(1 - r ^ 2) ≤ σ * |z| / √(1 - r ^ 2) := by
                gcongr
                exact mul_le_of_le_one_right hσ.le hr1'
            _ ≤ σ * |z| / √(1 - ((1 + r₀) / 2) ^ 2) := by
                gcongr
            _ = σ / √(1 - ((1 + r₀) / 2) ^ 2) * |z| := by ring
    calc |deriv f (r * x + σ * √(1 - r ^ 2) * z)| * |x - σ * r * z / √(1 - r ^ 2)|
        ≤ 1 * (|x| + σ / √(1 - ((1 + r₀) / 2) ^ 2) * |z|) :=
          mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = |x| + σ / √(1 - ((1 + r₀) / 2) ^ 2) * |z| := one_mul _
  · exact (integrable_const |x|).add (stein_integrable_abs_std.const_mul _)
  · refine Eventually.of_forall fun z r hr => ?_
    obtain ⟨hr1, hr2⟩ := hr
    exact hinner z r (by linarith) (by linarith)

/-- Derivative in `x` of the Gaussian average of `f'`, for `0 < r < 1`. -/
lemma stein_hasDerivAt_kernel_x {σ r : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hσ : 0 < σ)
    (hf' : ∀ y, |deriv f y| ≤ 1) (hr : r ∈ Ioo (0 : ℝ) 1) (x : ℝ) :
    HasDerivAt (fun x => steinKernel σ (deriv f) r x)
      (r / (σ * √(1 - r ^ 2)) * ∫ z, z * deriv f (r * x + σ * √(1 - r ^ 2) * z)
        ∂(gaussianReal 0 1)) x := by
  obtain ⟨hr0, hr1⟩ := hr
  have hdc : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hpos : 0 < σ * √(1 - r ^ 2) := mul_pos hσ (Real.sqrt_pos.2 (by nlinarith))
  have hG := stein_hasDerivAt_gaussian_mean hdc hf' hpos (r * x)
  have hlin : HasDerivAt (fun y : ℝ => r * y) r x := by
    simpa using (hasDerivAt_id x).const_mul r
  refine (hG.comp x hlin).congr_deriv ?_
  ring

/-- Bound on the `x`-derivative integrand: `|r / c * E[Z f'(·)]| ≤ √(2/π) r / (σ √(1 - r²))`. -/
lemma stein_abs_kernel_deriv_le {σ r x : ℝ} {f : ℝ → ℝ}
    (hf' : ∀ y, |deriv f y| ≤ 1) (hσ : 0 < σ) (hr : r ∈ Icc (0 : ℝ) 1) :
    |r / (σ * √(1 - r ^ 2)) * ∫ z, z * deriv f (r * x + σ * √(1 - r ^ 2) * z) ∂(gaussianReal 0 1)|
      ≤ √(2 / π) * r / (σ * √(1 - r ^ 2)) := by
  have hI := stein_abs_integral_mul_id_le hf' (r * x) (σ * √(1 - r ^ 2))
  have hnn : 0 ≤ r / (σ * √(1 - r ^ 2)) := div_nonneg hr.1 (mul_nonneg hσ.le (Real.sqrt_nonneg _))
  rw [abs_mul, abs_of_nonneg hnn]
  calc r / (σ * √(1 - r ^ 2)) * |∫ z, z * deriv f (r * x + σ * √(1 - r ^ 2) * z) ∂(gaussianReal 0 1)|
      ≤ r / (σ * √(1 - r ^ 2)) * (1 * √(2 / π)) := mul_le_mul_of_nonneg_left hI hnn
    _ = √(2 / π) * r / (σ * √(1 - r ^ 2)) := by ring

/-- The integrand `r / √(1 - r²)` is interval integrable on `[0, 1]`, with integral `1`. -/
lemma stein_intervalIntegrable_r_div_sqrt :
    IntervalIntegrable (fun r : ℝ => r / √(1 - r ^ 2)) volume 0 1 ∧
      ∫ r in (0 : ℝ)..1, r / √(1 - r ^ 2) = 1 := by
  have hGc : ContinuousOn (fun r : ℝ => -√(1 - r ^ 2)) (Icc 0 1) := by
    apply Continuous.continuousOn
    fun_prop
  have hderiv : ∀ r ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => -√(1 - r ^ 2)) (r / √(1 - r ^ 2)) r := by
    intro r hr
    have hpos : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
    have hq : HasDerivAt (fun r : ℝ => 1 - r ^ 2) (-(2 * r)) r := by
      have := (hasDerivAt_pow 2 r).const_sub 1
      convert this using 1
      norm_num
    refine ((hq.sqrt hpos.ne').neg).congr_deriv ?_
    have hsq : √(1 - r ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    field_simp
  have hnn : ∀ r ∈ Ioo (0 : ℝ) 1, 0 ≤ r / √(1 - r ^ 2) := fun r hr =>
    div_nonneg hr.1.le (Real.sqrt_nonneg _)
  have hint : IntegrableOn (fun r : ℝ => r / √(1 - r ^ 2)) (Ioc 0 1) :=
    intervalIntegral.integrableOn_deriv_of_nonneg hGc hderiv hnn
  have hII : IntervalIntegrable (fun r : ℝ => r / √(1 - r ^ 2)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hint
  refine ⟨hII, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hGc hderiv hII]
  norm_num

/-- A jointly measurable integrand gives a strongly measurable parametric Gaussian average. -/
lemma stein_stronglyMeasurable_param {G : ℝ × ℝ → ℝ} (hG : Measurable G) :
    StronglyMeasurable (fun r : ℝ => ∫ z, G (r, z) ∂(gaussianReal 0 1)) :=
  hG.stronglyMeasurable.integral_prod_right'

/-- The `x`-derivative of the solution: the parametric integral of `dK` is interval integrable,
and the derivative of `x ↦ -∫₀¹ E f'(r x + σ √(1 - r²) Z) dr` is `-∫₀¹ dK dr`. -/
lemma stein_hasDerivAt_solution {σ : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hσ : 0 < σ)
    (hf' : ∀ y, |deriv f y| ≤ 1) (x : ℝ) :
    IntervalIntegrable (fun r : ℝ => r / (σ * √(1 - r ^ 2))
        * ∫ z, z * deriv f (r * x + σ * √(1 - r ^ 2) * z) ∂(gaussianReal 0 1)) volume 0 1 ∧
      HasDerivAt (steinSolution σ f)
        (-∫ r in (0 : ℝ)..1, r / (σ * √(1 - r ^ 2))
          * ∫ z, z * deriv f (r * x + σ * √(1 - r ^ 2) * z) ∂(gaussianReal 0 1)) x := by
  have hdc : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hdm : Measurable (deriv f) := hdc.measurable
  have hkern : ∀ y, Continuous (fun r => steinKernel σ (deriv f) r y) := fun y =>
    stein_continuous_kernel hdc hf'
  have hJ : StronglyMeasurable (fun r : ℝ =>
      ∫ z, z * deriv f (r * x + σ * √(1 - r ^ 2) * z) ∂(gaussianReal 0 1)) :=
    stein_stronglyMeasurable_param (G := fun p : ℝ × ℝ =>
      p.2 * deriv f (p.1 * x + σ * √(1 - p.1 ^ 2) * p.2))
      (measurable_snd.mul (hdm.comp (by fun_prop)))
  have hmeasF : Measurable (fun r : ℝ => r / (σ * √(1 - r ^ 2))) := by
    fun_prop
  have hB := stein_intervalIntegrable_r_div_sqrt.1
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1) (x₀ := x) (s := univ)
    (F := fun y r => steinKernel σ (deriv f) r y)
    (F' := fun y r => r / (σ * √(1 - r ^ 2))
      * ∫ z, z * deriv f (r * y + σ * √(1 - r ^ 2) * z) ∂(gaussianReal 0 1))
    (bound := fun r => √(2 / π) / σ * (r / √(1 - r ^ 2)))
    univ_mem
    (Eventually.of_forall fun y => (hkern y).aestronglyMeasurable)
    ((hkern x).intervalIntegrable 0 1)
    (hmeasF.mul hJ.measurable).aestronglyMeasurable
    (by
      refine Eventually.of_forall fun r hr y _ => ?_
      rw [Set.uIoc_of_le zero_le_one] at hr
      rw [Real.norm_eq_abs]
      refine (stein_abs_kernel_deriv_le hf' hσ ⟨hr.1.le, hr.2⟩).trans_eq ?_
      ring)
    (hB.const_mul _)
    (by
      filter_upwards [stein_ae_ne_one] with r hr1 hr y _
      rw [Set.uIoc_of_le zero_le_one] at hr
      exact stein_hasDerivAt_kernel_x hf hσ hf' ⟨hr.1, lt_of_le_of_ne hr.2 hr1⟩ y)
  exact ⟨hmain.1, hmain.2.neg⟩

/-- Pointwise bound on the `r`-derivative of the Gaussian average, uniformly for `r ∈ [0, 1]`. -/
lemma stein_abs_kernel_deriv_r_le {σ r x : ℝ} {f : ℝ → ℝ} (hdc : Continuous (deriv f))
    (hf' : ∀ y, |deriv f y| ≤ 1) (hσ : 0 < σ) (hr : r ∈ Icc (0 : ℝ) 1) :
    |∫ z, deriv f (r * x + σ * √(1 - r ^ 2) * z) * (x - σ * r * z / √(1 - r ^ 2))
        ∂(gaussianReal 0 1)| ≤ |x| + σ * √(2 / π) * (r / √(1 - r ^ 2)) := by
  have hcz : Continuous (fun z : ℝ => r * x + σ * √(1 - r ^ 2) * z) := by fun_prop
  have hfi : Integrable (fun z => deriv f (r * x + σ * √(1 - r ^ 2) * z)) (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).mono' (hdc.comp hcz).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hf' _)
  have hgi : Integrable (fun z => z * deriv f (r * x + σ * √(1 - r ^ 2) * z))
      (gaussianReal 0 1) :=
    stein_integrable_mul_id hdc hf' _ _
  have hsplit : (fun z => deriv f (r * x + σ * √(1 - r ^ 2) * z) * (x - σ * r * z / √(1 - r ^ 2)))
      = fun z => x * deriv f (r * x + σ * √(1 - r ^ 2) * z)
          - (σ * r / √(1 - r ^ 2)) * (z * deriv f (r * x + σ * √(1 - r ^ 2) * z)) := by
    funext z
    ring
  rw [hsplit, integral_sub (hfi.const_mul x) (hgi.const_mul _), integral_const_mul,
    integral_const_mul]
  have hJ : |∫ z, deriv f (r * x + σ * √(1 - r ^ 2) * z) ∂(gaussianReal 0 1)| ≤ 1 :=
    stein_abs_kernel_le (σ := σ) (r := r) (x := x) hf'
  have hI := stein_abs_integral_mul_id_le hf' (r * x) (σ * √(1 - r ^ 2))
  have hk : 0 ≤ σ * r / √(1 - r ^ 2) := div_nonneg (mul_nonneg hσ.le hr.1) (Real.sqrt_nonneg _)
  calc |x * ∫ z, deriv f (r * x + σ * √(1 - r ^ 2) * z) ∂(gaussianReal 0 1)
        - σ * r / √(1 - r ^ 2) * ∫ z, z * deriv f (r * x + σ * √(1 - r ^ 2) * z)
          ∂(gaussianReal 0 1)|
      ≤ |x * ∫ z, deriv f (r * x + σ * √(1 - r ^ 2) * z) ∂(gaussianReal 0 1)|
        + |σ * r / √(1 - r ^ 2) * ∫ z, z * deriv f (r * x + σ * √(1 - r ^ 2) * z)
          ∂(gaussianReal 0 1)| := abs_sub _ _
    _ = |x| * |∫ z, deriv f (r * x + σ * √(1 - r ^ 2) * z) ∂(gaussianReal 0 1)|
        + |σ * r / √(1 - r ^ 2)| * |∫ z, z * deriv f (r * x + σ * √(1 - r ^ 2) * z)
          ∂(gaussianReal 0 1)| := by
          rw [abs_mul, abs_mul]
    _ ≤ |x| * 1 + |σ * r / √(1 - r ^ 2)| * (1 * √(2 / π)) :=
          add_le_add (mul_le_mul_of_nonneg_left hJ (abs_nonneg x))
            (mul_le_mul_of_nonneg_left hI (abs_nonneg _))
    _ = |x| + σ * √(2 / π) * (r / √(1 - r ^ 2)) := by
          rw [abs_of_nonneg hk]
          ring

/-- The `r`-integrand of the Stein equation is interval integrable on `[0, 1]`. -/
lemma stein_intervalIntegrable_kernel_deriv_r {σ x : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hσ : 0 < σ) (hf' : ∀ y, |deriv f y| ≤ 1) :
    IntervalIntegrable (fun r : ℝ => ∫ z, deriv f (r * x + σ * √(1 - r ^ 2) * z)
      * (x - σ * r * z / √(1 - r ^ 2)) ∂(gaussianReal 0 1)) volume 0 1 := by
  have hdc : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hB : IntervalIntegrable (fun r : ℝ => |x| + σ * √(2 / π) * (r / √(1 - r ^ 2)))
      volume 0 1 :=
    intervalIntegrable_const.add (stein_intervalIntegrable_r_div_sqrt.1.const_mul _)
  have hmeas : StronglyMeasurable (fun r : ℝ => ∫ z, deriv f (r * x + σ * √(1 - r ^ 2) * z)
      * (x - σ * r * z / √(1 - r ^ 2)) ∂(gaussianReal 0 1)) :=
    stein_stronglyMeasurable_param (G := fun p : ℝ × ℝ =>
      deriv f (p.1 * x + σ * √(1 - p.1 ^ 2) * p.2) * (x - σ * p.1 * p.2 / √(1 - p.1 ^ 2)))
      (by
        have hdm : Measurable (deriv f) := hdc.measurable
        fun_prop)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hB ⊢
  refine Integrable.mono' hB hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_)
  rw [Real.norm_eq_abs]
  exact stein_abs_kernel_deriv_r_le hdc hf' hσ ⟨hr.1.le, hr.2⟩

/-- Fundamental theorem of calculus in `r`: the `r`-integral of the derivative of the Gaussian
average of `f` is the difference of its endpoint values. -/
lemma stein_integral_kernel_deriv_r {σ x : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hσ : 0 < σ)
    (hfb : ∀ y, |f y| ≤ 1) (hf' : ∀ y, |deriv f y| ≤ 1) :
    ∫ r in (0 : ℝ)..1, (∫ z, deriv f (r * x + σ * √(1 - r ^ 2) * z)
        * (x - σ * r * z / √(1 - r ^ 2)) ∂(gaussianReal 0 1))
      = steinKernel σ f 1 x - steinKernel σ f 0 x :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun r => steinKernel σ f r x)
    zero_le_one
    (stein_continuous_kernel (σ := σ) (x := x) hf.continuous hfb).continuousOn
    (fun _ hr => stein_hasDerivAt_kernel_r hf hσ hfb hf' hr)
    (stein_intervalIntegrable_kernel_deriv_r hf hσ hf')

/-- At `r = 1` the Gaussian average of `f` is `f x`, since the variance vanishes. -/
lemma stein_kernel_one (σ x : ℝ) (f : ℝ → ℝ) : steinKernel σ f 1 x = f x := by
  unfold steinKernel
  simp

/-- At `r = 0` the Gaussian average of `f` is the average of `f (σ Z)`. -/
lemma stein_kernel_zero (σ x : ℝ) (f : ℝ → ℝ) :
    steinKernel σ f 0 x = ∫ z, f (σ * z) ∂(gaussianReal 0 1) := by
  unfold steinKernel
  simp

/-- The pointwise identity behind the Stein equation: for `0 < r < 1`,
`σ² ∂ₓ K(r, x) - x K(r, x) = -∂_r K(r, x)` where `K(r, x)` is the Gaussian average of `f`. -/
lemma stein_pointwise_identity {σ r x : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hσ : 0 < σ)
    (hf' : ∀ y, |deriv f y| ≤ 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    σ ^ 2 * (r / (σ * √(1 - r ^ 2)) * ∫ z, z * deriv f (r * x + σ * √(1 - r ^ 2) * z)
        ∂(gaussianReal 0 1))
      - x * steinKernel σ (deriv f) r x
      = -∫ z, deriv f (r * x + σ * √(1 - r ^ 2) * z) * (x - σ * r * z / √(1 - r ^ 2))
        ∂(gaussianReal 0 1) := by
  obtain ⟨hr0, hr1⟩ := hr
  have hdc : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hsr : 0 < √(1 - r ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hcz : Continuous (fun z : ℝ => r * x + σ * √(1 - r ^ 2) * z) := by fun_prop
  have hfi : Integrable (fun z => deriv f (r * x + σ * √(1 - r ^ 2) * z)) (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).mono' (hdc.comp hcz).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hf' _)
  have hgi : Integrable (fun z => z * deriv f (r * x + σ * √(1 - r ^ 2) * z))
      (gaussianReal 0 1) :=
    stein_integrable_mul_id hdc hf' _ _
  have hsplit : (fun z => deriv f (r * x + σ * √(1 - r ^ 2) * z) * (x - σ * r * z / √(1 - r ^ 2)))
      = fun z => x * deriv f (r * x + σ * √(1 - r ^ 2) * z)
          - (σ * r / √(1 - r ^ 2)) * (z * deriv f (r * x + σ * √(1 - r ^ 2) * z)) := by
    funext z
    ring
  have key : ∫ z, deriv f (r * x + σ * √(1 - r ^ 2) * z) * (x - σ * r * z / √(1 - r ^ 2))
        ∂(gaussianReal 0 1)
      = x * steinKernel σ (deriv f) r x
        - σ * r / √(1 - r ^ 2) * ∫ z, z * deriv f (r * x + σ * √(1 - r ^ 2) * z)
          ∂(gaussianReal 0 1) := by
    rw [hsplit, integral_sub (hfi.const_mul x) (hgi.const_mul _), integral_const_mul,
      integral_const_mul]
    rfl
  rw [key]
  have e : σ ^ 2 * (r / (σ * √(1 - r ^ 2))) = σ * r / √(1 - r ^ 2) := by
    field_simp
  linear_combination (∫ z, z * deriv f (r * x + σ * √(1 - r ^ 2) * z) ∂(gaussianReal 0 1)) * e

/-- The Stein equation for the Stein solution, with `E f(σ Z)` in the right-hand side. -/
lemma stein_ode {σ x : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hσ : 0 < σ)
    (hfb : ∀ y, |f y| ≤ 1) (hf' : ∀ y, |deriv f y| ≤ 1) :
    σ ^ 2 * deriv (steinSolution σ f) x - x * steinSolution σ f x
      = f x - ∫ z, f (σ * z) ∂(gaussianReal 0 1) := by
  have hdc : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  obtain ⟨hdKint, hderiv⟩ := stein_hasDerivAt_solution hf hσ hf' x
  have hFint : IntervalIntegrable (fun r : ℝ => steinKernel σ (deriv f) r x) volume 0 1 :=
    (stein_continuous_kernel (σ := σ) (x := x) hdc hf').intervalIntegrable 0 1
  have hsum : σ ^ 2 * (∫ r in (0 : ℝ)..1, r / (σ * √(1 - r ^ 2))
          * ∫ z, z * deriv f (r * x + σ * √(1 - r ^ 2) * z) ∂(gaussianReal 0 1))
        - x * ∫ r in (0 : ℝ)..1, steinKernel σ (deriv f) r x
      = ∫ r in (0 : ℝ)..1, (σ ^ 2 * (r / (σ * √(1 - r ^ 2))
          * ∫ z, z * deriv f (r * x + σ * √(1 - r ^ 2) * z) ∂(gaussianReal 0 1))
          - x * steinKernel σ (deriv f) r x) := by
    rw [intervalIntegral.integral_sub (hdKint.const_mul _) (hFint.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hpt : ∫ r in (0 : ℝ)..1, (σ ^ 2 * (r / (σ * √(1 - r ^ 2))
          * ∫ z, z * deriv f (r * x + σ * √(1 - r ^ 2) * z) ∂(gaussianReal 0 1))
          - x * steinKernel σ (deriv f) r x)
      = ∫ r in (0 : ℝ)..1, -∫ z, deriv f (r * x + σ * √(1 - r ^ 2) * z)
          * (x - σ * r * z / √(1 - r ^ 2)) ∂(gaussianReal 0 1) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [stein_ae_ne_one] with r hr1 hr
    rw [Set.uIoc_of_le zero_le_one] at hr
    exact stein_pointwise_identity hf hσ hf' ⟨hr.1, lt_of_le_of_ne hr.2 hr1⟩
  have hH : ∫ r in (0 : ℝ)..1, -∫ z, deriv f (r * x + σ * √(1 - r ^ 2) * z)
          * (x - σ * r * z / √(1 - r ^ 2)) ∂(gaussianReal 0 1)
      = -(f x - ∫ z, f (σ * z) ∂(gaussianReal 0 1)) := by
    rw [intervalIntegral.integral_neg, stein_integral_kernel_deriv_r hf hσ hfb hf',
      stein_kernel_one, stein_kernel_zero]
  rw [hderiv.deriv]
  unfold steinSolution
  linear_combination -hsum - hpt - hH

/-- The Stein solution is bounded by `1`. -/
lemma stein_abs_solution_le {σ x : ℝ} {f : ℝ → ℝ} (hf' : ∀ y, |deriv f y| ≤ 1) :
    |steinSolution σ f x| ≤ 1 := by
  unfold steinSolution
  rw [abs_neg]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := 1)
    (f := fun r => steinKernel σ (deriv f) r x)
    (fun _ _ => by
      rw [Real.norm_eq_abs]
      exact stein_abs_kernel_le hf')
  simpa [Real.norm_eq_abs] using h

/-- The derivative of the Stein solution is bounded by `√(2/π)/σ`. -/
lemma stein_abs_deriv_solution_le {σ x : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hσ : 0 < σ)
    (hf' : ∀ y, |deriv f y| ≤ 1) :
    |deriv (steinSolution σ f) x| ≤ √(2 / π) / σ := by
  obtain ⟨_, hderiv⟩ := stein_hasDerivAt_solution hf hσ hf' x
  rw [hderiv.deriv, abs_neg, ← Real.norm_eq_abs]
  have hae : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioc (0 : ℝ) 1 →
      ‖r / (σ * √(1 - r ^ 2)) * ∫ z, z * deriv f (r * x + σ * √(1 - r ^ 2) * z)
        ∂(gaussianReal 0 1)‖ ≤ √(2 / π) / σ * (r / √(1 - r ^ 2)) :=
    Eventually.of_forall fun r hr => by
      rw [Real.norm_eq_abs]
      refine (stein_abs_kernel_deriv_le hf' hσ ⟨hr.1.le, hr.2⟩).trans_eq ?_
      ring
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) zero_le_one hae
    (stein_intervalIntegrable_r_div_sqrt.1.const_mul (√(2 / π) / σ))
  rw [intervalIntegral.integral_const_mul, stein_intervalIntegrable_r_div_sqrt.2, mul_one] at h
  exact h

/-- **Existence of the Stein solution.** For `f` of class `C¹` with `|f| ≤ 1` and `|f'| ≤ 1`,
and `σ > 0`, there is a `C¹` function `u` with `σ² u' - x u = f - E f(σ Z)`, `|u| ≤ 1`, and
`|u'| ≤ √(2/π)/σ`. -/
theorem exists_stein_solution (σ : ℝ) (hσ : 0 < σ) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hfb : ∀ x, |f x| ≤ 1) (hf' : ∀ x, |deriv f x| ≤ 1) :
    ∃ u : ℝ → ℝ, ContDiff ℝ 1 u ∧
      (∀ x, σ ^ 2 * deriv u x - x * u x =
        f x - ∫ y, f y ∂(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩)) ∧
      (∀ x, |u x| ≤ 1) ∧ (∀ x, |deriv u x| ≤ Real.sqrt (2 / Real.pi) / σ) := by
  have hfc : Continuous f := hf.continuous
  have hscale : ∫ y, f y ∂(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩)
      = ∫ z, f (σ * z) ∂(gaussianReal 0 1) :=
    stein_integral_gaussian_scale σ hfc
  have hdiff : Differentiable ℝ (steinSolution σ f) := fun x =>
    (stein_hasDerivAt_solution hf hσ hf' x).2.differentiableAt
  refine ⟨steinSolution σ f, ?_, fun x => ?_, fun x => stein_abs_solution_le hf', fun x =>
    stein_abs_deriv_solution_le hf hσ hf'⟩
  · rw [contDiff_one_iff_deriv]
    refine ⟨hdiff, ?_⟩
    have hd : deriv (steinSolution σ f) = fun x => (x * steinSolution σ f x
        + (f x - ∫ z, f (σ * z) ∂(gaussianReal 0 1))) / σ ^ 2 := by
      funext x
      have h := stein_ode (x := x) hf hσ hfb hf'
      field_simp
      linear_combination h
    rw [hd]
    exact ((continuous_id.mul hdiff.continuous).add (hfc.sub continuous_const)).div_const _
  · rw [hscale]
    exact stein_ode (x := x) hf hσ hfb hf'

end Riesz1
