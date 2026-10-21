/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Approximation of bounded C¹ tests for logarithmic Sobolev inequalities

Normalized bump convolutions preserve uniform bounds on both a function and its derivative.
They converge pointwise together with their derivatives. These lemmas are internal analytic
tools. No logarithmic Sobolev inequality is assumed here.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped Convolution ContDiff

namespace Riesz1.LogSobolevInternal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Averaging a bounded continuous function against a normalized bump preserves its bound. -/
lemma norm_bump_convolution_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (φ : ContDiffBump (0 : E)) {g : E → G} {C : ℝ}
    (hg : ∀ x, ‖g x‖ ≤ C) (x : E) :
    ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x‖ ≤ C := by
  change ‖∫ z, φ.normed volume z • g (x - z)‖ ≤ C
  calc
    _ ≤ ∫ z, φ.normed volume z * C := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const C)
      filter_upwards with z
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed z)]
      exact mul_le_mul_of_nonneg_left (hg _) (φ.nonneg_normed z)
    _ = C := by rw [integral_mul_const, φ.integral_normed, one_mul]

/-- The derivative can fall on the C¹ factor without a support restriction on that factor.
The global derivative bound supplies domination for differentiation under the integral. -/
lemma hasFDerivAt_bump_convolution (φ : ContDiffBump (0 : E))
    {q : E → ℝ} (hq : ContDiff ℝ 1 q) {D : ℝ}
    (hD : ∀ x, ‖fderiv ℝ q x‖ ≤ D) (x : E) :
    HasFDerivAt (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] q)
      ((φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ q) x) x := by
  have hc : Continuous (fderiv ℝ q) := hq.continuous_fderiv one_ne_zero
  have hφ : Continuous (φ.normed volume) := φ.continuous_normed
  have hi (y : E) : Integrable (fun z => φ.normed volume z * q (y - z)) volume :=
    (hφ.mul (hq.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      φ.hasCompactSupport_normed.mul_right
  change HasFDerivAt (fun y => ∫ z, φ.normed volume z * q (y - z))
    (∫ z, φ.normed volume z • fderiv ℝ q (x - z)) x
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume)
    (F' := fun y z => φ.normed volume z • fderiv ℝ q (y - z)) (s := univ)
    (bound := fun z => φ.normed volume z * D) (by simp)
  · exact Eventually.of_forall fun y => (hi y).aestronglyMeasurable
  · exact hi x
  · exact (hφ.smul (hc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · filter_upwards with z y _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed z)]
    exact mul_le_mul_of_nonneg_left (hD _) (φ.nonneg_normed z)
  · exact φ.integrable_normed.mul_const D
  · filter_upwards with z y _
    have hd := ((hq.differentiable one_ne_zero) (y - z)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).sub_const z)
    simpa using hd.const_mul (φ.normed volume z)

/-- A bounded C¹ function with bounded derivative admits smooth approximations with exactly
the same bounds, converging pointwise in both value and derivative. -/
theorem exists_smooth_tests {q : E → ℝ} (hq : ContDiff ℝ 1 q) {C D : ℝ}
    (hC : ∀ x, |q x| ≤ C) (hD : ∀ x, ‖fderiv ℝ q x‖ ≤ D) :
    ∃ qn : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ ∞ (qn n)) ∧
      (∀ n x, |qn n x| ≤ C) ∧
      (∀ n x, ‖fderiv ℝ (qn n) x‖ ≤ D) ∧
      (∀ x, Tendsto (fun n => qn n x) atTop (𝓝 (q x))) ∧
      (∀ x, Tendsto (fun n => fderiv ℝ (qn n) x) atTop (𝓝 (fderiv ℝ q x))) := by
  let r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  let φ (n : ℕ) : ContDiffBump (0 : E) :=
    { rIn := r n / 2, rOut := r n, rIn_pos := half_pos (hr n),
      rIn_lt_rOut := half_lt_self (hr n) }
  let qn (n : ℕ) := φ n |>.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] q
  have hd (n : ℕ) (x : E) : fderiv ℝ (qn n) x =
      ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ q) x :=
    (hasFDerivAt_bump_convolution (φ n) hq hD x).fderiv
  have ht : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨qn, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (φ n).hasCompactSupport_normed.contDiff_convolution_left _
      (φ n).contDiff_normed hq.continuous.locallyIntegrable
  · intro n x
    simpa only [Real.norm_eq_abs] using
      norm_bump_convolution_le (φ n) (g := q) (fun y => hC y) x
  · intro n x
    rw [hd]
    exact norm_bump_convolution_le (φ n) hD x
  · exact fun x => ContDiffBump.convolution_tendsto_right_of_continuous ht hq.continuous x
  · intro x
    simp_rw [hd]
    exact ContDiffBump.convolution_tendsto_right_of_continuous ht
      (hq.continuous_fderiv one_ne_zero) x

end Riesz1.LogSobolevInternal

end
