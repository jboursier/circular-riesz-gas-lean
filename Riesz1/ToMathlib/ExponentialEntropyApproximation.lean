/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.SmoothCutoffApproximation
public import Riesz1.HelfferSjostrand.LogSobolevTransfer

/-!
# Extending exponential entropy bounds by compact cutoffs

This internal implication extends an exponential-test entropy inequality from compactly
supported smooth tests to bounded smooth tests with bounded derivative. It supports
the proof of the Bakry–Émery criterion `External.BakryEmery`. The comparison premise is
discharged by the Bakry–Émery development.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

/-- Internal cutoff extension of an exponential entropy bound. -/
theorem exponential_entropy_of_compact_tests (c : ℝ)
    (hc : ∀ f : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, f x * Real.exp (f x) ∂μ) -
        (∫ x, Real.exp (f x) ∂μ) * Real.log (∫ x, Real.exp (f x) ∂μ) ≤
          c * ∫ x, Real.exp (f x) * ‖fderiv ℝ f x‖ ^ 2 ∂μ)
    {g : E → ℝ} (hg : ContDiff ℝ ∞ g) {K D : ℝ}
    (hK : ∀ x, |g x| ≤ K) (hD : ∀ x, ‖fderiv ℝ g x‖ ≤ D) :
    (∫ x, g x * Real.exp (g x) ∂μ) -
      (∫ x, Real.exp (g x) ∂μ) * Real.log (∫ x, Real.exp (g x) ∂μ) ≤
        c * ∫ x, Real.exp (g x) * ‖fderiv ℝ g x‖ ^ 2 ∂μ := by
  obtain ⟨gn, B, hgn, hcs, hKn, hBn, hloc⟩ := exists_smooth_compact_cutoffs hg hK hD
  have ht (x : E) : Tendsto (fun n => gn n x) atTop (𝓝 (g x)) :=
    tendsto_const_nhds.congr' ((hloc x).mono fun _ hn => hn.eq_of_nhds.symm)
  have ht₁ := LogSobolevInternal.tendsto_integral_comp (μ := μ)
    (fun n => (hgn n).continuous) hKn ht (continuous_id.mul Real.continuous_exp)
  have ht₂ := LogSobolevInternal.tendsto_integral_comp (μ := μ)
    (fun n => (hgn n).continuous) hKn ht Real.continuous_exp
  have ht₃ : Tendsto (fun n => ∫ x, Real.exp (gn n x) * ‖fderiv ℝ (gn n) x‖ ^ 2 ∂μ)
      atTop (𝓝 (∫ x, Real.exp (g x) * ‖fderiv ℝ g x‖ ^ 2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => Real.exp K * B ^ 2)
    · intro n
      exact ((Real.continuous_exp.comp (hgn n).continuous).mul
        (((hgn n).continuous_fderiv (by simp)).norm.pow 2)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
      exact mul_le_mul (Real.exp_le_exp.mpr ((le_abs_self _).trans (hKn n x)))
        (pow_le_pow_left₀ (norm_nonneg _) (hBn n x) 2) (sq_nonneg _) (Real.exp_pos _).le
    · filter_upwards with x
      apply tendsto_const_nhds.congr'
      filter_upwards [hloc x] with n hn
      rw [hn.eq_of_nhds, hn.fderiv_eq]
  have htlog : Tendsto (fun n => Real.log (∫ x, Real.exp (gn n x) ∂μ)) atTop
      (𝓝 (Real.log (∫ x, Real.exp (g x) ∂μ))) := by
    have hI : (∫ x, Real.exp (g x) ∂μ) ≠ 0 := by
      apply ne_of_gt
      apply integral_exp_pos
      exact LogSobolevInternal.integrable_continuous_bounded
        (Real.continuous_exp.comp hg.continuous) (C := Real.exp K) (fun x => by
          rw [Real.norm_of_nonneg (Real.exp_pos _).le]
          exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hK x)))
    exact (Real.continuousAt_log hI).tendsto.comp ht₂
  exact le_of_tendsto_of_tendsto (ht₁.sub (ht₂.mul htlog))
    (tendsto_const_nhds.mul ht₃) (Eventually.of_forall fun n => hc (gn n) (hgn n) (hcs n))

end Riesz1

end
