/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.LogSobolevApproximation
public import Riesz1.HelfferSjostrand.LogSobolevTransfer
public import Riesz1.ToMathlib.Herbst.Herbst

/-!
# Smooth approximation of bounded Lipschitz observables

Normalized bump convolution preserves the Lipschitz constant without differentiability
of the observable. This extends the Herbst implication to bounded Lipschitz tests.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal Convolution ContDiff

namespace Riesz1.LogSobolevInternal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Mollification by a normalized bump preserves the exact Lipschitz constant. -/
lemma lipschitz_bump_convolution (φ : ContDiffBump (0 : E)) {G : E → ℝ} {L : ℝ≥0}
    (hG : LipschitzWith L G) :
    LipschitzWith L (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) := by
  have hi (x : E) : Integrable (fun z => φ.normed volume z * G (x - z)) volume :=
    (φ.continuous_normed.mul (hG.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport φ.hasCompactSupport_normed.mul_right
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  change |(∫ z, φ.normed volume z * G (x - z)) -
    (∫ z, φ.normed volume z * G (y - z))| ≤ L * dist x y
  rw [← integral_sub (hi x) (hi y), ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ z, φ.normed volume z * (L * dist x y) := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _)
      filter_upwards with z
      rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed z),
        Real.norm_eq_abs, ← Real.dist_eq]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed z)
      simpa only [dist_sub_right] using hG.dist_le_mul (x - z) (y - z)
    _ = L * dist x y := by rw [integral_mul_const, φ.integral_normed, one_mul]

/-- A bounded Lipschitz function admits smooth approximations with exactly the same value
bound and derivative bound, converging pointwise everywhere. -/
theorem exists_smooth_lipschitz_tests {G : E → ℝ} {L : ℝ≥0}
    (hG : LipschitzWith L G) {C : ℝ} (hC : ∀ x, |G x| ≤ C) :
    ∃ Gn : ℕ → E → ℝ, (∀ n, ContDiff ℝ ∞ (Gn n)) ∧
      (∀ n x, |Gn n x| ≤ C) ∧ (∀ n x, ‖fderiv ℝ (Gn n) x‖ ≤ L) ∧
      (∀ x, Tendsto (fun n => Gn n x) atTop (𝓝 (G x))) := by
  let r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  let φ (n : ℕ) : ContDiffBump (0 : E) :=
    { rIn := r n / 2, rOut := r n, rIn_pos := half_pos (hr n),
      rIn_lt_rOut := half_lt_self (hr n) }
  let Gn (n : ℕ) := φ n |>.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G
  have ht : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨Gn, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (φ n).hasCompactSupport_normed.contDiff_convolution_left _
      (φ n).contDiff_normed hG.continuous.locallyIntegrable
  · intro n x
    simpa only [Real.norm_eq_abs] using
      norm_bump_convolution_le (φ n) (g := G) (fun y => hC y) x
  · intro n x
    exact norm_fderiv_le_of_lipschitz ℝ (lipschitz_bump_convolution (φ n) hG)
  · exact fun x => ContDiffBump.convolution_tendsto_right_of_continuous ht hG.continuous x

/-- Internal Herbst implication for bounded Lipschitz observables. Its LSI premise is
discharged by the conditioning theorem when it is applied. -/
theorem herbst_bounded_lipschitz_of_lsi {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] {w : ℝ} (hw : 0 < w)
    (hLSI : ∀ q : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 q →
      (∃ C, ∀ x, |q x| ≤ C) → (∃ C, ∀ x, ‖fderiv ℝ q x‖ ≤ C) →
      ∫ x, q x^2 * Real.log (q x^2) ∂μ -
          (∫ x, q x^2 ∂μ) * Real.log (∫ x, q x^2 ∂μ) ≤
        2*w * ∫ x, ‖fderiv ℝ q x‖^2 ∂μ)
    {G : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ≥0} (hG : LipschitzWith L G)
    {C : ℝ} (hC : ∀ x, |G x| ≤ C) (t : ℝ) :
    Real.log (∫ x, Real.exp (t * G x) ∂μ) ≤
      t * ∫ x, G x ∂μ + w/2 * t^2 * (L : ℝ)^2 := by
  obtain ⟨Gn, hGn, hCn, hLn, ht⟩ := exists_smooth_lipschitz_tests hG hC
  have hlim₁ := tendsto_integral_comp (μ := μ) (fun n => (hGn n).continuous) hCn ht
    continuous_id
  have hlim₂ := tendsto_integral_comp (μ := μ) (fun n => (hGn n).continuous) hCn ht
    (show Continuous (fun r : ℝ => Real.exp (t * r)) by fun_prop)
  have hpos : 0 < ∫ x, Real.exp (t * G x) ∂μ := herbst_integral_exp_pos hG.continuous hC t
  have hlimlog := (Real.continuousAt_log hpos.ne').tendsto.comp hlim₂
  apply le_of_tendsto_of_tendsto hlimlog
    (tendsto_const_nhds.mul hlim₁ |>.add_const (w/2*t^2*(L : ℝ)^2))
  exact Eventually.of_forall fun n =>
    herbst_log_mgf_le μ w hw hLSI (Gn n) ((hGn n).of_le (by simp)) ⟨C, hCn n⟩ L (hLn n) t

end Riesz1.LogSobolevInternal

end
