/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.QuantitativeVarianceInput
public import Riesz1.CLT.NondegeneracyCompact
import all Riesz1.ToMathlib.Mollifier.RegularizationSobolev

/-!
# Sobolev finiteness of both convolution families

The analytic finiteness assertions in
Theorem 2 need neither loop input.
Fourier contraction bounds the smoothed variance by the original one.
The difference has Fourier coefficients at most twice as large.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Riesz1.Internal

/-- The smoothed test and its difference have variance parameter at most
four times the original, uniformly in every positive smoothing radius. -/
theorem optimalScaling_regularized_variance_le (P : Parameters) (p : Profile) (a : Scale)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {t : ℝ} (ht : 0 < t)
    (v : Profile)
    (hv : (∀ x, v.val x = cltScaledLift hρ a ht
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ x) ∨
      (∀ x, v.val x = testAtScale p a x - cltScaledLift hρ a ht
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ x)) :
    cltVariance P a ⟨(fun x => (v.val x : ℂ)), v.property⟩ ≤
      4 * circleVariance P p a := by
  let g := cltScaledLift hρ a ht
    ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩
  have hg := cltScaledLift_memLp hρ a ht
    ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩
  have hc (k : ℤ) : ‖fourierCoeff (fun x => (v.val x : ℂ)) k‖ ≤
      2 * ‖fourierCoeff (fun x => (testAtScale p a x : ℂ)) k‖ := by
    have hgk : ‖fourierCoeff (fun x => (g x : ℂ)) k‖ ≤
        ‖fourierCoeff (fun x => (testAtScale p a x : ℂ)) k‖ := by
      rw [nondegeneracy_compact_lift_coeff hρ p a ht k, norm_mul]
      exact (mul_le_mul_of_nonneg_left (by
        simpa only [Complex.norm_real, Real.norm_eq_abs] using
          mollifierFT_abs_le_one hρ.isCircleMollifier
            (t * k / (observationLength a).val)) (norm_nonneg _)).trans_eq (mul_one _)
    rcases hv with hv | hv
    · have he : (fun x => (v.val x : ℂ)) = fun x => (g x : ℂ) :=
        funext fun x => congrArg Complex.ofReal (hv x)
      rw [he]
      linarith [norm_nonneg (fourierCoeff (fun x => (testAtScale p a x : ℂ)) k)]
    · have he : (fun x => (v.val x : ℂ)) =
          (fun x => (testAtScale p a x : ℂ)) - (fun x => (g x : ℂ)) := by
        funext x
        simp only [hv, Pi.sub_apply, Complex.ofReal_sub, g]
      rw [he]
      change ‖fourierCoeff (subL2 ⟨(fun x => (testAtScale p a x : ℂ)), testAtScaleL2 p a⟩
        ⟨(fun x => (g x : ℂ)), hg⟩).val k‖ ≤ _
      rw [fourierCoeff_subL2]
      exact (norm_sub_le _ _).trans (by linarith)
  unfold cltVariance circleVariance
  rw [mul_left_comm (4 : ℝ≥0∞)]
  apply mul_le_mul le_rfl _ zero_le zero_le
  unfold circleSobolevSq
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k = 0
  · simp only [hk, ite_true, mul_zero, le_refl]
  · simp only [hk, ite_false]
    have hfour : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by norm_num
    rw [hfour, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    apply ENNReal.ofReal_le_ofReal
    have hs : ‖fourierCoeff (fun x => (v.val x : ℂ)) k‖ ^ 2 ≤
        4 * ‖fourierCoeff (fun x => (testAtScale p a x : ℂ)) k‖ ^ 2 := by
      nlinarith [hc k, norm_nonneg (fourierCoeff (fun x => (v.val x : ℂ)) k),
        norm_nonneg (fourierCoeff (fun x => (testAtScale p a x : ℂ)) k)]
    nlinarith [mul_le_mul_of_nonneg_left hs
      (Real.rpow_nonneg (abs_nonneg (k : ℝ)) (2 * ((1 - P.val.2) / 2)))]

/-- Every test in the input domain has finite variance parameter,
independently of both probabilistic variance estimates. -/
theorem optimalScaling_test_variance_finite (P : Parameters) (p : Profile)
    (ell : Scales) (α : ℝ) (d : TestData) (hadm : Admissible P p ell α d)
    (N : ℕ+) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (r : ℝ) (v : Profile)
    (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
    (hv : OptimalScalingTest p ell N hρ r v f) :
    cltVariance P (ell N) ⟨(fun x => (v.val x : ℂ)), v.property⟩ < ⊤ := by
  have hfin := admissible_circleVariance_finite P p ell α d hadm N
  rcases hv with ⟨hv, _⟩ | ⟨t, ht, _, _, hcases⟩
  · have he : v = ⟨testAtScale p (ell N), testAtScaleL2 p (ell N)⟩ := Subtype.ext hv
    subst v
    exact hfin
  · have hpair : (∀ x, v.val x = cltScaledLift hρ (ell N) ht
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x) ∨
      (∀ x, v.val x = testAtScale p (ell N) x - cltScaledLift hρ (ell N) ht
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x) :=
      hcases.elim (fun h => Or.inl (congrFun h.1)) (fun h => Or.inr h.1)
    exact (optimalScaling_regularized_variance_le P p (ell N) hρ ht v hpair).trans_lt
      (ENNReal.mul_lt_top (by norm_num) hfin)

end Riesz1.Internal
