/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryReductionFinalBridge
import all Riesz1.Variance.LoopMaster

/-!
# Smoothing uniformly over both convolution families

The microscopic smoothing error of either family is at most four times
that of the original profile. This Fourier argument needs no new
admissibility certificates for the varying family members, and its
constant is independent of the additional smoothing parameter.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1.Internal

/-- The microscopic error multiplier, on the actual objects. -/
theorem auxiliary_error_coeff {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (N : ℕ+) (a : Scale)
    (f : {f : Circle (loopMasterLength a) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength a))}) (k : ℤ) :
    circleCoeff (loopMasterPullback (loopMasterLength a)
        (subCircleL2 f (mixedReg hρ N a f)).val) k =
      circleCoeff (loopMasterPullback (loopMasterLength a) f.val) k *
        (1 - (mollifierFT ρ ((cltK N a)⁻¹ * k / (loopMasterLength a).val) : ℂ)) := by
  change circleCoeff
    (fun z => loopMasterPullback (loopMasterLength a) f.val z -
      loopMasterPullback (loopMasterLength a) (mixedReg hρ N a f).val z) k = _
  rw [circleCoeff_sub_of_memLp _ _ (loopMasterPullback_memLp _ f)
    (loopMasterPullback_memLp _ (mixedReg hρ N a f))]
  change circleCoeff (loopMasterPullback (loopMasterLength a) f.val) k -
      circleCoeff (loopMasterPullback (loopMasterLength a)
        (cltRegCircle hρ _ (inv_pos.mpr (cltK_pos N a)) f)) k = _
  rw [circleCoeff_pullback_cltRegCircle]
  ring

/-- Pointwise domination of Fourier coefficients passes to the extended
variance parameter with the square of the amplitude, here amplitude two. -/
theorem auxiliary_scaledVariance_le_four (P : Parameters) (a : Scale)
    (f g : {f : Circle (loopMasterLength a) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength a))})
    (hc : ∀ k : ℤ, ‖circleCoeff (loopMasterPullback (loopMasterLength a) f.val) k‖ ≤
      2 * ‖circleCoeff (loopMasterPullback (loopMasterLength a) g.val) k‖) :
    scaledVariance P a f ≤ 4 * scaledVariance P a g := by
  unfold scaledVariance cltVariance
  rw [mul_left_comm (4 : ℝ≥0∞)]
  apply mul_le_mul le_rfl _ zero_le zero_le
  unfold circleSobolevSq
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k = 0
  · simp only [hk, ite_true, mul_zero, le_refl]
  · simp only [hk, ite_false]
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    apply ENNReal.ofReal_le_ofReal
    have hs : ‖circleCoeff (loopMasterPullback (loopMasterLength a) f.val) k‖ ^ 2 ≤
        4 * ‖circleCoeff (loopMasterPullback (loopMasterLength a) g.val) k‖ ^ 2 := by
      nlinarith [hc k, norm_nonneg (circleCoeff (loopMasterPullback (loopMasterLength a) f.val) k),
        norm_nonneg (circleCoeff (loopMasterPullback (loopMasterLength a) g.val) k)]
    change |(k : ℝ)| ^ (2 * ((1 - P.val.2) / 2)) *
        ‖circleCoeff (loopMasterPullback (loopMasterLength a) f.val) k‖ ^ 2 ≤
      4 * (|(k : ℝ)| ^ (2 * ((1 - P.val.2) / 2)) *
        ‖circleCoeff (loopMasterPullback (loopMasterLength a) g.val) k‖ ^ 2)
    nlinarith [mul_le_mul_of_nonneg_left hs
      (Real.rpow_nonneg (abs_nonneg (k : ℝ)) (2 * ((1 - P.val.2) / 2)))]

/-- The actual original, smoothed, and difference tests share a Fourier
coefficient envelope independent of the optional family radius. -/
theorem auxiliary_family_coeff_le (p : Profile) (ell : Scales) (N : ℕ+)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (r : ℝ) (v : Profile)
    (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
    (hv : OptimalScalingTest p ell N hρ r v f) (k : ℤ) :
    ‖circleCoeff (loopMasterPullback (loopMasterLength (ell N)) f.val) k‖ ≤
      2 * ‖circleCoeff (loopMasterPullback (loopMasterLength (ell N))
        (periodizedProfile p (observationLength (ell N)))) k‖ := by
  let ξ := (⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ :
    {f : Circle (loopMasterLength (ell N)) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
  rcases hv with ⟨_, rfl⟩ | ⟨t, ht, _, _, hcases⟩
  · exact le_mul_of_one_le_left (norm_nonneg _) (by norm_num)
  · have hc : ‖circleCoeff (loopMasterPullback (loopMasterLength (ell N))
        (cltRegCircle hρ _ ht ξ)) k‖ ≤
        ‖circleCoeff (loopMasterPullback (loopMasterLength (ell N)) ξ.val) k‖ := by
      rw [circleCoeff_pullback_cltRegCircle, norm_mul]
      apply (mul_le_mul_of_nonneg_left _ (norm_nonneg _)).trans_eq (mul_one _)
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        mollifierFT_abs_le_one hρ.isCircleMollifier
          (t * k / (loopMasterLength (ell N)).val)
    rcases hcases with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact hc.trans (le_mul_of_one_le_left (norm_nonneg _) (by norm_num))
    · change ‖circleCoeff (fun z => loopMasterPullback (loopMasterLength (ell N)) ξ.val z -
          loopMasterPullback (loopMasterLength (ell N)) (cltRegCircle hρ _ ht ξ) z) k‖ ≤ _
      rw [circleCoeff_sub_of_memLp _ _ (loopMasterPullback_memLp _ ξ)
        (loopMasterPullback_memLp _ (loopMasterLengthTest _ _ (cltRegCircle_contDiff hρ _ ht ξ)))]
      exact (norm_sub_le _ _).trans (by linarith)

/-- Microscopic regularization error contracts uniformly across both
families. This includes every positive optional radius, without a
small-radius threshold or additional support hypothesis. -/
theorem auxiliary_family_smoothing_le (P : Parameters) (p : Profile)
    (ell : Scales) (N : ℕ+) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (r : ℝ) (v : Profile)
    (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
    (hv : OptimalScalingTest p ell N hρ r v f) :
    let ξ := (⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ :
      {f : Circle (loopMasterLength (ell N)) → ℝ //
        MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
    scaledVariance P (ell N) (subCircleL2 f (mixedReg hρ N (ell N) f)) ≤
      4 * scaledVariance P (ell N) (subCircleL2 ξ (mixedReg hρ N (ell N) ξ)) := by
  intro ξ
  apply auxiliary_scaledVariance_le_four
  intro k
  rw [auxiliary_error_coeff, auxiliary_error_coeff, norm_mul, norm_mul]
  calc _ ≤ (2 * ‖circleCoeff (loopMasterPullback (loopMasterLength (ell N)) ξ.val) k‖) * _ :=
      mul_le_mul_of_nonneg_right (auxiliary_family_coeff_le p ell N hρ r v f hv k) (norm_nonneg _)
    _ = _ := by ring

/-- The complete smoothing estimate needed by Proposition 5.6, uniformly
over the families, with the constant before every family member and scale. -/
theorem auxiliary_smoothing_family_bound (P : Parameters) (p : Profile)
    (α : ℝ) (d : TestData) (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales, Admissible P p ell α d →
      ∀ N : ℕ+, 1 ≤ cltK N (ell N) → ∀ (r : ℝ) (v : Profile)
        (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        scaledVariance P (ell N) (subCircleL2 f (mixedReg hρ N (ell N) f)) ≤
          ENNReal.ofReal (C * cltK N (ell N) ^ (2 * α + ε - P.val.2)) := by
  obtain ⟨C, hC, hb⟩ := auxiliary_smoothing_bound P p α d ρ hρ ε hε
  refine ⟨4 * C, by positivity, fun ell hadm N hK r v f hv => ?_⟩
  apply (auxiliary_family_smoothing_le P p ell N hρ r v f hv).trans
  calc _ ≤ 4 * ENNReal.ofReal (C * cltK N (ell N) ^ (2 * α + ε - P.val.2)) :=
      mul_le_mul_of_nonneg_left (hb ell hadm N hK) zero_le
    _ = _ := by rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]; congr 1; ring

end Riesz1.Internal

end
