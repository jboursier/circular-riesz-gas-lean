/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroLargeFourier
public import Riesz1.Variance.AuxiliarySmoothingFamily

/-!
# Microscopic Gibbs variance uniformly over the convolution families

The microscopic error has zero spatial mean. Its Fourier coefficients
for either family are dominated by twice those for the original test.
The common-rotation comparison therefore bounds its actual Gibbs
variance by four times the original microscopic variance, at every scale.
This is the family step of Lemma 5.3 and
Theorem 2.
-/

public section

open MeasureTheory Filter
open scoped ENNReal

namespace Riesz1.Internal

/-- Microscopic regularization preserves spatial mass exactly. -/
theorem regMicro_error_integral_zero {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (N : ℕ+) (a : Scale)
    (f : {f : Circle (loopMasterLength a) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength a))}) :
    (∫ z : UnitAddCircle, loopMasterPullback (loopMasterLength a)
      (subCircleL2 f (mixedReg hρ N a f)).val z) = 0 := by
  have hc := auxiliary_error_coeff hρ N a f 0
  simp only [Int.cast_zero, mul_zero, zero_div, mollifierFT_zero hρ.isCircleMollifier,
    Complex.ofReal_one, sub_self, mul_zero] at hc
  have he (u : UnitAddCircle → ℝ) : circleCoeff u 0 = ((∫ z, u z : ℝ) : ℂ) := by
    simp only [circleCoeff, fourierCoeff, neg_zero, fourier_zero, one_smul,
      ← volume_unitAddCircle_eq_haar, integral_complex_ofReal]
  rw [he] at hc
  exact Complex.ofReal_injective hc

/-- A microscopic error is already centered on the physical circle. -/
theorem regMicro_error_statistic {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (P : Parameters) (N : ℕ+) (a : Scale)
    (f : {f : Circle (loopMasterLength a) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength a))}) :
    mixedStat P N a (subCircleL2 f (mixedReg hρ N a f)) =
      linearStatistic (loopMasterPullback (loopMasterLength a)
        (subCircleL2 f (mixedReg hρ N a f)).val) := by
  funext X
  change linearStatistic _ X - (N : ℝ)*(∫ z : UnitAddCircle,
    loopMasterPullback (loopMasterLength a) (subCircleL2 f (mixedReg hρ N a f)).val z) = _
  rw [regMicro_error_integral_zero hρ, mul_zero, sub_zero]

/-- Both actual convolution families satisfy a Gibbs-variance bound
by four times the original microscopic error. The constant precedes
the family radius, and no admissibility or mark separation is needed. -/
theorem regMicroFamily_variance_le_four (P : Parameters) (p : Profile)
    (ell : Scales) (N : ℕ+) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (r : ℝ) (v : Profile)
    (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
    (hv : OptimalScalingTest p ell N hρ r v f) :
    let ξ := (⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ :
      {f : Circle (loopMasterLength (ell N)) → ℝ //
        MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
    ∀ (hE : Integrable (mixedStat P N (ell N) (subCircleL2 f (mixedReg hρ N (ell N) f)))
        (gibbsMeasure P N))
      (hξ : Integrable (mixedStat P N (ell N) (subCircleL2 ξ (mixedReg hρ N (ell N) ξ)))
        (gibbsMeasure P N)),
      variance (gibbsMeasure P N) _ hE ≤ 4*variance (gibbsMeasure P N) _ hξ := by
  intro ξ hE hξ
  let a := ell N
  let L := loopMasterLength a
  let E := subCircleL2 f (mixedReg hρ N a f)
  let E₀ := subCircleL2 ξ (mixedReg hρ N a ξ)
  have hc (k : ℤ) :
      ‖circleCoeff (loopMasterPullback L E.val) k‖ ≤
        2*‖circleCoeff (loopMasterPullback L E₀.val) k‖ := by
    dsimp only [E, E₀]
    rw [auxiliary_error_coeff, auxiliary_error_coeff, norm_mul, norm_mul]
    have hh := mul_le_mul_of_nonneg_right
      (auxiliary_family_coeff_le p ell N hρ r v f hv k)
      (norm_nonneg (1-(mollifierFT ρ ((cltK N a)⁻¹*k/L.val) : ℂ)))
    simpa only [mul_assoc] using hh
  have hh := regMicro_variance_le_of_circleCoeff P N
    (loopMasterPullback L E.val) (loopMasterPullback L E₀.val)
    (loopMasterPullback_memLp L E) (loopMasterPullback_memLp L E₀)
    (regMicro_error_integral_zero hρ N a f) (regMicro_error_integral_zero hρ N a ξ)
    4 (by norm_num) (fun k => by
      nlinarith [hc k, norm_nonneg (circleCoeff (loopMasterPullback L E.val) k),
        norm_nonneg (circleCoeff (loopMasterPullback L E₀.val) k)])
  have he := auxiliary_variance_congr hE
    ((memLp_linearStatistic P N (memLp_real_of_complex (loopMasterPullback_memLp L E))).integrable one_le_two)
    (Eventually.of_forall (congrFun (regMicro_error_statistic hρ P N a f)))
  have he₀ := auxiliary_variance_congr hξ
    ((memLp_linearStatistic P N (memLp_real_of_complex (loopMasterPullback_memLp L E₀))).integrable one_le_two)
    (Eventually.of_forall (congrFun (regMicro_error_statistic hρ P N a ξ)))
  rw [he, he₀]
  simpa only [show ENNReal.ofReal 4 = (4 : ℝ≥0∞) by norm_num] using hh

/-- Transfer any bound for the original microscopic error to an actual
family member. The factor four is independent of both radii and `N`. -/
theorem regMicroFamily_bound_of_original (P : Parameters) (p : Profile)
    (ell : Scales) (N : ℕ+) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (r : ℝ) (v : Profile)
    (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
    (hv : OptimalScalingTest p ell N hρ r v f) (A : ℝ)
    (hξ : Integrable (mixedStat P N (ell N)
      (subCircleL2 ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
        (mixedReg hρ N (ell N)
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩)))
      (gibbsMeasure P N))
    (hb : variance (gibbsMeasure P N) _ hξ ≤ ENNReal.ofReal A) :
    ∃ hE : MemLp (mixedStat P N (ell N) (subCircleL2 f (mixedReg hρ N (ell N) f))) 2
        (gibbsMeasure P N),
      variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤ ENNReal.ofReal (4*A) := by
  let E := subCircleL2 f (mixedReg hρ N (ell N) f)
  have hE : MemLp (mixedStat P N (ell N) E) 2 (gibbsMeasure P N) :=
    memLp_fluctuation P N (memLp_real_of_complex (loopMasterPullback_memLp _ E))
  refine ⟨hE, (regMicroFamily_variance_le_four P p ell N hρ r v f hv
    (hE.integrable one_le_two) hξ).trans ?_⟩
  calc
    _ ≤ 4*ENNReal.ofReal A := mul_le_mul_of_nonneg_left hb zero_le
    _ = _ := by
      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]

end Riesz1.Internal
