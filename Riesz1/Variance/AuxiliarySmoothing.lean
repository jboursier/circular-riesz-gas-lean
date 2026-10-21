/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.SmoothingVariance
public import Riesz1.Variance.AuxiliaryMixedProfileBridge
import all Riesz1.CLT.IdentityDefs
import all Riesz1.ToMathlib.Mollifier.RegularizationSobolev
import all Riesz1.Variance.LoopMaster

/-!
# The smoothing term in the reduced variance expansion

The analytic smoothing estimate of Proposition 5.6, on the actual
`mixedReg` object. The profile bridge is proved before converting the finite
extended seminorm to a real number. No probabilistic input is used.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace Riesz1.Internal

/-- The scaled lift of a regularization is its circle pullback. -/
theorem auxiliary_pullback_reg {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (a : Scale)
    {h : ℝ} (hh : 0 < h)
    (f : {f : Circle (loopMasterLength a) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength a))}) :
    loopMasterPullback (loopMasterLength a) (cltRegCircle hρ _ hh f) =
      cltScaledLift hρ a hh f := by
  funext z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [loopMasterPullback_coe]
  change _ = (cltScaledFun_periodic hρ a hh f).lift (x : UnitAddCircle)
  rw [Function.Periodic.lift_coe]
  rfl

/-- Profile bridge for the error between the periodized profile and its microscopic
regularization, including the representative discrepancy at the antipode. -/
theorem auxiliary_scaledVariance_error_eq (P : Parameters) (p : Profile)
    (N : ℕ+) (a : Scale) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
    let ξ := (⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ :
      {f : Circle (loopMasterLength a) → ℝ //
        MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength a))})
    scaledVariance P a (subCircleL2 ξ (mixedReg hρ N a ξ)) =
      cltVariance P a (subL2
        ⟨(fun x => (testAtScale p a x : ℂ)), testAtScaleL2 p a⟩
        ⟨(fun x => (cltScaledLift hρ a (inv_pos.mpr (cltK_pos N a)) ξ x : ℂ)),
          cltScaledLift_memLp hρ a _ ξ⟩) := by
  intro ξ
  unfold scaledVariance cltVariance
  congr 1
  apply circleSobolevSq_congr_ae
  filter_upwards [testAtScale_ae_eq_loopMasterPullback_periodizedProfile p a] with z hz
  simp only [loopMasterPullback_subCircleL2, Complex.ofReal_sub]
  rw [hz]
  congr 1
  exact congrArg Complex.ofReal
    (congrFun (auxiliary_pullback_reg hρ a (inv_pos.mpr (cltK_pos N a)) ξ) z)

/-- The smoothing-seminorm term in Proposition 5.6. The constant precedes
all scale sequences and particle numbers, and the estimate is extended-real. -/
theorem auxiliary_smoothing_bound (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ell : Scales), Admissible P p ell α d → ∀ N : ℕ+,
      1 ≤ cltK N (ell N) →
      let ξ := (⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ :
        {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
      scaledVariance P (ell N) (subCircleL2 ξ (mixedReg hρ N (ell N) ξ)) ≤
        ENNReal.ofReal (C * cltK N (ell N) ^ (2 * α + ε - P.val.2)) := by
  obtain ⟨C, hC, hb⟩ := clt_smoothing_variance P p α d ρ hρ (ε / 2) (by positivity)
  refine ⟨C ^ 2, sq_pos_of_pos hC, fun ell hadm N hK => ?_⟩
  dsimp only
  rw [auxiliary_scaledVariance_error_eq]
  have hK0 := cltK_pos N (ell N)
  have hh : (cltK N (ell N))⁻¹ ≤ 1 := (inv_le_one₀ hK0).mpr hK
  obtain ⟨hf, hs⟩ := hb ell hadm N _ (inv_pos.mpr hK0) hh
  apply (ENNReal.le_ofReal_iff_toReal_le hf.ne (by positivity)).2
  generalize hv : cltVariance P (ell N) _ = V at hf hs ⊢
  have hsq := Real.sq_sqrt (ENNReal.toReal_nonneg (a := V))
  have hb0 : 0 ≤ C * ((cltK N (ell N))⁻¹) ^ (P.val.2 / 2 - α - ε / 2) := by positivity
  have hp : (C * ((cltK N (ell N))⁻¹) ^ (P.val.2 / 2 - α - ε / 2)) ^ 2 =
      C ^ 2 * cltK N (ell N) ^ (2 * α + ε - P.val.2) := by
    rw [mul_pow, Real.inv_rpow hK0.le, ← Real.rpow_neg hK0.le]
    congr 1
    rw [← Real.rpow_two, ← Real.rpow_mul hK0.le]
    congr 1
    ring
  nlinarith [Real.sqrt_nonneg V.toReal]

end Riesz1.Internal

end
