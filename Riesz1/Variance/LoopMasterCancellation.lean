/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopMasterTransport
import all Riesz1.Kernel.MeanFieldEnergyFourier
import all Mathlib.Basic.Complex.Basic
import all Mathlib.Basic.Real.Basic

/-!
# Fourier expansion of the transport convolution

The convolution calculation used by Proposition 5.5.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ContDiff Real

namespace Riesz1

/-- Expanding a smooth factor inside a convolution with an integrable kernel. -/
lemma loopMaster_hasSum_convolution (f : UnitAddCircle → ℝ) (hf : IsSmoothCircle f)
    (g : ℝ → ℝ) (hg : IntervalIntegrable g volume 0 1) (x : ℝ) :
    HasSum (fun k : ℤ => (fourier k (x : UnitAddCircle) * circleCoeff f k) *
      lineCoeff (fun u => (g u : ℂ)) k)
      (∫ u in (0 : ℝ)..1, (g u : ℂ) * (f ((x - u : ℝ) : UnitAddCircle) : ℂ)) := by
  have hs : Summable fun k : ℤ => ‖circleCoeff f k‖ := by
    simpa only [pow_zero, one_mul] using summable_norm_two_pi_pow_mul f hf 0
  have hb : IntervalIntegrable (fun u => ∑' k : ℤ, ‖g u‖ * ‖circleCoeff f k‖) volume 0 1 := by
    simp_rw [tsum_mul_left]
    exact hg.norm.mul_const _
  have hi := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0)
    (b := 1)
    (F := fun (k : ℤ) (u : ℝ) => (g u : ℂ) *
      (fourier k ((x - u : ℝ) : UnitAddCircle) * circleCoeff f k))
    (f := fun u : ℝ => (g u : ℂ) * (f ((x - u : ℝ) : UnitAddCircle) : ℂ))
    (bound := fun (k : ℤ) (u : ℝ) => ‖g u‖ * ‖circleCoeff f k‖)
    (fun k => by
      rw [uIoc_of_le zero_le_one]
      convert
        ((Complex.continuous_ofReal.comp_aestronglyMeasurable hg.aestronglyMeasurable).mul
          ((by fun_prop : Continuous fun u : ℝ => fourier k ((x - u : ℝ) : UnitAddCircle) *
            circleCoeff f k).aestronglyMeasurable)) using 1)
    (fun k => Eventually.of_forall fun u _ => by
      rw [norm_mul, norm_mul, Complex.norm_real, norm_fourier_coe, one_mul])
    (Eventually.of_forall fun u _ => hs.mul_left ‖g u‖) hb
    (Eventually.of_forall fun u _ => (hasSum_circleCoeff f hf (x - u)).mul_left (g u : ℂ))
  have hm (k : ℤ) (u : ℝ) : fourier k ((x - u : ℝ) : UnitAddCircle) =
      fourier k (x : UnitAddCircle) * Complex.exp (-(2 * π * I * (k : ℂ) * u)) := by
    simp only [fourier_coe_apply, Complex.ofReal_one, div_one]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have ht (k : ℤ) : (∫ u in (0 : ℝ)..1, (g u : ℂ) *
      (fourier k ((x - u : ℝ) : UnitAddCircle) * circleCoeff f k)) =
      (fourier k (x : UnitAddCircle) * circleCoeff f k) *
        lineCoeff (fun u => (g u : ℂ)) k := by
    simp_rw [hm]
    unfold lineCoeff
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun u _ => by ring
  simpa only [ht] using hi

/-- The defining Fourier multiplier cancels the Riesz convolution. -/
theorem loopMaster_transport_pv_unit (P : Parameters) (ξ ψ : UnitAddCircle → ℝ)
    (hξ : IsSmoothCircle ξ) (hψ : IsSmoothCircle ψ)
    (htransport : ∀ k, circleCoeff ψ k = transportCoeffs P unitLength (loopMasterTest ξ hξ) k)
    (x : ℝ) :
    -2 * P.val.1 * pvConv P.val.2 (fun u : ℝ => ψ (u : UnitAddCircle)) x =
      ξ (x : UnitAddCircle) - ∫ u in (0 : ℝ)..1, ξ (u : UnitAddCircle) := by
  let s := parametersExponent P
  have hgk (k : ℤ) : lineCoeff (fun u => (hurwitzKernel s.val u : ℂ)) k =
      if k = 0 then 0 else
        ((rieszConstant s * (2 * π * |(k : ℝ)|) ^ (s.val - 1) : ℝ) : ℂ) := by
    have h := fourierCoeff_rieszRepresentative s k
    rw [fourierCoeff_eq_lineCoeff] at h
    exact h
  have hcs : 0 < rieszConstant s := by
    unfold rieszConstant
    exact div_pos (mul_pos (mul_pos (by positivity) (Real.sqrt_pos.2 Real.pi_pos))
      (Real.Gamma_pos_of_pos (by linarith [s.property.2])))
      (Real.Gamma_pos_of_pos (by linarith [s.property.1]))
  have hterm (k : ℤ) : (-2 * P.val.1 : ℂ) *
      (circleCoeff (loopMasterCircleDeriv ψ hψ) k * lineCoeff (fun u => (hurwitzKernel s.val u : ℂ)) k) =
      if k = 0 then 0 else circleCoeff ξ k := by
    rw [hgk, loopMaster_transport_derivative_coeff P ξ ψ hξ hψ htransport,
      fractionalLaplacianCoeffs_unit]
    by_cases hk : k = 0
    · subst k
      simp
    · rw [ite_eq_right hk, ite_eq_right hk, ite_eq_right hk]
      have ha : 0 < |2 * π * (k : ℝ)| := by
        exact abs_pos.mpr (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
          (by exact_mod_cast hk))
      have hp : |2 * π * (k : ℝ)| ^ (1 - s.val) * |2 * π * (k : ℝ)| ^ (s.val - 1) = 1 := by
        rw [← Real.rpow_add ha, show 1 - s.val + (s.val - 1) = 0 by ring, Real.rpow_zero]
      have hpc : ((|2 * π * (k : ℝ)| ^ (1 - s.val) : ℝ) : ℂ) *
          ((|2 * π * (k : ℝ)| ^ (s.val - 1) : ℝ) : ℂ) = 1 := by
        exact_mod_cast hp
      have hab : 2 * π * |(k : ℝ)| = |2 * π * (k : ℝ)| := by
        rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_two]
      rw [hab, show 2 * ((1 - P.val.2) / 2) = 1 - P.val.2 by ring]
      change (-2 * P.val.1 : ℂ) *
        ((-(1 / (2 * P.val.1 * rieszConstant s)) *
          (((|2 * π * (k : ℝ)| ^ (1 - s.val) : ℝ) : ℂ) * circleCoeff ξ k)) *
          ((rieszConstant s * |2 * π * (k : ℝ)| ^ (s.val - 1) : ℝ) : ℂ)) = _
      push_cast
      have hb : (P.val.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 P.property.1.ne'
      have hc : (rieszConstant s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hcs.ne'
      field_simp
      linear_combination (circleCoeff ξ k) * hpc
  have hi := (loopMaster_hasSum_convolution (loopMasterCircleDeriv ψ hψ)
    (loopMasterCircleDeriv_smooth hψ) (hurwitzKernel s.val)
    (intervalIntegrable_hurwitzKernel s.val s.property.1 s.property.2) x).mul_left (-2 * P.val.1 : ℂ)
  have hval : (∫ u in (0 : ℝ)..1, (hurwitzKernel s.val u : ℂ) *
      (loopMasterCircleDeriv ψ hψ ((x - u : ℝ) : UnitAddCircle) : ℂ)) =
      ((pvConv s.val (fun u : ℝ => ψ (u : UnitAddCircle)) x : ℝ) : ℂ) := by
    rw [pvConv_eq_integral_deriv s.property.1 s.property.2 hψ (lift_periodic ψ)]
    simp_rw [loopMasterCircleDeriv_coe, ← Complex.ofReal_mul]
    exact intervalIntegral.integral_ofReal
  rw [hval] at hi
  have hterms : (fun k : ℤ => (-2 * P.val.1 : ℂ) *
      ((fourier k (x : UnitAddCircle) * circleCoeff (loopMasterCircleDeriv ψ hψ) k) *
        lineCoeff (fun u => (hurwitzKernel s.val u : ℂ)) k)) =
      fun k : ℤ => if k = 0 then 0 else fourier k (x : UnitAddCircle) * circleCoeff ξ k := by
    funext k
    have he := congrArg (fun z => fourier k (x : UnitAddCircle) * z) (hterm k)
    convert he using 1
    · ring
    · split <;> simp_all
  rw [hterms] at hi
  have he : (∑' k : ℤ, if k = 0 then 0 else fourier k (x : UnitAddCircle) * circleCoeff ξ k) =
      (ξ (x : UnitAddCircle) : ℂ) - circleCoeff ξ 0 := by
    have hs := (hasSum_circleCoeff ξ hξ x).summable
    have h := hs.tsum_eq_add_tsum_ite 0
    rw [(hasSum_circleCoeff ξ hξ x).tsum_eq] at h
    simp only [fourier_zero, one_mul] at h
    linear_combination -h
  have hc0 : circleCoeff ξ 0 = ((∫ u in (0 : ℝ)..1, ξ (u : UnitAddCircle) : ℝ) : ℂ) := by
    rw [circleCoeff_eq_intervalIntegral]
    simp only [neg_zero, Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul]
    exact intervalIntegral.integral_ofReal
  have heq := hi.tsum_eq.symm.trans (he.trans (by rw [hc0]))
  exact_mod_cast heq

end Riesz1

end
