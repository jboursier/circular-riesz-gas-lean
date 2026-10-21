/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopMasterConvolution
public import Riesz1.Frozen.TransportCoeffs
import all Riesz1.Kernel.MeanFieldEnergyFourier

/-!
# Derivative of the transport

The unit-circle coefficient calculation in Proposition 5.5.
The transport is specified by `transportCoeffs`, rather than by a
convolution equation imposed as an additional hypothesis.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ContDiff Real

namespace Riesz1

/-- Smooth real circle functions, on the integrable Fourier carrier. -/
@[reducible] noncomputable def loopMasterTest (ξ : UnitAddCircle → ℝ) (hξ : IsSmoothCircle ξ) :
    {f : Circle unitLength → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength unitLength)} := by
  have hc : Continuous ξ :=
    (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 hξ.continuous
  haveI : IsFiniteMeasure (arclength unitLength) := by
    unfold arclength
    infer_instance
  refine ⟨fun z => ξ z, ?_⟩
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine MemLp.of_bound (Complex.continuous_ofReal.comp hc).aestronglyMeasurable C ?_
  exact Eventually.of_forall fun z => by
    rw [Complex.norm_real]
    exact hC z (mem_univ _)

/-- The derivative of a smooth circle function, as a circle function. -/
noncomputable def loopMasterCircleDeriv (ψ : UnitAddCircle → ℝ) (_hψ : IsSmoothCircle ψ) :
    UnitAddCircle → ℝ :=
  (show Function.Periodic (deriv fun u : ℝ => ψ (u : UnitAddCircle)) 1 from
    deriv_add_one_of_periodic (F := fun u : ℝ => ψ (u : UnitAddCircle)) (lift_periodic ψ)).lift

lemma loopMasterCircleDeriv_coe (ψ : UnitAddCircle → ℝ) (hψ : IsSmoothCircle ψ) (x : ℝ) :
    loopMasterCircleDeriv ψ hψ (x : UnitAddCircle) = deriv (fun u : ℝ => ψ (u : UnitAddCircle)) x :=
  (show Function.Periodic (deriv fun u : ℝ => ψ (u : UnitAddCircle)) 1 from
    deriv_add_one_of_periodic (F := fun u : ℝ => ψ (u : UnitAddCircle)) (lift_periodic ψ)).lift_coe x

lemma loopMasterCircleDeriv_smooth {ψ : UnitAddCircle → ℝ} (hψ : IsSmoothCircle ψ) :
    IsSmoothCircle (loopMasterCircleDeriv ψ hψ) := by
  unfold IsSmoothCircle
  simp_rw [loopMasterCircleDeriv_coe]
  exact (contDiff_infty_iff_deriv.mp hψ).2

lemma circleCoeff_loopMasterCircleDeriv {ψ : UnitAddCircle → ℝ} (hψ : IsSmoothCircle ψ) (k : ℤ) :
    circleCoeff (loopMasterCircleDeriv ψ hψ) k = (2 * π * I * (k : ℂ)) * circleCoeff ψ k := by
  rw [circleCoeff, fourierCoeff_eq_lineCoeff]
  simp_rw [loopMasterCircleDeriv_coe]
  rw [lineCoeff_deriv (hψ.of_le (by simp)) (lift_periodic ψ), circleCoeff, fourierCoeff_eq_lineCoeff]

/-- Fourier coefficients of the derivative of the transport. -/
lemma loopMaster_transport_derivative_coeff (P : Parameters) (ξ ψ : UnitAddCircle → ℝ)
    (hξ : IsSmoothCircle ξ) (hψ : IsSmoothCircle ψ)
    (htransport : ∀ k, circleCoeff ψ k = transportCoeffs P unitLength (loopMasterTest ξ hξ) k)
    (k : ℤ) : circleCoeff (loopMasterCircleDeriv ψ hψ) k =
      (-(1 / (2 * P.val.1 * rieszConstant (parametersExponent P))) : ℂ) *
        fractionalLaplacianCoeffs unitLength ((1 - P.val.2) / 2) (circleCoeff ξ) k := by
  rw [circleCoeff_loopMasterCircleDeriv hψ, htransport]
  unfold transportCoeffs
  rw [fractionalLaplacianCoeffs_unit]
  by_cases hk : k = 0
  · subst k
    simp
  · rw [ite_eq_right hk, ite_eq_right hk]
    change (2 * π * I * (k : ℂ)) *
      (-((|2 * π * (k : ℝ) / 1| ^ (1 - P.val.2) : ℝ) : ℂ) /
        ((2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) *
          (2 * π * I * (k : ℂ) / 1)) * circleCoeff ξ k) = _
    simp only [div_one, show 2 * ((1 - P.val.2) / 2) = 1 - P.val.2 by ring]
    have hf : (2 * π * I * (k : ℂ)) ≠ 0 := by
      have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) Complex.I_ne_zero) hkc
    have hc : (2 * P.val.1 * rieszConstant (parametersExponent P) : ℂ) ≠ 0 := by
      have hs : 0 < rieszConstant (parametersExponent P) := by
        unfold rieszConstant
        exact div_pos (mul_pos (mul_pos (by positivity) (Real.sqrt_pos.2 Real.pi_pos))
          (Real.Gamma_pos_of_pos (by linarith [(parametersExponent P).property.2])))
          (Real.Gamma_pos_of_pos (by linarith [(parametersExponent P).property.1]))
      exact mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.2 P.property.1.ne')) (Complex.ofReal_ne_zero.2 hs.ne')
    push_cast
    field_simp

/-- The derivative formula follows from the transport coefficients, pointwise.
This is the `ℓ = 1` characterization in Proposition 5.5. -/
theorem loopMaster_transport_derivative_unit (P : Parameters) (ξ ψ : UnitAddCircle → ℝ)
    (hξ : IsSmoothCircle ξ) (hψ : IsSmoothCircle ψ)
    (htransport : ∀ k, circleCoeff ψ k = transportCoeffs P unitLength (loopMasterTest ξ hξ) k)
    (x : ℝ) :
    ((deriv (fun u : ℝ => ψ (u : UnitAddCircle)) x : ℝ) : ℂ) =
      (-(1 / (2 * P.val.1 * rieszConstant (parametersExponent P))) : ℂ) *
        fracLapSeries ((1 - P.val.2) / 2) ξ hξ x := by
  have hi := (hasSum_circleCoeff (loopMasterCircleDeriv ψ hψ)
    (loopMasterCircleDeriv_smooth hψ) x).tsum_eq
  rw [loopMasterCircleDeriv_coe] at hi
  rw [← hi]
  unfold fracLapSeries
  rw [← tsum_mul_left]
  exact tsum_congr fun k => by rw [loopMaster_transport_derivative_coeff P ξ ψ hξ hψ htransport]; ring

end Riesz1

end
