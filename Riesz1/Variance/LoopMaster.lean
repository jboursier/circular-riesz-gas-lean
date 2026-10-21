/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopScaleDifferential
public import Riesz1.Variance.LoopMasterCancellation
public import Riesz1.Variance.LoopMasterScaling
import all Riesz1.Variance.LoopForce
import all Riesz1.Variance.LoopForceKernel
import all Mathlib.Basic.Real.Basic

/-!
# Transport equation at every scale

Assembly of Proposition 5.5, with the operator
written in lifted coordinates as `β ∇H · ∇Φ - ΔΦ`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ContDiff Real

namespace Riesz1

/-- A smooth function with nonzero period is globally Lipschitz. -/
lemma loopMaster_lipschitz {T : ℝ} (hT : T ≠ 0) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f T) : ∃ C : NNReal, LipschitzWith C f := by
  have hdper : Function.Periodic (deriv f) T := by
    intro u
    have he : (fun v => f (v + T)) = f := funext hp
    have hd := ((hf.differentiable (by simp) (u + T)).hasDerivAt.comp u
      ((hasDerivAt_id u).add_const T)).deriv
    change deriv (fun v => f (v + T)) u = deriv f (u + T) * 1 at hd
    rw [he, mul_one] at hd
    exact hd.symm
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (hdper.isBounded_of_continuous hT (hf.continuous_deriv (by simp)))
  refine ⟨⟨|C|, abs_nonneg C⟩, lipschitzWith_of_nnnorm_deriv_le
    (hf.differentiable (by simp)) fun u => ?_⟩
  change ‖deriv f u‖ ≤ |C|
  exact (hC _ ⟨u, rfl⟩).trans (le_abs_self C)

/-- The length `ℓ⁻¹` of the profile circle. -/
noncomputable def loopMasterLength (ℓ : Ioc (0 : ℝ) 1) : Length := ⟨ℓ.val⁻¹, inv_pos.mpr ℓ.property.1⟩

/-- A smooth real profile on the long circle, on the loop's Lipschitz carrier. -/
@[reducible] noncomputable def loopMasterProfile (ℓ : Ioc (0 : ℝ) 1)
    (ψ : Circle (loopMasterLength ℓ) → ℝ)
    (hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle (loopMasterLength ℓ)))) :
    LoopScaleProfile ℓ.val := by
  have hp : Function.Periodic (fun u : ℝ => ψ (u : Circle (loopMasterLength ℓ))) ℓ.val⁻¹ :=
    fun u => by
      change ψ ((u + (loopMasterLength ℓ).val : ℝ) : Circle (loopMasterLength ℓ)) = _
      rw [AddCircle.coe_add_period]
  exact ⟨_, hp, loopMaster_lipschitz (inv_ne_zero ℓ.property.1.ne') hψ hp⟩

lemma pvConv_const_mul (s : RieszExponent) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f 1) (c x : ℝ) :
    pvConv s.val (fun u => c * f u) x = c * pvConv s.val f x := by
  have hcp : Function.Periodic (fun u => c * f u) 1 := fun u => congrArg (c * ·) (hp u)
  rw [pvConv_eq s.property.1 s.property.2 (contDiff_const.mul hf) hcp,
    pvConv_eq s.property.1 s.property.2 hf hp, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun u _ => by unfold pvIntegrand; ring

/-- The long-circle transport pulls back to `ℓ^(s-1)` times the diagonal field. -/
lemma loopMaster_transport_field (P : Parameters) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : Circle (loopMasterLength ℓ) → ℝ) (u : ℝ) :
    loopMasterTransportPullback P (loopMasterLength ℓ) ψ (u : UnitAddCircle) =
      ℓ.val ^ (P.val.2 - 1) * loopScaleField ℓ.val
        (fun v => ψ (v : Circle (loopMasterLength ℓ))) u := by
  unfold loopMasterTransportPullback
  rw [loopMasterPullback_coe]
  change (ℓ.val⁻¹) ^ (-P.val.2) * ψ ((u * ℓ.val⁻¹ : ℝ) : Circle (loopMasterLength ℓ)) = _
  rw [Real.inv_rpow ℓ.property.1.le, ← Real.rpow_neg ℓ.property.1.le, neg_neg,
    Real.rpow_sub_one ℓ.property.1.ne']
  unfold loopScaleField
  rw [div_eq_mul_inv]
  field_simp [ℓ.property.1.ne']

/-- The microscopic force of the transport cancels the centered test at every scale. -/
theorem loopMaster_transport_cancellation (P : Parameters) (ℓ : Ioc (0 : ℝ) 1)
    (ξ ψ : Circle (loopMasterLength ℓ) → ℝ)
    (hξ : ContDiff ℝ ∞ (fun u : ℝ => ξ (u : Circle (loopMasterLength ℓ))))
    (hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle (loopMasterLength ℓ))))
    (htransport : ∀ k, coeff (loopMasterLength ℓ)
      ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
      transportCoeffs P (loopMasterLength ℓ) (loopMasterLengthTest _ ξ hξ) k)
    (N : ℕ) (x : Fin N → ℝ) :
    -2 * P.val.1 * ℓ.val ^ (P.val.2 - 1) *
      fluctIntegral (pvConv P.val.2 (loopScaleField ℓ.val (loopMasterProfile ℓ ψ hψ).val)) N x =
      fluctIntegral (fun u => ξ ((u / ℓ.val : ℝ) : Circle (loopMasterLength ℓ))) N x := by
  let L := loopMasterLength ℓ
  let ξ1 := loopMasterPullback L ξ
  let ψ1 := loopMasterTransportPullback P L ψ
  have hξ1 : IsSmoothCircle ξ1 := loopMasterPullback_smooth L ξ hξ
  have hψ1 : IsSmoothCircle ψ1 :=
    contDiff_const.mul (loopMasterPullback_smooth L ψ hψ)
  have hp := loopMaster_transport_pv_unit P ξ1 ψ1 hξ1 hψ1
    (loopMaster_transport_pullback P L ξ ψ hξ hψ htransport)
  let q := loopScaleField ℓ.val (loopMasterProfile ℓ ψ hψ).val
  have hq : ContDiff ℝ ∞ q := loopScaleField_contDiff hψ
  have hqp : Function.Periodic q 1 := loopScaleField_periodic (loopMasterProfile ℓ ψ hψ).property.1
  have hψeq : (fun u : ℝ => ψ1 (u : UnitAddCircle)) = fun u => ℓ.val ^ (P.val.2 - 1) * q u :=
    funext (loopMaster_transport_field P ℓ ψ)
  have hξeq : (fun u : ℝ => ξ1 (u : UnitAddCircle)) =
      fun u => ξ ((u / ℓ.val : ℝ) : Circle L) := by
    funext u
    dsimp only [ξ1]
    rw [loopMasterPullback_coe]
    congr 2
  have hp' (u : ℝ) : -2 * P.val.1 * ℓ.val ^ (P.val.2 - 1) * pvConv P.val.2 q u =
      ξ ((u / ℓ.val : ℝ) : Circle L) - ∫ v in (0 : ℝ)..1, ξ ((v / ℓ.val : ℝ) : Circle L) := by
    have hh := hp u
    rw [hψeq] at hh
    have he : pvConv P.val.2 (fun v => ℓ.val ^ (P.val.2 - 1) * q v) u =
        ℓ.val ^ (P.val.2 - 1) * pvConv P.val.2 q u :=
      pvConv_const_mul (parametersExponent P) hq hqp _ _
    rw [he] at hh
    change -2 * P.val.1 * (ℓ.val ^ (P.val.2 - 1) * pvConv P.val.2 q u) =
      (fun v : ℝ => ξ1 (v : UnitAddCircle)) u -
        ∫ v in (0 : ℝ)..1, (fun v : ℝ => ξ1 (v : UnitAddCircle)) v at hh
    rw [hξeq] at hh
    simpa only [mul_assoc] using hh
  rw [fluctIntegral_pvConv P.property.2.1 P.property.2.2 hq hqp]
  unfold fluctIntegral
  rw [Finset.mul_sum]
  simp_rw [hp']
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Proposition 5.5 at every lift without collisions.
The transport is identified by the Fourier coefficients on the circle of length `ℓ⁻¹`. -/
theorem loop_equations_master (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ξ ψ : Circle (loopMasterLength ℓ) → ℝ)
    (hξ : ContDiff ℝ ∞ (fun u : ℝ => ξ (u : Circle (loopMasterLength ℓ))))
    (hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle (loopMasterLength ℓ))))
    (htransport : ∀ k, coeff (loopMasterLength ℓ)
      ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
      transportCoeffs P (loopMasterLength ℓ) (loopMasterLengthTest _ ξ hξ) k)
    (x : Fin (N : ℕ) → ℝ)
    (hx : ∀ i j, i ≠ j → ((x i - x j : ℝ) : UnitAddCircle) ≠ 0) :
    let a := ((N : ℝ) * ℓ.val) ^ (P.val.2 - 1)
    let Ψ := loopMasterProfile ℓ ψ hψ
    P.val.1 * (∑ k : Fin (N : ℕ), partialDeriv (energyLift (parametersExponent P) N) k x *
        partialDeriv (loopScalePotential ℓ a Ψ N) k x)
      - laplacian (loopScalePotential ℓ a Ψ N) x
      - fluctIntegral (fun u => ξ ((u / ℓ.val : ℝ) : Circle (loopMasterLength ℓ))) N x =
    a * (P.val.1 * loopScale (parametersExponent P) N ℓ Ψ x hx
      - fluctIntegral (fun u => deriv Ψ.val (u / ℓ.val)) N x) := by
  dsimp only
  rw [loopScale_force_expansion (parametersExponent P) N ℓ _ P.val.1 _ hψ x hx]
  have hN : (0 : ℝ) < N := by exact_mod_cast N.property
  have he : ((N : ℝ) * ℓ.val) ^ (P.val.2 - 1) * (N : ℝ) ^ (1 - P.val.2) =
      ℓ.val ^ (P.val.2 - 1) := by
    rw [Real.mul_rpow hN.le ℓ.property.1.le]
    calc (N : ℝ) ^ (P.val.2 - 1) * ℓ.val ^ (P.val.2 - 1) * (N : ℝ) ^ (1 - P.val.2) =
        ((N : ℝ) ^ (P.val.2 - 1) * (N : ℝ) ^ (1 - P.val.2)) * ℓ.val ^ (P.val.2 - 1) := by ring
      _ = ℓ.val ^ (P.val.2 - 1) := by
        rw [← Real.rpow_add hN, show P.val.2 - 1 + (1 - P.val.2) = 0 by ring,
          Real.rpow_zero, one_mul]
  have hc := loopMaster_transport_cancellation P ℓ ξ ψ hξ hψ htransport N x
  have hec := congrArg (fun t : ℝ => -2 * P.val.1 * t *
    fluctIntegral (pvConv P.val.2 (loopScaleField ℓ.val (loopMasterProfile ℓ ψ hψ).val)) N x) he
  change ((N : ℝ) * ℓ.val) ^ (P.val.2 - 1) *
      (P.val.1 * loopScale (parametersExponent P) N ℓ (loopMasterProfile ℓ ψ hψ) x hx -
        2 * P.val.1 * (N : ℝ) ^ (1 - P.val.2) *
          fluctIntegral (pvConv P.val.2 (loopScaleField ℓ.val (loopMasterProfile ℓ ψ hψ).val)) N x -
        fluctIntegral (fun u => deriv (loopMasterProfile ℓ ψ hψ).val (u / ℓ.val)) N x) -
      fluctIntegral (fun u => ξ ((u / ℓ.val : ℝ) : Circle (loopMasterLength ℓ))) N x = _
  linear_combination hc + hec

/-- The pointwise derivative characterization in Proposition 5.5. -/
theorem loopMaster_transport_derivative (P : Parameters) (ℓ : Ioc (0 : ℝ) 1)
    (ξ ψ : Circle (loopMasterLength ℓ) → ℝ)
    (hξ : ContDiff ℝ ∞ (fun u : ℝ => ξ (u : Circle (loopMasterLength ℓ))))
    (hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle (loopMasterLength ℓ))))
    (htransport : ∀ k, coeff (loopMasterLength ℓ)
      ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
      transportCoeffs P (loopMasterLength ℓ) (loopMasterLengthTest _ ξ hξ) k)
    (u : ℝ) :
    ((deriv (fun v : ℝ => ψ (v : Circle (loopMasterLength ℓ))) u : ℝ) : ℂ) =
      (-(1 / (2 * P.val.1 * rieszConstant (parametersExponent P))) : ℂ) *
        ((ℓ.val ^ (1 - P.val.2) : ℝ) : ℂ) *
        fracLapSeries ((1 - P.val.2) / 2) (loopMasterPullback (loopMasterLength ℓ) ξ)
          (loopMasterPullback_smooth _ ξ hξ) (ℓ.val * u) := by
  let L := loopMasterLength ℓ
  let ξ1 := loopMasterPullback L ξ
  let ψ1 := loopMasterTransportPullback P L ψ
  have hξ1 : IsSmoothCircle ξ1 := loopMasterPullback_smooth L ξ hξ
  have hψ1 : IsSmoothCircle ψ1 := contDiff_const.mul (loopMasterPullback_smooth L ψ hψ)
  have hd := loopMaster_transport_derivative_unit P ξ1 ψ1 hξ1 hψ1
    (loopMaster_transport_pullback P L ξ ψ hξ hψ htransport) (ℓ.val * u)
  have he : (fun v : ℝ => ψ1 (v : UnitAddCircle)) = fun v => ℓ.val ^ (P.val.2 - 1) *
      loopScaleField ℓ.val (fun w => ψ (w : Circle L)) v :=
    funext (loopMaster_transport_field P ℓ ψ)
  rw [he, deriv_const_mul_field, deriv_loopScaleField ℓ hψ, mul_div_cancel_left₀ u ℓ.property.1.ne'] at hd
  have hp : ℓ.val ^ (1 - P.val.2) * ℓ.val ^ (P.val.2 - 1) = 1 := by
    rw [← Real.rpow_add ℓ.property.1, show 1 - P.val.2 + (P.val.2 - 1) = 0 by ring, Real.rpow_zero]
  have hpc := congrArg (fun r : ℝ => (r : ℂ)) hp
  push_cast at hd hpc
  have hh := congrArg (fun z : ℂ => ((ℓ.val ^ (1 - P.val.2) : ℝ) : ℂ) * z) hd
  dsimp only [ξ1] at hh
  linear_combination hh -
    (((deriv (fun v : ℝ => ψ (v : Circle L)) u : ℝ) : ℂ)) * hpc

end Riesz1

end
