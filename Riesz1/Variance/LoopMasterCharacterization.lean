/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopMaster
public import Riesz1.Variance.LoopMasterExistence
public import Riesz1.Variance.LoopScaleIntegrability
import all Mathlib.Basic.Complex.Basic
import all Mathlib.Basic.Real.Basic

/-!
# Characterization and existence form of the master loop equation

Proposition 5.5: the derivative formula and zero
mean are equivalent to the transport coefficients. The final existence
form derives smoothness of the transport from smoothness of the test function.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ContDiff Real

namespace Riesz1

/-- The full "equivalently" clause of Proposition 5.5. -/
theorem loopMaster_transport_iff (P : Parameters) (ℓ : Ioc (0 : ℝ) 1)
    (ξ ψ : Circle (loopMasterLength ℓ) → ℝ)
    (hξ : ContDiff ℝ ∞ (fun u : ℝ => ξ (u : Circle (loopMasterLength ℓ))))
    (hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle (loopMasterLength ℓ)))) :
    (∀ k, coeff (loopMasterLength ℓ)
      ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
      transportCoeffs P (loopMasterLength ℓ) (loopMasterLengthTest _ ξ hξ) k) ↔
    ((∫ u in (0 : ℝ)..(loopMasterLength ℓ).val, ψ (u : Circle (loopMasterLength ℓ))) = 0 ∧
      ∀ u : ℝ, ((deriv (fun v : ℝ => ψ (v : Circle (loopMasterLength ℓ))) u : ℝ) : ℂ) =
        (-(1 / (2 * P.val.1 * rieszConstant (parametersExponent P))) : ℂ) *
          ((ℓ.val ^ (1 - P.val.2) : ℝ) : ℂ) *
          fracLapSeries ((1 - P.val.2) / 2) (loopMasterPullback (loopMasterLength ℓ) ξ)
            (loopMasterPullback_smooth _ ξ hξ) (ℓ.val * u)) := by
  constructor
  · intro hc
    exact ⟨loopMaster_transport_mean_zero P _ ξ ψ hξ hψ hc,
      loopMaster_transport_derivative P ℓ ξ ψ hξ hψ hc⟩
  · rintro ⟨hm, hd⟩
    obtain ⟨χ, hχ, hcχ⟩ := loopMaster_exists_transport_length P (loopMasterLength ℓ) ξ hξ
    have hmχ := loopMaster_transport_mean_zero P _ ξ χ hξ hχ hcχ
    have hdχ := loopMaster_transport_derivative P ℓ ξ χ hξ hχ hcχ
    have hder (u : ℝ) : deriv (fun v : ℝ => ψ (v : Circle (loopMasterLength ℓ))) u =
        deriv (fun v : ℝ => χ (v : Circle (loopMasterLength ℓ))) u := by
      exact_mod_cast (hd u).trans (hdχ u).symm
    let f : ℝ → ℝ := fun u => ψ (u : Circle (loopMasterLength ℓ)) - χ (u : Circle (loopMasterLength ℓ))
    have hfd : Differentiable ℝ f :=
      (hψ.differentiable (by simp)).sub (hχ.differentiable (by simp))
    have hzero (u : ℝ) : deriv f u = 0 := by
      change deriv ((fun v : ℝ => ψ (v : Circle (loopMasterLength ℓ))) -
        (fun v : ℝ => χ (v : Circle (loopMasterLength ℓ)))) u = 0
      rw [deriv_sub (hψ.differentiable (by simp) u) (hχ.differentiable (by simp) u), hder, sub_self]
    have hfconst := is_const_of_deriv_eq_zero hfd hzero
    have hIf := congrArg (fun g : ℝ → ℝ => ∫ u in (0 : ℝ)..(loopMasterLength ℓ).val, g u)
      (funext fun u => hfconst u 0)
    change (∫ u in (0 : ℝ)..(loopMasterLength ℓ).val,
      (ψ (u : Circle (loopMasterLength ℓ)) - χ (u : Circle (loopMasterLength ℓ)))) = _ at hIf
    rw [intervalIntegral.integral_sub (hψ.continuous.intervalIntegrable _ _)
      (hχ.continuous.intervalIntegrable _ _), hm, hmχ, sub_self,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hIf
    have hf0 : f 0 = 0 :=
      (mul_eq_zero.mp hIf.symm).resolve_left (loopMasterLength ℓ).property.ne'
    have hfun : ψ = χ := by
      funext z
      obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective z
      exact sub_eq_zero.mp ((hfconst u 0).trans hf0)
    subst χ
    exact hcχ

/-- The master identity with transport existence and smoothness concluded from the test.
This form has exactly the hypotheses of the paper: positive parameters, `N ≥ 1`, an admissible
scale, and a smooth real test on the long circle. -/
theorem loop_equations_master_exists (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ξ : Circle (loopMasterLength ℓ) → ℝ)
    (hξ : ContDiff ℝ ∞ (fun u : ℝ => ξ (u : Circle (loopMasterLength ℓ)))) :
    ∃ ψ : Circle (loopMasterLength ℓ) → ℝ,
    ∃ hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle (loopMasterLength ℓ))),
      (∀ k, coeff (loopMasterLength ℓ)
        ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
        transportCoeffs P (loopMasterLength ℓ) (loopMasterLengthTest _ ξ hξ) k) ∧
      (∫ u in (0 : ℝ)..(loopMasterLength ℓ).val, ψ (u : Circle (loopMasterLength ℓ))) = 0 ∧
      ∀ (x : Fin (N : ℕ) → ℝ)
        (hx : ∀ i j, i ≠ j → ((x i - x j : ℝ) : UnitAddCircle) ≠ 0),
        let a := ((N : ℝ) * ℓ.val) ^ (P.val.2 - 1)
        let Ψ := loopMasterProfile ℓ ψ hψ
        P.val.1 * (∑ k : Fin (N : ℕ), partialDeriv (energyLift (parametersExponent P) N) k x *
            partialDeriv (loopScalePotential ℓ a Ψ N) k x)
          - laplacian (loopScalePotential ℓ a Ψ N) x
          - fluctIntegral (fun u => ξ ((u / ℓ.val : ℝ) : Circle (loopMasterLength ℓ))) N x =
        a * (P.val.1 * loopScale (parametersExponent P) N ℓ Ψ x hx
          - fluctIntegral (fun u => deriv Ψ.val (u / ℓ.val)) N x) := by
  obtain ⟨ψ, hψ, hc⟩ := loopMaster_exists_transport_length P (loopMasterLength ℓ) ξ hξ
  exact ⟨ψ, hψ, hc, loopMaster_transport_mean_zero P _ ξ ψ hξ hψ hc,
    loop_equations_master P N ℓ ξ ψ hξ hψ hc⟩

end Riesz1

end
