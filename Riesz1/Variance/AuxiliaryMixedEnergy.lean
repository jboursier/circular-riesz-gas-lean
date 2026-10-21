/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.MeanFieldEnergy
public import Riesz1.Variance.AuxiliaryMixedExpansion
public import Riesz1.Variance.AuxiliaryMixedKernel
public import Riesz1.Variance.AuxiliaryMixedHessian
public import Riesz1.Variance.LoopMasterScaling
public import Riesz1.Variance.LoopMaster
public import Riesz1.Variance.LoopIBPMoments
public import Riesz1.ToMathlib.CircleFourierPairing
public import Riesz1.Variance.LoopMasterTransport

/-!
# The energy link in the proof of Proposition 5.6

For a transport `φ` on the unit circle, the Hessian background integral of the loop profile
`f = ℓ ψ(·/ℓ)` is `ℓ^{2-2s}` times the double integral `I(φ)` of the Riesz kernel second derivative
against `(φ(x) - φ(y))²` (Fubini on `(0,1]²`). The mean-field energy identity
`Riesz1.mean_field_energy_identity` gives `β I(φ) = C σ²(η)` for the
unit transport `φ` of a smooth profile `η`. Together with the Hessian expectation
`integral_hessPairSum`, this is the energy step `β K^{2s-2} N^{2-s} ∬ K_f = K^s σ_ℓ²(ξ_h)` of the
proof of Proposition 5.6.

The main results are `Riesz1.integral_hessBackground_loop_eq`, `Riesz1.beta_mul_energy_eq` and
`Riesz1.integral_hessianQuadratic_eq`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace Riesz1

/-- The Riesz representative on the real line is the Hurwitz kernel: the second derivative in the
energy identity is the second derivative of `hurwitzKernel`. -/
lemma riesz_representative_eq_hurwitzKernel (s : RieszExponent) :
    (fun t : ℝ => rieszRepresentative s (t : UnitAddCircle)) = hurwitzKernel s.val := rfl

/-- Factoring a scalar out of the Hessian background: for `f = κ φ`, the background integral is
`κ²` times the double integral of the kernel against `(φ x - φ y)²` over the unit square, by
Fubini's theorem on `(0,1]²`. -/
theorem integral_hessBackground_scaled_eq (s : ℝ) (κ : ℝ) (φ : ℝ → ℝ)
    (hint : Integrable (fun p : ℝ × ℝ => deriv (deriv (hurwitzKernel s)) (p.1 - p.2) *
        (φ p.1 - φ p.2) ^ 2) ((volume.restrict (Ioc (0 : ℝ) 1)).prod
          (volume.restrict (Ioc (0 : ℝ) 1)))) :
    ∫ a in (0 : ℝ)..1, hessBackground s (fun u => κ * φ u) a =
      κ ^ 2 * ∫ p : ℝ × ℝ, deriv (deriv (hurwitzKernel s)) (p.1 - p.2) *
        (φ p.1 - φ p.2) ^ 2 ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod
          (volume.restrict (Ioc (0 : ℝ) 1))) := by
  have hkernel : ∀ a y : ℝ, hessKernel s (fun u => κ * φ u) a y =
      κ ^ 2 * (deriv (deriv (hurwitzKernel s)) (a - y) * (φ a - φ y) ^ 2) := fun a y => by
    unfold hessKernel
    ring
  have hb : ∀ a : ℝ, hessBackground s (fun u => κ * φ u) a =
      κ ^ 2 * ∫ y in (0 : ℝ)..1, deriv (deriv (hurwitzKernel s)) (a - y) * (φ a - φ y) ^ 2 := by
    intro a
    unfold hessBackground
    simp_rw [hkernel]
    rw [intervalIntegral.integral_const_mul]
  simp_rw [hb]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le zero_le_one]
  congr 1
  rw [integral_prod _ hint]
  congr 1
  funext a
  rw [intervalIntegral.integral_of_le zero_le_one]

/-- **The energy identity**, in the form used in the proof of Proposition 5.6: for a smooth
profile `η` on the unit circle and an `L²` function `φ` with the transport coefficients of `η`,
`β I(φ) = (2π)^{1-s}/(2βR) σ²(η)`, where `I(φ)` is the double integral of the Riesz kernel
second derivative against `(φ x - φ y)²` over `(0,1]²`. -/
theorem beta_mul_energy_eq (P : Parameters) (η φ : UnitAddCircle → ℝ)
    (hη : IsSmoothCircle η)
    (hφ : MemLp (fun x : UnitAddCircle => (φ x : ℂ)) 2 volume)
    (htr : ∀ k : ℤ, circleCoeff φ k = transportCoeffs P unitLength (loopMasterTest η hη) k) :
    P.val.1 * (∫ p : ℝ × ℝ, deriv (deriv (hurwitzKernel (parametersExponent P).val))
        (p.1 - p.2) * (φ (p.1 : UnitAddCircle) - φ (p.2 : UnitAddCircle)) ^ 2
        ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1)))) =
      ((2 * π) ^ (1 - (parametersExponent P).val) /
        (2 * P.val.1 * rieszConstant (parametersExponent P))) *
        (circleSobolevSq ((1 - (parametersExponent P).val) / 2)
          ⟨fun x : UnitAddCircle => (η x : ℂ), memLp_unitCircle_of_isSmoothCircle hη⟩).toReal := by
  have hcoeff : ∀ k : ℤ, fourierCoeff (fun x : UnitAddCircle => (φ x : ℂ)) k =
      transportCoeffs P ⟨1, one_pos⟩ ⟨η, memLp_unitCircle_of_isSmoothCircle hη⟩ k := fun k => htr k
  have h := mean_field_energy_identity P ⟨η, memLp_unitCircle_of_isSmoothCircle hη⟩ hη φ hφ hcoeff
  obtain ⟨_, _, h3, h4⟩ := h
  rw [riesz_representative_eq_hurwitzKernel] at h3 h4
  linarith

/-- The energy identity with its integrability and finiteness conclusions, for a smooth profile `η`
and an `L²` function `φ` with the transport coefficients of `η`. -/
theorem energy_package (P : Parameters) (η φ : UnitAddCircle → ℝ)
    (hη : IsSmoothCircle η)
    (hφ : MemLp (fun x : UnitAddCircle => (φ x : ℂ)) 2 volume)
    (htr : ∀ k : ℤ, circleCoeff φ k = transportCoeffs P unitLength (loopMasterTest η hη) k) :
    Integrable (fun p : ℝ × ℝ => deriv (deriv (hurwitzKernel (parametersExponent P).val))
        (p.1 - p.2) * (φ (p.1 : UnitAddCircle) - φ (p.2 : UnitAddCircle)) ^ 2)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) ∧
    circleSobolevSq ((1 - (parametersExponent P).val) / 2)
      ⟨fun x : UnitAddCircle => (η x : ℂ), memLp_unitCircle_of_isSmoothCircle hη⟩ ≠ ⊤ := by
  have hcoeff : ∀ k : ℤ, fourierCoeff (fun x : UnitAddCircle => (φ x : ℂ)) k =
      transportCoeffs P ⟨1, one_pos⟩ ⟨η, memLp_unitCircle_of_isSmoothCircle hη⟩ k := fun k => htr k
  have h := mean_field_energy_identity P ⟨η, memLp_unitCircle_of_isSmoothCircle hη⟩ hη φ hφ hcoeff
  obtain ⟨h1, h2, _, _⟩ := h
  refine ⟨?_, h2⟩
  rw [riesz_representative_eq_hurwitzKernel] at h1
  exact h1

/-- The Hessian quadratic term is `β N^{-s}` times the pair sum of the field `f = loopScaleField`. -/
lemma hessianQuadratic_eq_scaled_pairSum (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) (X : Configuration N) :
    hessianQuadratic P N ℓ ψ X = P.val.1 * (N : ℝ) ^ (-(parametersExponent P).val) *
      hessPairSum (parametersExponent P).val (N : ℕ) (loopScaleField ℓ.val ψ.val) X.val := by
  rw [hessianQuadratic_eq_pairSum]
  rfl

/-- **The Hessian expectation** (the Hessian step in the proof of Proposition 5.6): the Gibbs mean
of the Hessian quadratic term is `β N^{-s}` times `N²` times the background integral plus the mean
of the fluctuation expansion. -/
theorem integral_hessianQuadratic_eq (P : Parameters) (hPL : External.PrekopaLeindler)
    (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) (ψ : LoopScaleProfile ℓ.val) :
    ∫ X, hessianQuadratic P N ℓ ψ X ∂(gibbsMeasure P N) =
      P.val.1 * (N : ℝ) ^ (-(parametersExponent P).val) *
        ((N : ℝ) ^ 2 * (∫ u in (0 : ℝ)..1, hessBackground (parametersExponent P).val
          (loopScaleField ℓ.val ψ.val) u) +
        ∫ X : Configuration N, hessFluctExpansion (parametersExponent P).val (N : ℕ)
          (loopScaleField ℓ.val ψ.val) X.val ∂(gibbsMeasure P N)) := by
  simp_rw [hessianQuadratic_eq_scaled_pairSum]
  rw [integral_const_mul, integral_hessPairSum P hPL N ℓ ψ]

end Riesz1

end
