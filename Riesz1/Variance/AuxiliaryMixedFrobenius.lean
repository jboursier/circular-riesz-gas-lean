/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopIBPUniform
public import Riesz1.Variance.LoopForce
public import Riesz1.Gibbs.FluctuationMoments
public import Riesz1.ToMathlib.CircleFourierDerivativeShift

/-!
# The diagonal derivative term in mean

The diagonal contribution in the proof of the mixed identity in Proposition 5.6.
The field `DΨ_ψ(X) = diag(ψ'(x_i/ℓ))` has the Frobenius square `∑_i ψ'(x_i/ℓ)²`, which is the
linear statistic of the one-periodic function `u ↦ ψ'(u/ℓ)²`. Its Gibbs mean is `N` times the
integral of that function over one period. The file proves this from the uniform one-particle
marginals (`map_coord_gibbsMeasure`, through `integral_comp_coord`).

The main result is `Riesz1.integral_frobeniusSqDiag`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The Gibbs mean of the Frobenius square of the diagonal derivative field `DΨ_ψ`: it equals
`N` times the integral of `ψ'(u/ℓ)²` over one period `u ∈ [0, 1]`. -/
theorem integral_frobeniusSqDiag (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) :
    ∫ X : Configuration N, frobeniusSqDiag ℓ ψ X ∂gibbsMeasure P N =
      (N : ℝ) * ∫ u in (0 : ℝ)..1, deriv ψ.val (u / ℓ.val) ^ 2 := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  set h : ℝ → ℝ := fun u => deriv ψ.val (u / ℓ.val) ^ 2 with hh
  -- The integrand is one-periodic, because `ψ` has period `ℓ⁻¹` and `(u + 1)/ℓ = u/ℓ + ℓ⁻¹`.
  have hdψ : Function.Periodic (deriv ψ.val) ℓ.val⁻¹ :=
    CircleFourier.periodic_deriv ψ.property.1
  have hper : Function.Periodic h 1 := by
    intro u
    simp only [hh]
    rw [show (u + 1) / ℓ.val = u / ℓ.val + ℓ.val⁻¹ by rw [add_div, one_div], hdψ (u / ℓ.val)]
  have hcont : Continuous h := by
    have hd : Continuous (deriv ψ.val) := hψ.continuous_deriv (by simp)
    exact (hd.comp (continuous_id.div_const _)).pow 2
  -- Its circle lift is continuous, hence square integrable on the circle.
  set G : UnitAddCircle → ℝ := hper.lift with hG
  have hGcont : Continuous G := continuous_lift_periodic hcont hper
  have hGmem : MemLp G 2 volume := hGcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- The Frobenius square is the linear statistic of `G`.
  have hfrob : (fun X : Configuration N => frobeniusSqDiag ℓ ψ X) =
      fun X : Configuration N => linearStatistic G X := by
    funext X
    unfold frobeniusSqDiag linearStatistic
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hG, hper.lift_coe]
  rw [hfrob, integral_linearStatistic P N hGmem]
  congr 1
  -- The circle integral of `G` is the integral of `h` over one period.
  rw [← UnitAddCircle.intervalIntegral_preimage 0 G]
  simp only [zero_add, hG, hper.lift_coe]

/-- The Gibbs mean of the Frobenius square, rescaled to the profile circle of length `ℓ⁻¹`: with
`K = Nℓ` it equals `K ∫_0^{ℓ⁻¹} ψ'(v)² dv`, which is the term `K^{2s-1}‖ψ_h'‖²` after the power of
`K` in `a² = K^{2s-2}`. -/
theorem integral_frobeniusSqDiag_profile (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) :
    ∫ X : Configuration N, frobeniusSqDiag ℓ ψ X ∂gibbsMeasure P N =
      ((N : ℝ) * ℓ.val) * ∫ v in (0 : ℝ)..ℓ.val⁻¹, deriv ψ.val v ^ 2 := by
  rw [integral_frobeniusSqDiag P N ℓ ψ hψ]
  have hℓ : ℓ.val ≠ 0 := ne_of_gt ℓ.property.1
  have hc : ℓ.val⁻¹ ≠ 0 := inv_ne_zero hℓ
  have hsub : (fun u : ℝ => deriv ψ.val (u / ℓ.val) ^ 2) =
      fun u : ℝ => deriv ψ.val (ℓ.val⁻¹ * u) ^ 2 := by
    funext u
    rw [div_eq_inv_mul]
  have key := intervalIntegral.integral_comp_mul_left (fun v : ℝ => deriv ψ.val v ^ 2) hc
    (a := (0 : ℝ)) (b := 1)
  simp only [mul_zero, mul_one, inv_inv, smul_eq_mul] at key
  rw [hsub, key]
  ring

end Riesz1

end

end
