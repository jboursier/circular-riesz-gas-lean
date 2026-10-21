/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopForce
import all Riesz1.Variance.LoopForce
import all Riesz1.Variance.LoopForceEnergy

/-!
# The loop functional at an arbitrary scale

Profiles are Lipschitz periodic real functions,
the scale is in `(0,1]`, and particle lifts have distinct images on the circle.
The definition uses exactly the four terms of the fluctuation expansion, through the
unit-scale functional applied to the field `x ↦ ℓ ψ(x/ℓ)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- Real Lipschitz profiles on the circle of length `ℓ⁻¹`, represented by periodic lifts. -/
@[reducible] def LoopScaleProfile (ℓ : ℝ) :=
  {ψ : ℝ → ℝ // Function.Periodic ψ ℓ⁻¹ ∧ ∃ C : NNReal, LipschitzWith C ψ}

/-- The unit-circle field `ℓ ψ(x/ℓ)`. -/
noncomputable def loopScaleField (ℓ : ℝ) (ψ : ℝ → ℝ) (u : ℝ) : ℝ := ℓ * ψ (u / ℓ)

lemma loopScaleField_periodic {ℓ : ℝ} {ψ : ℝ → ℝ}
    (hp : Function.Periodic ψ ℓ⁻¹) : Function.Periodic (loopScaleField ℓ ψ) 1 := by
  intro u
  unfold loopScaleField
  rw [add_div, one_div, hp]

lemma loopScaleField_contDiff {ℓ : ℝ} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (loopScaleField ℓ ψ) :=
  contDiff_const.mul (hψ.comp (contDiff_id.div_const ℓ))

/-- The loop functional, for every admissible scale and every Lipschitz profile.
The noncollision condition specifies the carrier of the particle-particle term. -/
noncomputable def loopScale (s : RieszExponent) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) (x : Fin (N : ℕ) → ℝ)
    (_hx : ∀ i j, i ≠ j → ((x i - x j : ℝ) : UnitAddCircle) ≠ 0) : ℝ :=
  loopFunctional s.val N (loopScaleField ℓ.val ψ.val) x

/-- Multiplying a field by a real scalar multiplies its loop by that scalar. -/
lemma loopFunctional_const_mul (s : ℝ) (N : ℕ) (c : ℝ) (ψ : ℝ → ℝ)
    (x : Fin N → ℝ) :
    loopFunctional s N (fun u => c * ψ u) x = c * loopFunctional s N ψ x := by
  have hk : loopKernel s (fun u => c * ψ u) = fun u v => c * loopKernel s ψ u v := by
    funext u v
    unfold loopKernel
    ring
  unfold loopFunctional
  simp_rw [hk]
  have hite (i j : Fin N) : (if j = i then 0 else c * loopKernel s ψ (x i) (x j)) =
      c * (if j = i then 0 else loopKernel s ψ (x i) (x j)) := by
    split <;> simp_all
  simp_rw [hite, intervalIntegral.integral_const_mul, ← Finset.mul_sum]
  ring

/-- At scale one the definition is exactly `loopFunctional`. -/
lemma loopScale_one (s : RieszExponent) (N : ℕ+) (ψ : LoopScaleProfile 1)
    (x : Fin (N : ℕ) → ℝ)
    (hx : ∀ i j, i ≠ j → ((x i - x j : ℝ) : UnitAddCircle) ≠ 0) :
    loopScale s N ⟨1, zero_lt_one, le_rfl⟩ ψ x hx = loopFunctional s.val N ψ.val x := by
  change loopFunctional s.val N (fun u => 1 * ψ.val (u / 1)) x = _
  simp only [div_one, one_mul]

/-- The four terms in the definition, with the scale factor outside the expansion. -/
lemma loopScale_eq_expansion (s : RieszExponent) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) (x : Fin (N : ℕ) → ℝ)
    (hx : ∀ i j, i ≠ j → ((x i - x j : ℝ) : UnitAddCircle) ≠ 0) :
    loopScale s N ℓ ψ x hx = ℓ.val * loopFunctional s.val N (fun u => ψ.val (u / ℓ.val)) x :=
  loopFunctional_const_mul _ _ _ _ _

/-- Scaling identity used in Proposition 5.5:
`Loop₁[ℓ^s ψ(·/ℓ)] = ℓ^(s-1) Loop_ℓ[ψ]`. -/
lemma loopScale_transport_scaling (s : RieszExponent) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) (x : Fin (N : ℕ) → ℝ)
    (hx : ∀ i j, i ≠ j → ((x i - x j : ℝ) : UnitAddCircle) ≠ 0) :
    loopFunctional s.val N (fun u => ℓ.val ^ s.val * ψ.val (u / ℓ.val)) x =
      ℓ.val ^ (s.val - 1) * loopScale s N ℓ ψ x hx := by
  rw [loopFunctional_const_mul, loopScale_eq_expansion]
  rw [← mul_assoc, Real.rpow_sub_one ℓ.property.1.ne', div_mul_cancel₀ _ ℓ.property.1.ne']

/-- The lifted scalar potential, written in the original coordinates.
It is periodic in each coordinate when the profile has zero mean. -/
noncomputable def loopScalePotential (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  a * ℓ.val ^ 2 * ∑ i : Fin N, ∫ u in (0 : ℝ)..(x i / ℓ.val), ψ.val u

/-- Change of variables identifies the scaled primitive with the field potential. -/
lemma loopScalePotential_eq_fieldPotential (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (N : ℕ) :
    loopScalePotential ℓ a ψ N = fun x => a * fieldPotential (loopScaleField ℓ.val ψ.val) N x := by
  funext x
  have hi (t : ℝ) : (∫ u in (0 : ℝ)..t, loopScaleField ℓ.val ψ.val u) =
      ℓ.val ^ 2 * ∫ u in (0 : ℝ)..(t / ℓ.val), ψ.val u := by
    unfold loopScaleField
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div _ ℓ.property.1.ne']
    simp only [zero_div, smul_eq_mul]
    ring
  unfold loopScalePotential fieldPotential
  simp_rw [hi, ← Finset.mul_sum]
  ring

end Riesz1

end
