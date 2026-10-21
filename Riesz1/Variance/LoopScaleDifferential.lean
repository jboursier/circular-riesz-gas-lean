/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopScale
import all Riesz1.Variance.LoopForce
import all Riesz1.Variance.LoopForceEnergy

/-!
# Derivatives of the scaled diagonal potential

The gradient and Laplacian assertions for the scaled potential, and the
algebraic rescaling of Proposition 5.5.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

lemma partialDeriv_const_mul {N : ℕ} (F : (Fin N → ℝ) → ℝ) (a : ℝ) (k : Fin N)
    (x : Fin N → ℝ) : partialDeriv (fun y => a * F y) k x = a * partialDeriv F k x := by
  unfold partialDeriv
  exact deriv_const_mul_field a

lemma laplacian_const_mul {N : ℕ} (F : (Fin N → ℝ) → ℝ) (a : ℝ) (x : Fin N → ℝ) :
    laplacian (fun y => a * F y) x = a * laplacian F x := by
  unfold laplacian
  simp_rw [partialDeriv_const_mul, ← Finset.mul_sum]

/-- The gradient of `Φ_{ψ,a}` is `a ℓ (ψ(xᵢ/ℓ))ᵢ`. -/
theorem partialDeriv_loopScalePotential (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) {N : ℕ} (k : Fin N) (x : Fin N → ℝ) :
    partialDeriv (loopScalePotential ℓ a ψ N) k x = a * ℓ.val * ψ.val (x k / ℓ.val) := by
  obtain ⟨C, hC⟩ := ψ.property.2
  have hc : Continuous (loopScaleField ℓ.val ψ.val) :=
    continuous_const.mul (hC.continuous.comp (continuous_id.div_const ℓ.val))
  rw [loopScalePotential_eq_fieldPotential, partialDeriv_const_mul,
    partialDeriv_fieldPotential hc]
  change a * (ℓ.val * ψ.val (x k / ℓ.val)) = _
  ring

/-- Differentiating `ℓ ψ(x/ℓ)` cancels the scale in the chain rule. -/
lemma deriv_loopScaleField (ℓ : Ioc (0 : ℝ) 1) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (u : ℝ) :
    deriv (loopScaleField ℓ.val ψ) u = deriv ψ (u / ℓ.val) := by
  have hd := ((hψ.differentiable (by simp) (u / ℓ.val)).hasDerivAt.comp u
    ((hasDerivAt_id u).div_const ℓ.val)).const_mul ℓ.val
  have he : ℓ.val * (deriv ψ (u / ℓ.val) * (1 / ℓ.val)) = deriv ψ (u / ℓ.val) := by
    field_simp [ℓ.property.1.ne']
  rw [he] at hd
  exact hd.deriv

/-- The Laplacian of `Φ_{ψ,a}` is `a Fluct_N[ψ'(·/ℓ)]`. -/
theorem laplacian_loopScalePotential (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) (N : ℕ) (x : Fin N → ℝ) :
    laplacian (loopScalePotential ℓ a ψ N) x =
      a * fluctIntegral (fun u => deriv ψ.val (u / ℓ.val)) N x := by
  rw [loopScalePotential_eq_fieldPotential, laplacian_const_mul,
    laplacian_fieldPotential (loopScaleField_contDiff hψ) (loopScaleField_periodic ψ.property.1)]
  congr 2
  funext u
  exact deriv_loopScaleField ℓ hψ u

/-- The force expansion for the scaled potential. This holds for every smooth profile,
before specializing the profile to the mean-zero transport. -/
theorem loopScale_force_expansion (s : RieszExponent) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (a β : ℝ) (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (x : Fin (N : ℕ) → ℝ)
    (hx : ∀ i j, i ≠ j → ((x i - x j : ℝ) : UnitAddCircle) ≠ 0) :
    β * (∑ k : Fin (N : ℕ), partialDeriv (energyLift s N) k x *
        partialDeriv (loopScalePotential ℓ a ψ N) k x)
      - laplacian (loopScalePotential ℓ a ψ N) x =
    a * (β * loopScale s N ℓ ψ x hx
      - 2 * β * (N : ℝ) ^ (1 - s.val) *
        fluctIntegral (pvConv s.val (loopScaleField ℓ.val ψ.val)) N x
      - fluctIntegral (fun u => deriv ψ.val (u / ℓ.val)) N x) := by
  have hg : (∑ k : Fin (N : ℕ), partialDeriv (energyLift s N) k x *
      partialDeriv (loopScalePotential ℓ a ψ N) k x) =
      a * gradDot s N (loopScaleField ℓ.val ψ.val) x := by
    rw [loopScalePotential_eq_fieldPotential]
    unfold gradDot
    simp_rw [partialDeriv_const_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hgrad : gradDot s N (loopScaleField ℓ.val ψ.val) x =
      loopFunctional s.val N (loopScaleField ℓ.val ψ.val) x -
        2 * (N : ℝ) ^ (1 - s.val) * ∑ i, pvConv s.val (loopScaleField ℓ.val ψ.val) (x i) :=
    gradDot_eq_loop s.val s.property.1 s.property.2 N.property (loopScaleField_contDiff hψ)
      (loopScaleField_periodic ψ.property.1) x hx
  rw [hg, laplacian_loopScalePotential ℓ a ψ hψ, hgrad,
    ← fluctIntegral_pvConv s.property.1 s.property.2 (loopScaleField_contDiff hψ)
      (loopScaleField_periodic ψ.property.1)]
  change β * (a * (loopScale s N ℓ ψ x hx - _)) - _ = _
  ring

end Riesz1

end
