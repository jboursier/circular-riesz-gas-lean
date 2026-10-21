/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GroundStatePotential
public import Riesz1.HelfferSjostrand.BoundaryCoreTests
public import Riesz1.ToMathlib.GroundStateProductRule
public import Riesz1.ToMathlib.WeightedSobolev.LocalIntegrationByParts

/-!
# Ground-state multiplication preserves the test class

The classical product rule and preservation of the entire collision-free
test class. No boundary regularity of the
Hamiltonian is needed, because the tests vanish near the boundary.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff Laplacian

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

/-- Multiplication by any real exponential of the Hamiltonian preserves
the collision-free test class. -/
def hsExponentialTest (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c)
    (t : ℝ) (f : HsTestFunction N) : HsTestFunction N where
  toFun x := f x * Real.exp (t * hsPairExpression χ x)
  smooth := WeightedSobolev.contDiff_cutoff_mul (isOpen_hsChamber N) f.smooth
    (f.tsupport_subset_chamber hN) (contDiffOn_const.mul (hsPairExpression_contDiffOn χ)).exp
  periodic k x := by rw [f.periodic, hsPairExpression_translate]
  boundarySupport := by
    obtain ⟨δ, hδ, hf⟩ := f.boundarySupport
    exact ⟨δ, hδ, fun x hx => hf x (fun hz => hx (by rw [hz, zero_mul]))⟩

/-- The inverse exponential recovers the original test, on its whole carrier. -/
theorem hsExponentialTest_inverse (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c)
    (t : ℝ) (f : HsTestFunction N) :
    (hsExponentialTest hN χ (-t) (hsExponentialTest hN χ t f)).toFun = f.toFun := by
  funext x
  change (f x * Real.exp (t * hsPairExpression χ x)) *
    Real.exp (-t * hsPairExpression χ x) = f x
  rw [mul_assoc, ← Real.exp_add]
  ring_nf
  rw [Real.exp_zero, mul_one]

/-- The differential ground-state identity, throughout the chamber.
This is `(-Δ + W)(e^{-H/2} f) = e^{-H/2} L₀f`. -/
theorem hsGroundState_differential (χ : HsPairPotentials N c)
    {f : HsEuclidean N → ℝ} (hf : ContDiffOn ℝ ∞ f (hsChamber N))
    {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    -(Δ (fun z => Real.exp (-hsPairExpression χ z / 2) * f z)) x +
        hsGroundStatePotential χ x * (Real.exp (-hsPairExpression χ x / 2) * f x) =
      Real.exp (-hsPairExpression χ x / 2) *
        (inner ℝ (gradient (hsPairExpression χ) x) (gradient f x) - Δ f x) := by
  have h := laplacian_exp_mul (isOpen_hsChamber N) (hsPairExpression_contDiffOn χ) hf
    (-1 / 2) hx
  have he : (fun z => Real.exp (-hsPairExpression χ z / 2) * f z) =
      fun z => Real.exp ((-1 / 2) * hsPairExpression χ z) * f z := by
    funext z
    congr 2
    ring
  rw [he, h]
  unfold hsGroundStatePotential
  have harg : (-1 / 2) * hsPairExpression χ x = -hsPairExpression χ x / 2 := by ring
  rw [harg]
  ring

/-- The inverse-weight formula used to turn an adjoint equation into
the unweighted Schrödinger equation. -/
theorem hsGroundState_inverse_differential (χ : HsPairPotentials N c)
    {φ : HsEuclidean N → ℝ} (hφ : ContDiffOn ℝ ∞ φ (hsChamber N))
    {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    inner ℝ (gradient (hsPairExpression χ) x)
        (gradient (fun z => Real.exp (hsPairExpression χ z / 2) * φ z) x) -
        Δ (fun z => Real.exp (hsPairExpression χ z / 2) * φ z) x =
      Real.exp (hsPairExpression χ x / 2) *
        (-Δ φ x + hsGroundStatePotential χ x * φ x) := by
  have hg : inner ℝ (gradient (hsPairExpression χ) x)
      (gradient (fun z => Real.exp ((1 / 2) * hsPairExpression χ z) * φ z) x) =
      Real.exp ((1 / 2) * hsPairExpression χ x) *
        (inner ℝ (gradient (hsPairExpression χ) x) (gradient φ x) +
          (1 / 2) * ‖gradient (hsPairExpression χ) x‖ ^ 2 * φ x) := by
    let B := EuclideanSpace.basisFun (Fin (N : ℕ)) ℝ
    rw [← B.sum_inner_mul_inner, ← B.sum_inner_mul_inner (gradient (hsPairExpression χ) x)
      (gradient φ x), ← real_inner_self_eq_norm_sq (gradient (hsPairExpression χ) x),
      ← B.sum_inner_mul_inner (gradient (hsPairExpression χ) x) (gradient (hsPairExpression χ) x)]
    simp only [inner_gradient_left, inner_gradient_right, RCLike.conj_to_real]
    simp_rw [fderiv_exp_mul_apply (isOpen_hsChamber N)
      (hsPairExpression_contDiffOn χ) hφ (1 / 2) hx]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have he : (fun z => Real.exp (hsPairExpression χ z / 2) * φ z) =
      fun z => Real.exp ((1 / 2) * hsPairExpression χ z) * φ z := by
    funext z
    congr 2
    ring
  rw [he, hg, laplacian_exp_mul (isOpen_hsChamber N) (hsPairExpression_contDiffOn χ) hφ (1 / 2) hx]
  unfold hsGroundStatePotential
  have harg : (1 / 2) * hsPairExpression χ x = hsPairExpression χ x / 2 := by ring
  rw [harg]
  ring

end Riesz1
