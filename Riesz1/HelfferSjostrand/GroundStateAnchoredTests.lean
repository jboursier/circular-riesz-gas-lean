/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GroundStateAnchoredTransform
public import Riesz1.HelfferSjostrand.BoundaryCoreAnchoredTests

/-!
# Ground-state multiplication on the anchored test functions

Preservation of the existing compact smooth test class and the classical
Schrödinger product identity, for the ground-state conjugation and the scalar boundary core.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff Laplacian

namespace Riesz1

variable {n : ℕ} {c : ℝ} (χ : HsPairPotentials n.succPNat c)

/-- Every real exponential of the anchored Hamiltonian preserves test functions. -/
def anchoredExponentialTest (t : ℝ) (f : anchoredTestSubmodule n) : anchoredTestSubmodule n :=
  ⟨fun y => f.val y * Real.exp (t * hsAnchoredHamiltonianE χ y),
    WeightedSobolev.contDiff_cutoff_mul (isOpen_anchoredSimplex n) f.property.1 f.property.2.2
      (contDiffOn_const.mul (contDiffOn_hsAnchoredHamiltonianE χ)).exp,
    f.property.2.1.mul_right, tsupport_mul_subset_left.trans f.property.2.2⟩

/-- The normalized forward transform on the entire anchored test class. -/
def anchoredGroundStateTest (f : anchoredTestSubmodule n) : anchoredTestSubmodule n :=
  (Real.sqrt (hsPartitionFunction χ).toReal)⁻¹ • anchoredExponentialTest χ (-1 / 2) f

/-- The normalized inverse transform on the entire anchored test class. -/
def anchoredInverseGroundStateTest (f : anchoredTestSubmodule n) : anchoredTestSubmodule n :=
  Real.sqrt (hsPartitionFunction χ).toReal • anchoredExponentialTest χ (1 / 2) f

/-- The normalized test transform is the actual multiplier, pointwise everywhere. -/
theorem anchoredGroundStateTest_apply (f : anchoredTestSubmodule n) (y : AnchoredEuclidean n) :
    (anchoredGroundStateTest χ f).val y = anchoredGroundStateMultiplier χ y * f.val y := by
  change (Real.sqrt (hsPartitionFunction χ).toReal)⁻¹ *
    (f.val y * Real.exp ((-1 / 2) * hsAnchoredHamiltonianE χ y)) = _
  unfold anchoredGroundStateMultiplier
  rw [show (-1 / 2) * hsAnchoredHamiltonianE χ y = -hsAnchoredHamiltonianE χ y / 2 by ring]
  ring

/-- The normalized test transformations are inverse on the entire test class. -/
theorem anchoredGroundStateTest_inverse (hc : 0 < c) (f : anchoredTestSubmodule n) :
    anchoredGroundStateTest χ (anchoredInverseGroundStateTest χ f) = f := by
  have hZ : Real.sqrt (hsPartitionFunction χ).toReal ≠ 0 :=
    (Real.sqrt_pos.mpr (ENNReal.toReal_pos (hsPartitionFunction_pos χ).ne'
      (hsPartitionFunction_lt_top χ hc).ne)).ne'
  apply Subtype.ext
  funext y
  rw [show (anchoredGroundStateTest χ (anchoredInverseGroundStateTest χ f)).val y =
    anchoredGroundStateMultiplier χ y * (anchoredInverseGroundStateTest χ f).val y from
      anchoredGroundStateTest_apply χ _ y]
  change (Real.sqrt (hsPartitionFunction χ).toReal)⁻¹ * Real.exp (-hsAnchoredHamiltonianE χ y / 2) *
    (Real.sqrt (hsPartitionFunction χ).toReal * (f.val y * Real.exp ((1 / 2) * hsAnchoredHamiltonianE χ y))) = _
  calc
    _ = ((Real.sqrt (hsPartitionFunction χ).toReal)⁻¹ * Real.sqrt (hsPartitionFunction χ).toReal) *
        (Real.exp (-hsAnchoredHamiltonianE χ y / 2) * Real.exp ((1 / 2) * hsAnchoredHamiltonianE χ y)) * f.val y := by ring
    _ = f.val y := by
      rw [inv_mul_cancel₀ hZ, ← Real.exp_add]
      rw [show -hsAnchoredHamiltonianE χ y / 2 + (1 / 2) * hsAnchoredHamiltonianE χ y = 0 by ring,
        Real.exp_zero, one_mul, one_mul]

/-- The differential ground-state identity throughout the anchored simplex. -/
theorem anchoredGroundState_differential {f : AnchoredEuclidean n → ℝ}
    (hf : ContDiffOn ℝ ∞ f (anchoredSimplex n)) {y : AnchoredEuclidean n}
    (hy : y ∈ anchoredSimplex n) :
    -Δ (fun z => Real.exp (-hsAnchoredHamiltonianE χ z / 2) * f z) y +
        hsAnchoredGroundStatePotential χ y * (Real.exp (-hsAnchoredHamiltonianE χ y / 2) * f y) =
      Real.exp (-hsAnchoredHamiltonianE χ y / 2) * anchoredLangevinExpr χ f y := by
  have h := laplacian_exp_mul (isOpen_anchoredSimplex n) (contDiffOn_hsAnchoredHamiltonianE χ) hf
    (-1 / 2) hy
  have he : (fun z => Real.exp (-hsAnchoredHamiltonianE χ z / 2) * f z) =
      fun z => Real.exp ((-1 / 2) * hsAnchoredHamiltonianE χ z) * f z := by
    funext z
    congr 2
    ring
  rw [he, h]
  unfold hsAnchoredGroundStatePotential anchoredLangevinExpr
  rw [show (-1 / 2) * hsAnchoredHamiltonianE χ y = -hsAnchoredHamiltonianE χ y / 2 by ring]
  ring

/-- The normalized test function satisfies the Schrödinger product identity. -/
theorem anchoredGroundStateTest_schrodinger (f : anchoredTestSubmodule n)
    {y : AnchoredEuclidean n} (hy : y ∈ anchoredSimplex n) :
    -Δ (anchoredGroundStateTest χ f).val y +
        hsAnchoredGroundStatePotential χ y * (anchoredGroundStateTest χ f).val y =
      anchoredGroundStateMultiplier χ y * anchoredLangevinExpr χ f.val y := by
  let a := (Real.sqrt (hsPartitionFunction χ).toReal)⁻¹
  let g := fun z => Real.exp (-hsAnchoredHamiltonianE χ z / 2) * f.val z
  have he : (anchoredGroundStateTest χ f).val = a • g := by
    funext z
    simpa only [a, g, Pi.smul_apply, smul_eq_mul, anchoredGroundStateMultiplier, mul_assoc] using anchoredGroundStateTest_apply χ f z
  have hg : ContDiffAt ℝ 2 g y := by
    apply ContDiffAt.of_le
      (((((contDiffOn_hsAnchoredHamiltonianE χ).neg.div_const 2).exp.mul
        f.property.1.contDiffOn).contDiffAt ((isOpen_anchoredSimplex n).mem_nhds hy)))
    norm_num
  rw [he, InnerProductSpace.laplacian_smul a hg]
  have hp := anchoredGroundState_differential χ f.property.1.contDiffOn hy
  change -(a * Δ g y) + hsAnchoredGroundStatePotential χ y * (a * g y) = _
  calc
    _ = a * (-Δ g y + hsAnchoredGroundStatePotential χ y * g y) := by ring
    _ = _ := by rw [hp]; simp only [a, anchoredGroundStateMultiplier, mul_assoc]

end Riesz1
