/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.AnchoredIntegrationByParts
public import Riesz1.HelfferSjostrand.GradientConvergenceAnchoredTests
public import Riesz1.HelfferSjostrand.GradientConvergenceCommutator
public import Riesz1.HelfferSjostrand.VectorEnergyAnchoredSobolev
public import Riesz1.ToMathlib.LangevinCommutator

/-!
# Gradients of anchored tests against vector tests

The commutator step in the proof of Remark 3.2. For an anchored test
function `f` and a test tuple `u`, the vector form of `∇f` against `u` is the integral of
`⟪∇(𝓛f), u⟫`, where `𝓛f = ⟪∇H*, ∇f⟫ - Δf`. The proof uses the pointwise commutator
`∂_i 𝓛f - 𝓛 ∂_i f = ∂_i∂_j H* ∂_j f` and the weighted integration by parts of
`AnchoredIntegrationByParts`. The integration by parts against a general vector test gives
the coefficient `∑_i (u_i ∂_i H* - ∂_i u_i)` that the weak equation uses.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ContDiff Laplacian

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- The coefficient `∑_i (u_i ∂_i H* - ∂_i u_i)` of the weighted integration by parts against a
vector test tuple `u`. -/
def anchoredWeakCoeff (χ : HsPairPotentials n.succPNat c) (u : AnchoredVectorTest n)
    (y : AnchoredEuclidean n) : ℝ :=
  ∑ i : Fin n, ((u i : AnchoredEuclidean n → ℝ) y *
      fderiv ℝ (hsAnchoredHamiltonianE χ) y (EuclideanSpace.single i 1) -
    fderiv ℝ (u i : AnchoredEuclidean n → ℝ) y (EuclideanSpace.single i 1))

/-- The Hessian of `H*` applied to a gradient splits into the coordinate commutators.
This is the pointwise identity behind the commutator step in Remark 3.2. -/
theorem hessian_gradient_coordinates (χ : HsPairPotentials n.succPNat c)
    {f : anchoredTestSubmodule n} {y : AnchoredEuclidean n} (hy : y ∈ anchoredSimplex n)
    (w : AnchoredEuclidean n) :
    fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) y (gradient f.val y) w =
      ∑ i : Fin n, (fderiv ℝ (anchoredLangevinExpr χ f.val) y (EuclideanSpace.single i 1) -
        anchoredLangevinExpr χ (anchoredGradientTestDirection f (EuclideanSpace.single i 1)).val y) *
          w i := by
  have hH := (contDiffOn_hsAnchoredHamiltonianE χ).contDiffAt
    ((isOpen_anchoredSimplex n).mem_nhds hy)
  have hsym := hH.isSymmSndFDerivAt (by simp)
  rw [hsCommutator_linear_coordinates
    (fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) y (gradient f.val y)) w]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hcomm := langevin_direction_commutator hH f.property.1 (EuclideanSpace.single i 1)
  exact (hsym _ _).trans hcomm.symm

/-- The pairing of a gradient with a vector is the coordinate sum of its directional
derivatives. -/
theorem inner_gradient_anchoredTestVector (g : AnchoredEuclidean n → ℝ) (y : AnchoredEuclidean n)
    (u : AnchoredVectorTest n) :
    inner ℝ (gradient g y) (anchoredTestVector u y) =
      ∑ i : Fin n, fderiv ℝ g y (EuclideanSpace.single i 1) * (u i : AnchoredEuclidean n → ℝ) y := by
  rw [inner_gradient_left, hsCommutator_linear_coordinates (fderiv ℝ g y) (anchoredTestVector u y)]
  rfl

/-- Integrability of a test pairing with a vector test tuple. -/
theorem integrable_gradient_anchoredTestVector (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (g : anchoredTestSubmodule n) (u : AnchoredVectorTest n) :
    Integrable (fun y => inner ℝ (gradient g.val y) (anchoredTestVector u y))
      (anchoredMeasureE χ) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  simp_rw [inner_gradient_anchoredTestVector]
  apply integrable_finsetSum
  intro i _
  have hcont : Continuous (fun y => fderiv ℝ g.val y (EuclideanSpace.single i 1)) :=
    (g.property.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : HasCompactSupport (fun y => fderiv ℝ g.val y (EuclideanSpace.single i 1)) :=
    g.property.2.1.fderiv_apply ℝ _
  have hu : Continuous (fun y => (u i : AnchoredEuclidean n → ℝ) y) :=
    (u i).property.1.continuous
  exact (hcont.mul hu).integrable_of_hasCompactSupport (hcs.mul_right)

/-- Integrability of the Langevin expression of a test against a test function. -/
theorem integrable_anchoredTest_mul (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (g h : anchoredTestSubmodule n) :
    Integrable (fun y => anchoredLangevinExpr χ g.val y * (h : AnchoredEuclidean n → ℝ) y)
      (anchoredMeasureE χ) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  have hcont : Continuous (anchoredLangevinExpr χ g.val) :=
    (anchoredGradient_langevin_smooth χ g).continuous
  have hcs : HasCompactSupport (anchoredLangevinExpr χ g.val) :=
    (anchoredGradientLangevinTest χ g).property.2.1
  exact Continuous.integrable_of_hasCompactSupport (hcont.mul h.property.1.continuous)
    (hcs.mul_right)

/-- The vector form of a gradient tuple, expressed through the integrand of the commutator
identity. The gradient part is integrated by parts against each coordinate, and the Hessian
part is a sum of commutators. -/
theorem anchoredVectorForm_gradientTest (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f : anchoredTestSubmodule n) (u : AnchoredVectorTest n) :
    anchoredVectorForm χ (anchoredGradientTestTuple f) u =
      ∫ y, inner ℝ (gradient (anchoredLangevinExpr χ f.val) y) (anchoredTestVector u y)
        ∂anchoredMeasureE χ := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  let B : AnchoredEuclidean n → ℝ := fun y => ∑ i : Fin n,
    (inner ℝ (gradient (anchoredGradientTestDirection f (EuclideanSpace.single i 1)).val y)
        (gradient (u i : AnchoredEuclidean n → ℝ) y) -
      anchoredLangevinExpr χ (anchoredGradientTestDirection f (EuclideanSpace.single i 1)).val y *
        (u i : AnchoredEuclidean n → ℝ) y)
  have hB_int : Integrable B (anchoredMeasureE χ) := by
    apply integrable_finsetSum
    intro i _
    exact (integrable_anchoredGradInner χ (anchoredMeasureE χ) (anchoredGradientTestTuple f) u i).sub
      (integrable_anchoredTest_mul χ hc _ (u i))
  have key : ∀ᵐ y ∂(anchoredMeasureE χ), anchoredVectorFormIntegrand χ
      (anchoredGradientTestTuple f) u y =
        inner ℝ (gradient (anchoredLangevinExpr χ f.val) y) (anchoredTestVector u y) + B y := by
    filter_upwards [ae_mem_anchoredSimplex χ] with y hy
    unfold anchoredVectorFormIntegrand
    rw [anchoredTestVector_gradientTestTuple f y, hessian_gradient_coordinates χ hy,
      inner_gradient_anchoredTestVector]
    simp only [B, anchoredTestVector, anchoredGradientTestTuple, sub_mul, Finset.sum_sub_distrib]
    ring_nf
  have hint : ∫ y, B y ∂(anchoredMeasureE χ) = 0 := by
    simp only [B]
    rw [integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro i _
      have hD := (anchoredGradientTestDirection f (EuclideanSpace.single i 1)).property
      have hIBP := anchoredIntegrationByParts χ hc hD.1 hD.2.1 hD.2.2
        (isAnchoredH1_of_testFunction χ (u i : AnchoredEuclidean n → ℝ) (u i).property.1
          (u i).property.2.1 inferInstance)
      have hi1 : Integrable (fun y => inner ℝ
          (gradient (anchoredGradientTestDirection f (EuclideanSpace.single i 1)).val y)
          (gradient (u i : AnchoredEuclidean n → ℝ) y)) (anchoredMeasureE χ) :=
        integrable_anchoredGradInner χ (anchoredMeasureE χ) (anchoredGradientTestTuple f) u i
      rw [integral_sub hi1 (integrable_anchoredTest_mul χ hc _ (u i)), hIBP, sub_self]
    · intro i _
      have hi1 : Integrable (fun y => inner ℝ
          (gradient (anchoredGradientTestDirection f (EuclideanSpace.single i 1)).val y)
          (gradient (u i : AnchoredEuclidean n → ℝ) y)) (anchoredMeasureE χ) :=
        integrable_anchoredGradInner χ (anchoredMeasureE χ) (anchoredGradientTestTuple f) u i
      exact hi1.sub (integrable_anchoredTest_mul χ hc _ (u i))
  have hL_int : Integrable (fun y => inner ℝ (gradient (anchoredLangevinExpr χ f.val) y)
      (anchoredTestVector u y)) (anchoredMeasureE χ) :=
    integrable_gradient_anchoredTestVector χ hc (anchoredGradientLangevinTest χ f) u
  unfold anchoredVectorForm
  rw [integral_congr_ae key, integral_add hL_int hB_int, hint, add_zero]

/-- The inner product of the gradient of a test function against a vector test tuple is the
weighted integral of the test function against the coefficient of the tuple. -/
theorem integral_inner_anchoredTestVector (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {F : AnchoredEuclidean n → ℝ} {G : AnchoredEuclidean n → AnchoredEuclidean n}
    (hFG : IsAnchoredH1 χ F G) (u : AnchoredVectorTest n) :
    ∫ y, inner ℝ (G y) (anchoredTestVector u y) ∂anchoredMeasureE χ =
      ∫ y, F y * anchoredWeakCoeff χ u y ∂anchoredMeasureE χ := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  have hpt (y : AnchoredEuclidean n) : inner ℝ (G y) (anchoredTestVector u y) =
      ∑ i : Fin n, (u i : AnchoredEuclidean n → ℝ) y *
        inner ℝ (G y) (EuclideanSpace.single i 1) := by
    have h := hsCommutator_linear_coordinates (innerSL ℝ (G y)) (anchoredTestVector u y)
    simp only [innerSL_apply_apply] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
    rfl
  have hcoef (i : Fin n) : Integrable (fun y => (u i : AnchoredEuclidean n → ℝ) y *
      inner ℝ (G y) (EuclideanSpace.single i 1)) (anchoredMeasureE χ) := by
    have hu2 : MemLp (fun y => (u i : AnchoredEuclidean n → ℝ) y) 2 (anchoredMeasureE χ) :=
      ((u i).property.1.continuous).memLp_of_hasCompactSupport (u i).property.2.1
    exact hu2.integrable_mul (hFG.2.1.inner_const (EuclideanSpace.single i 1))
  have hdir (i : Fin n) : ∫ y, (u i : AnchoredEuclidean n → ℝ) y *
      inner ℝ (G y) (EuclideanSpace.single i 1) ∂(anchoredMeasureE χ) =
        ∫ y, F y * ((u i : AnchoredEuclidean n → ℝ) y *
          fderiv ℝ (hsAnchoredHamiltonianE χ) y (EuclideanSpace.single i 1) -
          fderiv ℝ (u i : AnchoredEuclidean n → ℝ) y (EuclideanSpace.single i 1))
            ∂(anchoredMeasureE χ) :=
    anchoredH1_directional_integrationByParts χ hc hFG (u i).property.1 (u i).property.2.1
      (u i).property.2.2 _
  have hR : ∫ y, F y * anchoredWeakCoeff χ u y ∂(anchoredMeasureE χ) =
      ∑ i : Fin n, ∫ y, F y * ((u i : AnchoredEuclidean n → ℝ) y *
          fderiv ℝ (hsAnchoredHamiltonianE χ) y (EuclideanSpace.single i 1) -
          fderiv ℝ (u i : AnchoredEuclidean n → ℝ) y (EuclideanSpace.single i 1))
            ∂(anchoredMeasureE χ) := by
    rw [← integral_finsetSum]
    · apply integral_congr_ae
      filter_upwards with y
      simp only [anchoredWeakCoeff, Finset.mul_sum]
    · intro i _
      exact hFG.1.integrable_mul (memLp_anchoredCoefficient χ hc (u i).property.1
        (u i).property.2.1 (u i).property.2.2 _)
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun i _ => hcoef i), hR]
  exact Finset.sum_congr rfl (fun i _ => hdir i)

/-- The coefficient of a test tuple is square integrable against `μ*`. -/
theorem memLp_anchoredWeakCoeff (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (u : AnchoredVectorTest n) : MemLp (anchoredWeakCoeff χ u) 2 (anchoredMeasureE χ) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact memLp_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ =>
    memLp_anchoredCoefficient χ hc (u i).property.1 (u i).property.2.1 (u i).property.2.2
      (EuclideanSpace.single i 1))

/-- The function `fun _ => 1` lies in `H¹(μ*)`, with zero weak gradient. -/
theorem isAnchoredH1_const (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    IsAnchoredH1 χ (fun _ => (1 : ℝ)) (fun _ => (0 : AnchoredEuclidean n)) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  refine ⟨memLp_const _, memLp_const _, fun _ _ => (1 : ℝ),
    fun _ => ⟨univ, isOpen_univ, subset_univ _, contDiff_const.contDiffOn⟩, ?_, ?_⟩
  · simp
  · simp

/-- The coefficient of every test tuple has zero mean, since the function `fun _ => 1` has zero
weak gradient. -/
theorem integral_anchoredWeakCoeff_eq_zero (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (u : AnchoredVectorTest n) :
    ∫ y, anchoredWeakCoeff χ u y ∂anchoredMeasureE χ = 0 := by
  have h := integral_inner_anchoredTestVector χ hc (isAnchoredH1_const χ hc) u
  simpa using h.symm

/-- The vector form of a gradient tuple is the integral of the Langevin expression against the
coefficient of the tuple. This is the commutator step in Remark 3.2. -/
theorem anchoredVectorForm_gradientTest_coeff (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f : anchoredTestSubmodule n) (u : AnchoredVectorTest n) :
    anchoredVectorForm χ (anchoredGradientTestTuple f) u =
      ∫ y, anchoredLangevinExpr χ f.val y * anchoredWeakCoeff χ u y ∂anchoredMeasureE χ := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  rw [anchoredVectorForm_gradientTest χ hc f u]
  exact integral_inner_anchoredTestVector χ hc
    (isAnchoredH1_of_testFunction χ (anchoredLangevinExpr χ f.val)
      (anchoredGradient_langevin_smooth χ f) (anchoredGradientLangevinTest χ f).property.2.1
      inferInstance) u

end Riesz1

end
