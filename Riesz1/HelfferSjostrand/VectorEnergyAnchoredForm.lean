/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.VectorEnergyAnchored
public import Riesz1.HelfferSjostrand.GeometryHessian
public import Riesz1.HelfferSjostrand.VectorEnergyForm

/-!
# The anchored Hessian energy and the anchored vector form

The anchored coordinates
`y = (y_1, …, y_n)` of the simplex `D_N^*` lift linearly to the `n + 1` particle configuration
`(0, y_1, …, y_n)`. The anchored Hamiltonian is the pair expression at this lift, so its Hessian is
the ambient Hessian on lifted vectors. Hence the anchored Hessian form has the pair energy
representation of `inner_hsHessianEnergy`, evaluated at the lift.

This file proves:
* the chain rule `∇²H*(y)[b, b'] = ∇²H(L y)[L b, L b']` for the linear lift `L`.
* the energy identity `b · ∇²H* b' = ⟪E_y(b), E_y(b')⟫` at every point of the simplex.
* the anchored integrand is the sum of the gradient and energy products.
* the anchored energy of a test tuple is continuous with compact support.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff InnerProductSpace

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- The linear lift `y ↦ (0, y_1, …, y_n)` of anchored coordinates to the configuration of
`n + 1` particles, with the anchor in position `0`. -/
def anchorLiftLin (n : ℕ) : AnchoredEuclidean n →ₗ[ℝ] HsEuclidean n.succPNat where
  toFun y := WithLp.toLp 2 (anchorVector (WithLp.ofLp y))
  map_add' y z := by
    ext i
    induction i using Fin.cases with
    | zero => exact (add_zero (0 : ℝ)).symm
    | succ k => rfl
  map_smul' a y := by
    ext i
    induction i using Fin.cases with
    | zero => exact (mul_zero a).symm
    | succ k => rfl

/-- The continuous lift `L : y ↦ (0, y_1, …, y_n)` of anchored coordinates. -/
def anchorLift (n : ℕ) : AnchoredEuclidean n →L[ℝ] HsEuclidean n.succPNat :=
  LinearMap.toContinuousLinearMap (anchorLiftLin n)

theorem anchorLift_apply (y : AnchoredEuclidean n) :
    anchorLift n y = WithLp.toLp 2 (anchorVector (WithLp.ofLp y)) := rfl

/-- The lift of a point of the anchored domain lies in the lifted chamber. -/
theorem anchorLift_mem_chamber {y : AnchoredEuclidean n} (hy : WithLp.ofLp y ∈ anchoredDomain n) :
    anchorLift n y ∈ hsChamber n.succPNat := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    exact anchorVector_strictMono hy hij
  · intro i
    have h0 : anchorLift n y ⟨0, n.succPNat.pos⟩ = 0 := by
      simp [anchorLift_apply, anchorVector]
    rw [h0, zero_add, anchorLift_apply]
    have := anchorVector_mem_Ico hy i
    exact this.2

/-- The anchored Hamiltonian is the pair expression at the lift. -/
theorem hsAnchoredHamiltonianE_eq_comp (χ : HsPairPotentials n.succPNat c) :
    hsAnchoredHamiltonianE χ = hsPairExpression χ ∘ anchorLift n :=
  rfl

/-- The Hessian of the anchored Hamiltonian is the ambient Hessian on lifted vectors. -/
theorem fderiv_fderiv_hsAnchoredHamiltonianE (χ : HsPairPotentials n.succPNat c)
    {y : AnchoredEuclidean n} (hy : anchorLift n y ∈ hsChamber n.succPNat)
    (u v : AnchoredEuclidean n) :
    fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) y u v =
      fderiv ℝ (fderiv ℝ (hsPairExpression χ)) (anchorLift n y) (anchorLift n u)
        (anchorLift n v) := by
  rw [hsAnchoredHamiltonianE_eq_comp]
  have hgrad : fderiv ℝ (hsPairExpression χ ∘ anchorLift n) =ᶠ[𝓝 y]
      fun z => (hsPairGradient χ (anchorLift n z)).comp (anchorLift n) := by
    have hopen : IsOpen (anchorLift n ⁻¹' hsChamber n.succPNat) :=
      (isOpen_hsChamber _).preimage (anchorLift n).continuous
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact ((hasFDerivAt_hsPairExpression χ hz).comp z (anchorLift n).hasFDerivAt).fderiv
  rw [hgrad.fderiv_eq]
  have hc : HasFDerivAt (fun z => hsPairGradient χ (anchorLift n z))
      ((hsPairHessian χ (anchorLift n y)).comp (anchorLift n)) y :=
    (hasFDerivAt_hsPairGradient χ hy).comp y (anchorLift n).hasFDerivAt
  have hd := hc.clm_comp (hasFDerivAt_const (anchorLift n) y)
  rw [hd.fderiv, fderiv_fderiv_hsPairExpression χ hy]
  simp [ContinuousLinearMap.comp_apply]
  rfl

/-- The anchored pair Hessian energy at the anchored coordinate `y` of the vector `b`: the Hessian
energy of the lifted vector `(0, b)` at the lifted point `(0, y)`. -/
def anchoredHessianEnergy (χ : HsPairPotentials n.succPNat c) (y b : AnchoredEuclidean n) :
    EuclideanSpace ℝ (HsPairIndex n.succPNat) :=
  hsHessianEnergy χ (anchorLift n y) (anchorLift n b)

/-- The anchored energy identity: `b · ∇²H* b' = ⟪E_y(b), E_y(b')⟫` on the simplex. -/
theorem inner_anchoredHessianEnergy (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {y : AnchoredEuclidean n} (hy : anchorLift n y ∈ hsChamber n.succPNat)
    (u v : AnchoredEuclidean n) :
    inner ℝ (anchoredHessianEnergy χ y u) (anchoredHessianEnergy χ y v) =
      fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) y u v := by
  rw [fderiv_fderiv_hsAnchoredHamiltonianE χ hy]
  exact inner_hsHessianEnergy χ hc hy (anchorLift n u) (anchorLift n v)

/-- The pair Hessian energy of a test tuple at an anchored coordinate. -/
def anchoredEnergyFun (χ : HsPairPotentials n.succPNat c) (u : AnchoredVectorTest n)
    (y : AnchoredEuclidean n) : EuclideanSpace ℝ (HsPairIndex n.succPNat) :=
  anchoredHessianEnergy χ y (anchoredTestVector u y)

/-- On the simplex, the anchored integrand is the sum of the gradient products and
the energy product. -/
theorem anchoredVectorFormIntegrand_eq (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {u h : AnchoredVectorTest n} {y : AnchoredEuclidean n}
    (hy : anchorLift n y ∈ hsChamber n.succPNat) :
    anchoredVectorFormIntegrand χ u h y =
      ∑ i, inner ℝ (gradient (u i : AnchoredEuclidean n → ℝ) y)
          (gradient (h i : AnchoredEuclidean n → ℝ) y) +
        inner ℝ (anchoredEnergyFun χ u y) (anchoredEnergyFun χ h y) := by
  unfold anchoredVectorFormIntegrand anchoredEnergyFun
  rw [inner_anchoredHessianEnergy χ hc hy]

/-- The weight `√(2 χ_ij''(y_j - y_i))` of a pair is continuous on the simplex, after lifting. -/
theorem continuousOn_anchoredEnergyWeight (χ : HsPairPotentials n.succPNat c)
    (p : HsPairIndex n.succPNat) :
    ContinuousOn (fun y : AnchoredEuclidean n => hsEnergyWeight χ p (anchorLift n y))
      (anchoredSimplex n) := by
  have hd2 : ContinuousOn (deriv (deriv (χ.potential p.1.1 p.1.2))) (Ioo 0 1) :=
    ((χ.smooth p.1.1 p.1.2 p.2).deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn_deriv_of_isOpen
      isOpen_Ioo (by norm_num)
  unfold hsEnergyWeight
  refine ContinuousOn.sqrt (continuousOn_const.mul ?_)
  refine hd2.comp ?_ ?_
  · exact (((EuclideanSpace.proj p.1.2).continuous.comp (anchorLift n).continuous).sub
      ((EuclideanSpace.proj p.1.1).continuous.comp (anchorLift n).continuous)).continuousOn
  · intro y hy
    exact anchorVector_sub_mem_Ioo hy p.2

/-- The anchored test vector `(u_1(y), …, u_n(y))` is continuous in `y`. -/
theorem continuous_anchoredTestVector (u : AnchoredVectorTest n) :
    Continuous (anchoredTestVector u) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => (u i).2.1.continuous)

/-- The anchored energy of a test tuple is continuous on the simplex. -/
theorem continuousOn_anchoredEnergyFun (χ : HsPairPotentials n.succPNat c)
    (u : AnchoredVectorTest n) :
    ContinuousOn (anchoredEnergyFun χ u) (anchoredSimplex n) := by
  unfold anchoredEnergyFun anchoredHessianEnergy hsHessianEnergy
  refine (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.mpr fun p => ?_)
  refine (continuousOn_anchoredEnergyWeight χ p).mul ?_
  refine ContinuousOn.sub ?_ ?_
  · exact ((EuclideanSpace.proj p.1.2).continuous.comp ((anchorLift n).continuous.comp
      (continuous_anchoredTestVector u))).continuousOn
  · exact ((EuclideanSpace.proj p.1.1).continuous.comp ((anchorLift n).continuous.comp
      (continuous_anchoredTestVector u))).continuousOn

/-- The anchored test vector is additive in the tuple. -/
theorem anchoredTestVector_add (u v : AnchoredVectorTest n) (y : AnchoredEuclidean n) :
    anchoredTestVector (u + v) y = anchoredTestVector u y + anchoredTestVector v y := by
  ext i
  simp [anchoredTestVector]

/-- The anchored test vector is homogeneous in the tuple. -/
theorem anchoredTestVector_smul (a : ℝ) (u : AnchoredVectorTest n) (y : AnchoredEuclidean n) :
    anchoredTestVector (a • u) y = a • anchoredTestVector u y := by
  ext i
  simp [anchoredTestVector]

/-- The anchored energy of a tuple is additive in the tuple. -/
theorem anchoredEnergyFun_add (χ : HsPairPotentials n.succPNat c) (u v : AnchoredVectorTest n)
    (y : AnchoredEuclidean n) :
    anchoredEnergyFun χ (u + v) y = anchoredEnergyFun χ u y + anchoredEnergyFun χ v y := by
  unfold anchoredEnergyFun anchoredHessianEnergy
  rw [anchoredTestVector_add, map_add, hsHessianEnergy_add]

/-- The anchored energy of a tuple is homogeneous in the tuple. -/
theorem anchoredEnergyFun_smul (χ : HsPairPotentials n.succPNat c) (a : ℝ)
    (u : AnchoredVectorTest n) (y : AnchoredEuclidean n) :
    anchoredEnergyFun χ (a • u) y = a • anchoredEnergyFun χ u y := by
  unfold anchoredEnergyFun anchoredHessianEnergy
  rw [anchoredTestVector_smul, map_smul, hsHessianEnergy_smul]

/-- The pair Hessian energy of the zero vector vanishes. -/
theorem hsHessianEnergy_zero_right (χ : HsPairPotentials n.succPNat c) (y : HsEuclidean n.succPNat) :
    hsHessianEnergy χ y 0 = 0 := by
  have h := hsHessianEnergy_smul χ y 0 0
  rwa [zero_smul, zero_smul] at h

/-- The anchored energy vanishes where every component of the tuple vanishes. -/
theorem anchoredEnergyFun_eq_zero (χ : HsPairPotentials n.succPNat c) (u : AnchoredVectorTest n)
    {y : AnchoredEuclidean n} (hy : ∀ i, y ∉ tsupport (u i : AnchoredEuclidean n → ℝ)) :
    anchoredEnergyFun χ u y = 0 := by
  have hv : anchoredTestVector u y = 0 := by
    ext i
    simp [anchoredTestVector, image_eq_zero_of_notMem_tsupport (hy i)]
  unfold anchoredEnergyFun anchoredHessianEnergy
  rw [hv, map_zero, hsHessianEnergy_zero_right]

/-- The union of the supports of the components of a test tuple. -/
def anchoredSupportUnion (u : AnchoredVectorTest n) : Set (AnchoredEuclidean n) :=
  ⋃ i, tsupport (u i : AnchoredEuclidean n → ℝ)

/-- The union of the supports of a test tuple is compact and lies in the simplex. -/
theorem isCompact_anchoredSupportUnion (u : AnchoredVectorTest n) :
    IsCompact (anchoredSupportUnion u) :=
  isCompact_iUnion fun i => (u i).2.2.1.isCompact

theorem anchoredSupportUnion_subset (u : AnchoredVectorTest n) :
    anchoredSupportUnion u ⊆ anchoredSimplex n :=
  iUnion_subset fun i => (u i).2.2.2

/-- The test tuple's anchored energy is continuous on the simplex and vanishes off the union of
the supports, so it is continuous on the whole space. -/
theorem continuous_anchoredEnergyFun (χ : HsPairPotentials n.succPNat c) (u : AnchoredVectorTest n) :
    Continuous (anchoredEnergyFun χ u) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ anchoredSimplex n
  · exact (continuousOn_anchoredEnergyFun χ u).continuousAt ((isOpen_anchoredSimplex n).mem_nhds hy)
  · have hyK : y ∉ anchoredSupportUnion u := fun h => hy (anchoredSupportUnion_subset u h)
    have hopen : IsOpen (anchoredSupportUnion u)ᶜ :=
      (isCompact_anchoredSupportUnion u).isClosed.isOpen_compl
    refine (continuousAt_const :
      ContinuousAt (fun _ : AnchoredEuclidean n => (0 : EuclideanSpace ℝ (HsPairIndex n.succPNat)))
        y).congr ?_
    filter_upwards [hopen.mem_nhds hyK] with z hz
    exact (anchoredEnergyFun_eq_zero χ u fun i hi => hz (mem_iUnion.mpr ⟨i, hi⟩)).symm

/-- The anchored energy of a test tuple has compact support. -/
theorem hasCompactSupport_anchoredEnergyFun (χ : HsPairPotentials n.succPNat c)
    (u : AnchoredVectorTest n) : HasCompactSupport (anchoredEnergyFun χ u) :=
  HasCompactSupport.intro (isCompact_anchoredSupportUnion u) fun _ hy =>
    anchoredEnergyFun_eq_zero χ u fun i hi => hy (mem_iUnion.mpr ⟨i, hi⟩)

end Riesz1

end
