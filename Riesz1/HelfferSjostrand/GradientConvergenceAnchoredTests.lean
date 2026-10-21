/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GradientConvergenceEnergy
public import Riesz1.HelfferSjostrand.VectorEnergyAnchoredSobolev

/-! # Anchored derivative and Langevin tests

The anchored source class is closed under differentiation and its Langevin
expression. These assertions use compact interior support, without a core theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ContDiff Laplacian

namespace Riesz1

variable {n : ℕ} {c : ℝ}

def anchoredGradientTestDirection (f : anchoredTestSubmodule n) (v : AnchoredEuclidean n) :
    anchoredTestSubmodule n :=
  ⟨fun x => fderiv ℝ f.val x v,
    (f.property.1.fderiv_right (by simp)).clm_apply contDiff_const,
    f.property.2.1.fderiv_apply ℝ v, (tsupport_fderiv_apply_subset ℝ v).trans f.property.2.2⟩

def anchoredGradientTestTuple (f : anchoredTestSubmodule n) : AnchoredVectorTest n :=
  fun i => anchoredGradientTestDirection f (EuclideanSpace.single i 1)

theorem anchoredGradientTestTuple_apply (f : anchoredTestSubmodule n)
    (x : AnchoredEuclidean n) (i : Fin n) :
    (anchoredGradientTestTuple f i).val x = gradient f.val x i := by
  change fderiv ℝ f.val x (EuclideanSpace.single i 1) = _
  rw [← inner_gradient_left]
  simpa only [EuclideanSpace.basisFun_apply] using
    EuclideanSpace.inner_basisFun_real (Fin n) (gradient f.val x) i

theorem anchoredTestVector_gradientTestTuple (f : anchoredTestSubmodule n)
    (x : AnchoredEuclidean n) : anchoredTestVector (anchoredGradientTestTuple f) x = gradient f.val x := by
  ext i
  exact anchoredGradientTestTuple_apply f x i

theorem anchoredGradient_langevin_zero (χ : HsPairPotentials n.succPNat c)
    (f : anchoredTestSubmodule n) {x : AnchoredEuclidean n} (hx : x ∉ tsupport f.val) :
    anchoredLangevinExpr χ f.val x = 0 := by
  have heq : f.val =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := notMem_tsupport_iff_eventuallyEq.mp hx
  have hg := heq.gradient_eq
  have hl := (InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds
  simp only [gradient_fun_const] at hg
  simp only [InnerProductSpace.laplacian_const, Pi.zero_apply] at hl
  simp only [anchoredLangevinExpr, hg, hl, inner_zero_right, sub_self]

theorem anchoredGradient_langevin_tsupport (χ : HsPairPotentials n.succPNat c)
    (f : anchoredTestSubmodule n) : tsupport (anchoredLangevinExpr χ f.val) ⊆ tsupport f.val := by
  apply closure_minimal ?_ (isClosed_tsupport f.val)
  intro x hx
  by_contra h
  exact hx (anchoredGradient_langevin_zero χ f h)

theorem anchoredGradient_langevin_smooth (χ : HsPairPotentials n.succPNat c)
    (f : anchoredTestSubmodule n) : ContDiff ℝ ∞ (anchoredLangevinExpr χ f.val) := by
  have hgf : ContDiff ℝ ∞ (gradient f.val) :=
    (toDual ℝ (AnchoredEuclidean n)).symm.toContinuousLinearEquiv.contDiff.comp
      (f.property.1.fderiv_right (by simp))
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ anchoredSimplex n
  · have hH := (contDiffOn_hsAnchoredHamiltonianE χ).contDiffAt
      ((isOpen_anchoredSimplex n).mem_nhds hx)
    have hgH : ContDiffAt ℝ ∞ (gradient (hsAnchoredHamiltonianE χ)) x :=
      (toDual ℝ (AnchoredEuclidean n)).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x
        (hH.fderiv_right (by simp))
    exact (hgH.inner ℝ hgf.contDiffAt).sub (contDiff_laplacian f.property.1).contDiffAt
  · have hxs : x ∉ tsupport f.val := fun h => hx (f.property.2.2 h)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport f.val).isOpen_compl.mem_nhds hxs] with y hy
    exact anchoredGradient_langevin_zero χ f hy

def anchoredGradientLangevinTest (χ : HsPairPotentials n.succPNat c)
    (f : anchoredTestSubmodule n) : anchoredTestSubmodule n :=
  ⟨anchoredLangevinExpr χ f.val, anchoredGradient_langevin_smooth χ f,
    f.property.2.1.of_isClosed_subset (isClosed_tsupport _) (anchoredGradient_langevin_tsupport χ f),
    (anchoredGradient_langevin_tsupport χ f).trans f.property.2.2⟩

end Riesz1
