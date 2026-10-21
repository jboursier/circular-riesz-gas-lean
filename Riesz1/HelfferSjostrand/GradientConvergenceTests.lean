/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GradientConvergenceCommutator
public import Riesz1.HelfferSjostrand.VectorEnergySobolev
public import Riesz1.HelfferSjostrand.ScalarPoincareProductCore

/-! # Differentiation of the scalar source core

The gradient components of a scalar source test lie in the vector
test core. This is the test-domain ingredient of the integrated commutator.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology InnerProductSpace Metric
open scoped ContDiff Laplacian

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

/-- Directional differentiation preserves the collision-free periodic source core. -/
def hsGradientTestDirection (hN : 2 ≤ (N : ℕ)) (f : HsTestFunction N)
    (v : HsEuclidean N) : HsTestFunction N where
  toFun x := fderiv ℝ f.toFun x v
  smooth := (f.smooth.fderiv_right (by simp)).clm_apply contDiff_const
  periodic k x := by
    rw [← inner_gradient_left, ← inner_gradient_left,
      scalarPoincare_gradient_translate f.smoothOnClosure]
  boundarySupport := by
    obtain ⟨δ, hδ, hs⟩ := f.support_distance hN
    have hcl : tsupport f.toFun ⊆ {x | δ ≤ hsBoundaryDistance N hN x} :=
      closure_minimal hs (isClosed_le continuous_const (hsBoundaryDistance_lipschitz N hN).continuous)
    refine ⟨δ, hδ, fun x hx => ?_⟩
    have hxf : x ∈ tsupport f.toFun := by
      by_contra h
      exact hx (by rw [fderiv_of_notMem_tsupport ℝ h]; rfl)
    exact (ENNReal.ofReal_le_iff_le_toReal
      (infEDist_ne_top (hsChamber_compl_nonempty hN))).mpr (hcl hxf)

/-- The test tuple of coordinate derivatives, in the existing vector test space. -/
def hsGradientTestTuple (hN : 2 ≤ (N : ℕ)) (f : HsTestFunction N) : HsVectorTest N :=
  fun i => let g := hsGradientTestDirection hN f (EuclideanSpace.single i 1)
    ⟨g.toFun, g.smooth, g.periodic, g.boundarySupport⟩

theorem hsGradientTestTuple_apply (hN : 2 ≤ (N : ℕ)) (f : HsTestFunction N)
    (x : HsEuclidean N) (i : Fin (N : ℕ)) :
    (hsGradientTestTuple hN f i : HsEuclidean N → ℝ) x = gradient f.toFun x i := by
  change fderiv ℝ f.toFun x (EuclideanSpace.single i 1) = _
  rw [← inner_gradient_left]
  simpa only [EuclideanSpace.basisFun_apply] using
    EuclideanSpace.inner_basisFun_real (Fin (N : ℕ)) (gradient f.toFun x) i

theorem hsTestVector_gradientTestTuple (hN : 2 ≤ (N : ℕ)) (f : HsTestFunction N)
    (x : HsEuclidean N) : hsTestVector (hsGradientTestTuple hN f) x = gradient f.toFun x := by
  ext i
  exact hsGradientTestTuple_apply hN f x i

theorem hsGradient_fderiv_translate {g : HsEuclidean N → ℝ}
    (hp : ∀ (k : ℤ) x, g (hsTranslate (k : ℝ) x) = g x) (k : ℤ) (x : HsEuclidean N) :
    fderiv ℝ g (hsTranslate (k : ℝ) x) = fderiv ℝ g x := by
  have he : (fun y => g (y + WithLp.toLp 2 (fun _ : Fin (N : ℕ) => (k : ℝ)))) = g :=
    funext (hp k)
  change fderiv ℝ g (x + WithLp.toLp 2 (fun _ : Fin (N : ℕ) => (k : ℝ))) = _
  rw [← fderiv_comp_add_right, he]

theorem hsGradient_laplacian_translate {g : HsEuclidean N → ℝ}
    (hp : ∀ (k : ℤ) x, g (hsTranslate (k : ℝ) x) = g x) (k : ℤ) (x : HsEuclidean N) :
    Δ g (hsTranslate (k : ℝ) x) = Δ g x := by
  have he : (fun y => g (y + WithLp.toLp 2 (fun _ : Fin (N : ℕ) => (k : ℝ)))) = g :=
    funext (hp k)
  have hd : iteratedFDeriv ℝ 2 g (hsTranslate (k : ℝ) x) = iteratedFDeriv ℝ 2 g x := by
    change iteratedFDeriv ℝ 2 g (x + WithLp.toLp 2 (fun _ : Fin (N : ℕ) => (k : ℝ))) = _
    rw [← iteratedFDeriv_comp_add_right 2 _ x, he]
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, hd]

/-- The differential expression of a source test is again globally smooth. -/
theorem hsGradient_contDiff_langevin (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c)
    (f : HsTestFunction N) : ContDiff ℝ ∞ (fun x : HsEuclidean N =>
      inner ℝ (gradient (hsPairExpression χ) x) (gradient f.toFun x) - Δ f.toFun x) := by
  have hgf : ContDiff ℝ ∞ (gradient f.toFun) :=
    (toDual ℝ (HsEuclidean N)).symm.toContinuousLinearEquiv.contDiff.comp
      (f.smooth.fderiv_right (by simp))
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ hsChamber N
  · have hH := (hsPairExpression_contDiffOn χ).contDiffAt ((isOpen_hsChamber N).mem_nhds hx)
    have hgH : ContDiffAt ℝ ∞ (gradient (hsPairExpression χ)) x :=
      (toDual ℝ (HsEuclidean N)).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x
        (hH.fderiv_right (by simp))
    exact (hgH.inner ℝ hgf.contDiffAt).sub (contDiff_laplacian f.smooth).contDiffAt
  · have hxs : x ∉ tsupport f.toFun := fun hx' => hx (f.tsupport_subset_chamber hN hx')
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport f.toFun).isOpen_compl.mem_nhds hxs] with y hy
    exact hsLangevinExpression_eq_zero_of_not_mem_tsupport χ f hy

/-- The actual differential source operator maps its test class to itself. -/
def hsLangevinTest (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c)
    (f : HsTestFunction N) : HsTestFunction N where
  toFun x := inner ℝ (gradient (hsPairExpression χ) x) (gradient f.toFun x) - Δ f.toFun x
  smooth := hsGradient_contDiff_langevin hN χ f
  periodic k x := by
    have hH := hsGradient_fderiv_translate (fun k x => hsPairExpression_translate χ (k : ℝ) x) k x
    have hf := hsGradient_fderiv_translate f.periodic k x
    unfold gradient
    rw [hH, hf, hsGradient_laplacian_translate f.periodic]
  boundarySupport := by
    obtain ⟨δ, hδ, hs⟩ := f.support_distance hN
    have hcl : tsupport f.toFun ⊆ {x | δ ≤ hsBoundaryDistance N hN x} :=
      closure_minimal hs (isClosed_le continuous_const (hsBoundaryDistance_lipschitz N hN).continuous)
    refine ⟨δ, hδ, fun x hx => ?_⟩
    have hxf : x ∈ tsupport f.toFun := by
      by_contra h
      exact hx (hsLangevinExpression_eq_zero_of_not_mem_tsupport χ f h)
    exact (ENNReal.ofReal_le_iff_le_toReal
      (infEDist_ne_top (hsChamber_compl_nonempty hN))).mpr (hcl hxf)

theorem hsLangevinTest_onQuotient (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c)
    (f : HsTestFunction N) : hsTestOnQuotient (hsLangevinTest hN χ f) = hsLangevin χ f := rfl

theorem hsGradient_dirichlet_tests (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]
    (f g : HsTestFunction N) :
    hsDirichletForm μ (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩)
      (hsSobolevOfSmooth μ ⟨g.toFun, g.smoothOnClosure⟩) =
      ∫ y, inner ℝ (gradient f.toFun (hsLiftPoint N y)) (gradient g.toFun (hsLiftPoint N y)) ∂μ := by
  rw [hsDirichletForm_eq_integral]
  apply integral_congr_ae
  filter_upwards [(f.smoothOnClosure.memLp_gradient μ).coeFn_toLp,
    (g.smoothOnClosure.memLp_gradient μ).coeFn_toLp] with y hf hg
  change inner ℝ (((f.smoothOnClosure.memLp_gradient μ).toLp _) y)
    (((g.smoothOnClosure.memLp_gradient μ).toLp _) y) = _
  rw [hf, hg]
  rfl

end Riesz1
