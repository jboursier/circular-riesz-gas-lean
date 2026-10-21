/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GradientConvergenceEnergy
public import Riesz1.HelfferSjostrand.CoercivityBounds

/-! # Linear gradient jets on the test space

Linear maps into the existing operator domain and vector completion.
The integrated commutator identifies their norms without a new function space.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ContDiff

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

/-- Read a scalar test submodule element as the test-function structure. -/
def hsGradientSourceOfTest (f : hsTestSubmodule N) : HsTestFunction N :=
  ⟨f.val, f.property.1, f.property.2.1, f.property.2.2⟩

def hsGradientTestOfSource (f : HsTestFunction N) : hsTestSubmodule N :=
  ⟨f.toFun, f.smooth, f.periodic, f.boundarySupport⟩

theorem hsGradientSourceOfTest_of_source (f : HsTestFunction N) :
    hsGradientSourceOfTest (hsGradientTestOfSource f) = f := HsTestFunction.ext rfl

/-- Coordinate differentiation as a linear map on the test space. -/
def hsGradientTupleLin (hN : 2 ≤ (N : ℕ)) : hsTestSubmodule N →ₗ[ℝ] HsVectorTest N where
  toFun f := hsGradientTestTuple hN (hsGradientSourceOfTest f)
  map_add' f g := by
    funext i
    apply Subtype.ext
    funext x
    change fderiv ℝ (f.val + g.val) x (EuclideanSpace.single i 1) = _
    rw [fderiv_add (f.property.1.differentiable (by simp) x)
      (g.property.1.differentiable (by simp) x)]
    rfl
  map_smul' a f := by
    funext i
    apply Subtype.ext
    funext x
    change fderiv ℝ (a • f.val) x (EuclideanSpace.single i 1) = _
    rw [fderiv_const_smul (f.property.1.differentiable (by simp) x)]
    rfl

/-- The gradient jet in the vector completion. -/
def hsGradientFieldLin (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    hsTestSubmodule N →ₗ[ℝ] HsVectorSobolev χ hN hc μ :=
  ((hsVectorJetLin χ hN hc μ).comp (hsGradientTupleLin hN)).codRestrict _
    (fun _f => hsVectorJet_mem_submodule χ hN hc μ _)

/-- Scalar tests take values in the actual domain of `L₀`. -/
def hsGradientSourceDomainLin (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c) :
    hsTestSubmodule N →ₗ[ℝ] (hsTestL2Operator χ hc).domain :=
  (((hsSobolevValue _).toLinearMap).comp (hsTestSobolev _)).codRestrict _ (fun f => by
    rw [hsTestL2Operator_domain hN χ hc]
    exact (mem_hsTestL2Domain _ _).mpr ⟨hsGradientSourceOfTest f, rfl⟩)

/-- The existing test operator, applied linearly to the existing scalar test space. -/
def hsGradientSourceOperatorLin (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c) :
    hsTestSubmodule N →ₗ[ℝ] Lp ℝ 2
      (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) :=
  (hsTestL2Operator χ hc).toFun.comp (hsGradientSourceDomainLin χ hN hc)

theorem hsGradientSourceOperatorLin_eq (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ))
    (hc : 0 < c) (f : hsTestSubmodule N) :
    hsGradientSourceOperatorLin χ hN hc f =
      (memLp_hsLangevin hN χ (hsGradientSourceOfTest f)
        (hsQuotientGibbsProbability χ hc : Measure _)).toLp
          (hsLangevin χ (hsGradientSourceOfTest f)) := by
  obtain ⟨h, he⟩ := (LinearPMap.mem_graph_iff _).mp
    (hsTestL2Operator_on_test hN χ hc (hsGradientSourceOfTest f))
  have hh : h = hsGradientSourceDomainLin χ hN hc f := Subtype.ext he.1
  exact (congrArg (hsTestL2Operator χ hc) hh).symm.trans he.2

theorem hsGradientSourceOperatorLin_of_source (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ))
    (hc : 0 < c) (f : HsTestFunction N) :
    hsGradientSourceOperatorLin χ hN hc (hsGradientTestOfSource f) =
      (memLp_hsLangevin hN χ f (hsQuotientGibbsProbability χ hc : Measure _)).toLp
        (hsLangevin χ f) := by
  simpa only [hsGradientSourceOfTest_of_source] using
    hsGradientSourceOperatorLin_eq χ hN hc (hsGradientTestOfSource f)

theorem hsGradientFieldLin_of_source (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (f : HsTestFunction N) :
    hsGradientFieldLin χ hN hc μ (hsGradientTestOfSource f) =
      hsVectorJetElt χ hN hc μ (hsGradientTestTuple hN f) := by
  change hsVectorJetElt χ hN hc μ
    (hsGradientTestTuple hN (hsGradientSourceOfTest (hsGradientTestOfSource f))) = _
  rw [hsGradientSourceOfTest_of_source]

theorem hsGradientFieldLin_value (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (f : hsTestSubmodule N)
    (i : Fin (N : ℕ)) :
    hsJetValue μ i (hsGradientFieldLin χ hN hc μ f).val =
      (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ
        (hsSobolevGradient μ (hsTestSobolev μ f)) := by
  apply Lp.ext
  filter_upwards [hsSobolevValue_hsTestSobolev μ (hsGradientTupleLin hN f i),
    ContinuousLinearMap.coeFn_compLpL (EuclideanSpace.proj (𝕜 := ℝ) i)
      (hsSobolevGradient μ (hsTestSobolev μ f)),
    hsSobolevGradient_hsTestSobolev_ae μ f] with y hv hp hg
  change (hsSobolevValue μ (hsTestSobolev μ (hsGradientTupleLin hN f i))) y = _
  rw [hv, hp, hg]
  exact hsGradientTestTuple_apply hN (hsGradientSourceOfTest f) (hsLiftPoint N y) i

/-- The squared vector norm is value energy plus the existing vector form. -/
theorem hsGradient_vector_norm_sq (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (u : HsVectorSobolev χ hN hc μ) :
    ‖u‖ ^ 2 = hsVectorValueNormSq μ u.val + hsVectorSobolevForm χ hN hc μ u u := by
  change ‖u.val‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp_rw [hsSobolev_norm_sq]
  rw [Finset.sum_add_distrib, hsVectorSobolevForm_self]
  exact add_assoc _ _ _

theorem hsGradientFieldLin_valueNormSq (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (f : hsTestSubmodule N) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    hsVectorValueNormSq μ (hsGradientFieldLin χ hN hc μ f).val =
      ‖hsSobolevGradient μ (hsTestSobolev μ f)‖ ^ 2 := by
  dsimp only
  unfold hsVectorValueNormSq
  simp_rw [hsGradientFieldLin_value]
  exact sum_norm_sq_l2_coordinates _ _

theorem hsGradientFieldLin_form (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (f : hsTestSubmodule N) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    let u := hsGradientFieldLin χ hN hc μ f
    hsVectorSobolevForm χ hN hc μ u u = ‖hsGradientSourceOperatorLin χ hN hc f‖ ^ 2 := by
  dsimp only
  exact (hsGradient_vector_energy hN χ hc (hsGradientSourceOfTest f)).trans
    (congrArg (fun z => ‖z‖ ^ 2) (hsGradientSourceOperatorLin_eq χ hN hc f).symm)

/-- The gradient jet has precisely the graph energy prescribed by the commutator. -/
theorem hsGradientFieldLin_norm_sq (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (f : hsTestSubmodule N) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    ‖hsGradientFieldLin χ hN hc μ f‖ ^ 2 =
      ‖hsSobolevGradient μ (hsTestSobolev μ f)‖ ^ 2 + ‖hsGradientSourceOperatorLin χ hN hc f‖ ^ 2 := by
  exact (hsGradient_vector_norm_sq χ hN hc _ _).trans
    (congrArg₂ (· + ·) (hsGradientFieldLin_valueNormSq χ hN hc f) (hsGradientFieldLin_form χ hN hc f))

end Riesz1
