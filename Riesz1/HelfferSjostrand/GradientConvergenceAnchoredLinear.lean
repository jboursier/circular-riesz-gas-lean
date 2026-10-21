/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GradientConvergenceAnchoredScalar
public import Riesz1.HelfferSjostrand.AnchoredInverseSpace

/-! # Anchored gradient jets and their graph norm

Linear maps on the existing anchored test space, into the operator on test
functions and the vector completion. No new scalar or vector space is defined.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

variable {n : ℕ} {c : ℝ}

def anchoredGradientTupleLin : anchoredTestSubmodule n →ₗ[ℝ] AnchoredVectorTest n where
  toFun := anchoredGradientTestTuple
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

def anchoredGradientFieldLin (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    anchoredTestSubmodule n →ₗ[ℝ] AnchoredVectorSobolev χ (anchoredMeasureE χ) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact ((anchoredVectorJetLin χ (anchoredMeasureE χ)).comp anchoredGradientTupleLin).codRestrict _
    (fun f => Submodule.le_topologicalClosure _ ⟨anchoredGradientTestTuple f, rfl⟩)

def anchoredGradientSourceDomainLin (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    anchoredTestSubmodule n →ₗ[ℝ] (anchoredTestL2Operator χ hc).domain :=
  ((poissonAnchoredValue χ hc).toLinearMap.comp (anchoredTestHilbert χ hc)).codRestrict _ (fun f => by
    rw [anchoredTestL2Operator_domain χ hc]
    exact (mem_anchoredTestL2Domain χ hc _).mpr ⟨f, rfl⟩)

def anchoredGradientSourceOperatorLin (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    anchoredTestSubmodule n →ₗ[ℝ] Lp ℝ 2 (anchoredMeasureE χ) :=
  (anchoredTestL2Operator χ hc).toFun.comp (anchoredGradientSourceDomainLin χ hc)

theorem anchoredGradientSourceOperatorLin_eq (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f : anchoredTestSubmodule n) :
    anchoredGradientSourceOperatorLin χ hc f =
      (memLp_anchoredLangevinExpr χ hc f.property.1 f.property.2.1 f.property.2.2).toLp
        (anchoredLangevinExpr χ f.val) := by
  obtain ⟨h, he⟩ := (LinearPMap.mem_graph_iff _).mp (anchoredTestL2Operator_on_test χ hc f)
  have hh : h = anchoredGradientSourceDomainLin χ hc f := Subtype.ext he.1
  exact (congrArg (anchoredTestL2Operator χ hc) hh).symm.trans he.2

theorem anchoredGradientFieldLin_values (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    ∀ f : anchoredTestSubmodule n,
      anchoredInverseValues (anchoredMeasureE χ) (anchoredGradientFieldLin χ hc f).val =
        poissonAnchoredGradient χ hc (anchoredTestHilbert χ hc f) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  intro f
  apply Lp.ext
  filter_upwards [anchoredInverseValues_jet_ae (anchoredMeasureE χ) χ (anchoredGradientTestTuple f),
    anchoredGradient_gradient_ae χ hc f] with y hv hg
  change (anchoredInverseValues (anchoredMeasureE χ)
    (anchoredVectorJet χ (anchoredMeasureE χ) (anchoredGradientTestTuple f)) :
      AnchoredEuclidean n → AnchoredEuclidean n) y = _
  rw [hv, hg]
  exact anchoredTestVector_gradientTestTuple f y

theorem anchoredGradientFieldLin_norm_sq (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    ∀ f : anchoredTestSubmodule n,
      ‖anchoredGradientFieldLin χ hc f‖ ^ 2 =
        ‖poissonAnchoredGradient χ hc (anchoredTestHilbert χ hc f)‖ ^ 2 +
          ‖anchoredGradientSourceOperatorLin χ hc f‖ ^ 2 := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  intro f
  have hn := anchoredInverse_norm_sq (anchoredMeasureE χ) (anchoredGradientFieldLin χ hc f).val
  rw [anchoredGradientFieldLin_values,
    ← real_inner_self_eq_norm_sq (x := anchoredInverseDerivatives (anchoredMeasureE χ)
      (anchoredGradientFieldLin χ hc f).val), anchoredInverseDerivatives_inner] at hn
  have he := anchoredGradient_vector_energy χ hc f
  change anchoredVectorSobolevForm (anchoredMeasureE χ) (anchoredGradientFieldLin χ hc f).val
    (anchoredGradientFieldLin χ hc f).val = _ at he
  rw [← anchoredGradientSourceOperatorLin_eq χ hc f] at he
  exact hn.trans (congrArg (‖poissonAnchoredGradient χ hc (anchoredTestHilbert χ hc f)‖ ^ 2 + ·) he)

end Riesz1
