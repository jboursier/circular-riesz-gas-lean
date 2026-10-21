/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BoundaryCoreQuotient
public import Riesz1.HelfferSjostrand.BoundaryCoreAnchored
public import Riesz1.ToMathlib.ComplexL2Operator
public import Riesz1.ToMathlib.ComplexFormCore
public import Riesz1.HelfferSjostrand.BoundaryCoreTestBridge

/-!
# Complex scalar boundary cores

Complex L² operators are specified by the real and imaginary parts of
the real variational operators. Complex form topology is realized
by the two existing real Sobolev components, with their sum-of-squares
norm. No new weak-gradient or Neumann relation is introduced.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

/-- The actual complex source domain: both real components are actual source tests. -/
def hsComplexTestL2Domain (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    Submodule ℂ (Lp ℂ 2 μ) := complexifyL2Submodule μ (hsTestL2Domain μ)

/-- The complex variational Neumann operator, acting separately on the two real components. -/
def hsComplexNeumannL2Operator (χ : HsPairPotentials N c) (hc : 0 < c) :
    Lp ℂ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) →ₗ.[ℂ]
      Lp ℂ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) :=
  complexifyL2Operator _ (hsNeumannL2Operator χ hc)

/-- The complex source differential operator on precisely the source domain. -/
def hsComplexTestL2Operator (χ : HsPairPotentials N c) (hc : 0 < c) :
    Lp ℂ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) →ₗ.[ℂ]
      Lp ℂ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) :=
  complexifyL2Operator _ (hsTestL2Operator χ hc)

/-- The complex Neumann graph is exactly the two real variational graph equations. -/
theorem mem_hsComplexNeumannL2Operator_graph (χ : HsPairPotentials N c) (hc : 0 < c)
    (f a : Lp ℂ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    (f, a) ∈ (hsComplexNeumannL2Operator χ hc).graph ↔
      (complexL2Re _ f, complexL2Re _ a) ∈ (hsNeumannL2Operator χ hc).graph ∧
        (complexL2Im _ f, complexL2Im _ a) ∈ (hsNeumannL2Operator χ hc).graph :=
  mem_complexifyL2Operator_graph _ _ f a

/-- The complex H¹ form topology, in real and imaginary coordinates of the existing space. -/
abbrev HsComplexSobolev (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :=
  WithLp 2 (HsSobolev μ × HsSobolev μ)

/-- The complex source forms in the existing Sobolev coordinates. -/
def hsComplexSourceTestSobolev (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    Set (HsComplexSobolev μ) := complexFormTests (hsSourceTestSobolev μ)

/-- The real-coordinate norm is exactly the complex H¹ norm. -/
theorem hsComplexSobolev_norm_sq (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]
    (f : HsComplexSobolev μ) :
    ‖f‖ ^ 2 = (‖hsSobolevValue μ f.ofLp.1‖ ^ 2 + ‖hsSobolevValue μ f.ofLp.2‖ ^ 2) +
      (‖hsSobolevGradient μ f.ofLp.1‖ ^ 2 + ‖hsSobolevGradient μ f.ofLp.2‖ ^ 2) := by
  rw [WithLp.prod_norm_sq_eq_of_L2, hsSobolev_norm_sq, hsSobolev_norm_sq]
  dsimp only [WithLp.fst, WithLp.snd]
  ring

theorem hsComplexTestL2Operator_domain (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c) (hc : 0 < c) :
    (hsComplexTestL2Operator χ hc).domain =
      hsComplexTestL2Domain (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
  rw [hsComplexTestL2Operator, complexifyL2Operator_domain, hsTestL2Operator_domain hN χ hc]
  rfl

/-- On a complex source test `f + i g`, the operator is the complex Langevin expression. -/
theorem hsComplexTestL2Operator_on_test (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c)
    (hc : 0 < c) (f g : HsTestFunction N) :
    let μ := (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
    (complexL2OfPair μ
      (hsSobolevValue μ (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩),
       hsSobolevValue μ (hsSobolevOfSmooth μ ⟨g.toFun, g.smoothOnClosure⟩)),
      complexL2OfPair μ
        ((memLp_hsLangevin hN χ f μ).toLp (hsLangevin χ f),
         (memLp_hsLangevin hN χ g μ).toLp (hsLangevin χ g))) ∈
      (hsComplexTestL2Operator χ hc).graph :=
  complexifyL2Operator_on_pair _ _ (hsTestL2Operator_on_test hN χ hc f)
    (hsTestL2Operator_on_test hN χ hc g)

/-- The full complex quotient component of the scalar boundary core theorem. -/
theorem scalar_boundary_core_L3219_quotient_complex {C_N : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c) (hadm : HsAdmissible χ C_N) :
    (hsComplexTestL2Operator χ hc).closure = hsComplexNeumannL2Operator χ hc ∧
      IsSelfAdjoint (hsComplexTestL2Operator χ hc).closure ∧
      (hsComplexNeumannL2Operator χ hc).HasCore
        (hsComplexTestL2Domain (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) ∧
      Dense (hsComplexSourceTestSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) := by
  obtain ⟨hcl, _, _, hform⟩ := scalar_boundary_core_L3219_quotient_real χ hc hadm
  have he : (hsComplexTestL2Operator χ hc).closure = hsComplexNeumannL2Operator χ hc := by
    change (complexifyL2Operator _ _).closure = complexifyL2Operator _ _
    rw [complexifyL2Operator_closure _ (hsTestL2Operator_isClosable χ hc), hcl]
  refine ⟨he, he ▸ complexifyL2Operator_selfAdjoint _ (hsNeumannL2Operator_selfAdjoint χ hc), ?_, ?_⟩
  · have hcore := (hsComplexTestL2Operator χ hc).closureHasCore
    rwa [he, hsComplexTestL2Operator_domain hadm.choose χ hc] at hcore
  · exact dense_complexFormTests hform

variable {n : ℕ}

/-- The complex anchored source domain, using the existing real source domain. -/
def anchoredComplexTestL2Domain (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    Submodule ℂ (Lp ℂ 2 (anchoredMeasureE χ)) :=
  complexifyL2Submodule _ (anchoredTestL2Domain χ hc)

/-- The complex anchored variational Neumann operator. -/
def anchoredComplexNeumannL2Operator (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    Lp ℂ 2 (anchoredMeasureE χ) →ₗ.[ℂ] Lp ℂ 2 (anchoredMeasureE χ) :=
  complexifyL2Operator _ (anchoredNeumannL2Operator χ hc)

/-- The complex anchored source differential operator. -/
def anchoredComplexTestL2Operator (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    Lp ℂ 2 (anchoredMeasureE χ) →ₗ.[ℂ] Lp ℂ 2 (anchoredMeasureE χ) :=
  complexifyL2Operator _ (anchoredTestL2Operator χ hc)

/-- The complex anchored H¹ form topology in the real Sobolev coordinates. -/
abbrev AnchoredComplexSobolev (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :=
  WithLp 2 (PoissonAnchoredSpace χ hc × PoissonAnchoredSpace χ hc)

/-- The anchored complex source forms. -/
def anchoredComplexSourceTestSobolev (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    Set (AnchoredComplexSobolev χ hc) := complexFormTests (anchoredSourceTestSobolev χ hc)

/-- The anchored complex form norm is exactly value norm squared plus gradient norm squared. -/
theorem anchoredComplexSobolev_norm_sq (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f : AnchoredComplexSobolev χ hc) :
    ‖f‖ ^ 2 =
      (‖poissonAnchoredValue χ hc f.ofLp.1‖ ^ 2 + ‖poissonAnchoredValue χ hc f.ofLp.2‖ ^ 2) +
      (‖poissonAnchoredGradient χ hc f.ofLp.1‖ ^ 2 + ‖poissonAnchoredGradient χ hc f.ofLp.2‖ ^ 2) := by
  have hn (v : PoissonAnchoredSpace χ hc) : ‖v‖ ^ 2 =
      ‖poissonAnchoredValue χ hc v‖ ^ 2 + ‖poissonAnchoredGradient χ hc v‖ ^ 2 :=
    WithLp.prod_norm_sq_eq_of_L2 v.val
  rw [WithLp.prod_norm_sq_eq_of_L2, hn, hn]
  dsimp only [WithLp.fst, WithLp.snd]
  ring

/-- The anchored complex Neumann graph is precisely the two real variational equations. -/
theorem mem_anchoredComplexNeumannL2Operator_graph (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f a : Lp ℂ 2 (anchoredMeasureE χ)) :
    (f, a) ∈ (anchoredComplexNeumannL2Operator χ hc).graph ↔
      (complexL2Re _ f, complexL2Re _ a) ∈ (anchoredNeumannL2Operator χ hc).graph ∧
        (complexL2Im _ f, complexL2Im _ a) ∈ (anchoredNeumannL2Operator χ hc).graph :=
  mem_complexifyL2Operator_graph _ _ f a

/-- The complex anchored source operator is the differential expression on both test components. -/
theorem anchoredComplexTestL2Operator_on_test (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f g : anchoredTestSubmodule n) :
    (complexL2OfPair _
      (poissonAnchoredValue χ hc (anchoredTestHilbert χ hc f),
       poissonAnchoredValue χ hc (anchoredTestHilbert χ hc g)),
      complexL2OfPair _
        ((memLp_anchoredLangevinExpr χ hc f.property.1 f.property.2.1 f.property.2.2).toLp
          (anchoredLangevinExpr χ f.val),
         (memLp_anchoredLangevinExpr χ hc g.property.1 g.property.2.1 g.property.2.2).toLp
          (anchoredLangevinExpr χ g.val))) ∈ (anchoredComplexTestL2Operator χ hc).graph :=
  complexifyL2Operator_on_pair _ _ (anchoredTestL2Operator_on_test χ hc f)
    (anchoredTestL2Operator_on_test χ hc g)

theorem anchoredComplexTestL2Operator_domain (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    (anchoredComplexTestL2Operator χ hc).domain = anchoredComplexTestL2Domain χ hc := by
  rw [anchoredComplexTestL2Operator, complexifyL2Operator_domain, anchoredTestL2Operator_domain]
  rfl

/-- The full complex anchored component of the scalar boundary core theorem. -/
theorem scalar_boundary_core_L3219_anchored_complex {C_N : ℝ}
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) (hadm : HsAdmissible χ C_N) :
    (anchoredComplexTestL2Operator χ hc).closure = anchoredComplexNeumannL2Operator χ hc ∧
      IsSelfAdjoint (anchoredComplexTestL2Operator χ hc).closure ∧
      (anchoredComplexNeumannL2Operator χ hc).HasCore (anchoredComplexTestL2Domain χ hc) ∧
      Dense (anchoredComplexSourceTestSobolev χ hc) := by
  obtain ⟨hcl, _, _, hform⟩ := scalar_boundary_core_L3219_anchored_real χ hc hadm
  have he : (anchoredComplexTestL2Operator χ hc).closure = anchoredComplexNeumannL2Operator χ hc := by
    change (complexifyL2Operator _ _).closure = complexifyL2Operator _ _
    rw [complexifyL2Operator_closure _ (anchoredTestL2Operator_isClosable χ hc), hcl]
  refine ⟨he, he ▸ complexifyL2Operator_selfAdjoint _ (anchoredNeumannL2Operator_selfAdjoint χ hc), ?_, ?_⟩
  · have hcore := (anchoredComplexTestL2Operator χ hc).closureHasCore
    rwa [he, anchoredComplexTestL2Operator_domain] at hcore
  · exact dense_complexFormTests hform

end Riesz1
