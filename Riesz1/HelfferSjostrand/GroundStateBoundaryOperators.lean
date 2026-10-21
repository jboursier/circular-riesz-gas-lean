/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BoundaryCoreComplex
public import Riesz1.ToMathlib.ConjugatePartialOperator

/-!
# The remaining ground-state source operators

The complex quotient operator and both anchored ground-state operators,
on their entire transported source domains.
The real quotient object remains the already defined `hsGroundStateOperator`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Laplacian

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

/-- The complex quotient source operator `U L₀ U⁻¹`. -/
def hsComplexGroundStateOperator (χ : HsPairPotentials N c) (hc : 0 < c) :
    Lp ℂ 2 (hsConfigurationVolume N) →ₗ.[ℂ] Lp ℂ 2 (hsConfigurationVolume N) :=
  conjugatePartialOperator (hsGroundStateUnitary χ hc).toLinearEquiv (hsComplexTestL2Operator χ hc)

theorem mem_hsComplexGroundStateOperator_graph (χ : HsPairPotentials N c) (hc : 0 < c)
    (f a : Lp ℂ 2 (hsConfigurationVolume N)) :
    (f, a) ∈ (hsComplexGroundStateOperator χ hc).graph ↔
      ((hsGroundStateUnitary χ hc).symm f, (hsGroundStateUnitary χ hc).symm a) ∈
        (hsComplexTestL2Operator χ hc).graph :=
  mem_conjugatePartialOperator_graph _ _ _ _

/-- The complex transformed source output is `-Δ + W` on both source components. -/
theorem hsComplexGroundStateOperator_schrodinger (hN : 2 ≤ (N : ℕ))
    (χ : HsPairPotentials N c) (hc : 0 < c) (f g : HsTestFunction N) :
    let μ := (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
    (hsGroundStateUnitary χ hc (complexL2OfPair μ
      ((memLp_hsLangevin hN χ f μ).toLp (hsLangevin χ f),
       (memLp_hsLangevin hN χ g μ).toLp (hsLangevin χ g))) : HsConfiguration N → ℂ)
      =ᵐ[hsConfigurationVolume N] fun x =>
        ((-Δ (hsGroundStateTest χ hN f).toFun (hsLiftPoint N x) +
          hsGroundStatePotential χ (hsLiftPoint N x) * hsGroundStateTest χ hN f (hsLiftPoint N x) : ℝ) : ℂ) +
        Complex.I * ((-Δ (hsGroundStateTest χ hN g).toFun (hsLiftPoint N x) +
          hsGroundStatePotential χ (hsLiftPoint N x) * hsGroundStateTest χ hN g (hsLiftPoint N x) : ℝ) : ℂ) := by
  let μ := (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
  let a := (memLp_hsLangevin hN χ f μ).toLp (hsLangevin χ f)
  let b := (memLp_hsLangevin hN χ g μ).toLp (hsLangevin χ g)
  have hac := Internal.squareDensity_ac (measurable_hsGroundStateMultiplier χ)
    (hsGroundStateMultiplier_pos χ hc) (hsQuotientGibbsProbability_eq_groundStateDensity χ hc)
  filter_upwards [hsGroundStateUnitary_coeFn χ hc (complexL2OfPair μ (a, b)),
    hac.ae_le (complexL2OfPair_ae μ a b), hac.ae_le (memLp_hsLangevin hN χ f μ).coeFn_toLp,
    hac.ae_le (memLp_hsLangevin hN χ g μ).coeFn_toLp] with x hU hab ha hb
  rw [hU, hab, ha, hb]
  have hf := hsGroundStateTest_schrodinger χ hN f (hsLiftPoint_mem_chamber N x)
  have hg := hsGroundStateTest_schrodinger χ hN g (hsLiftPoint_mem_chamber N x)
  change _ = hsGroundStateMultiplier χ x * hsLangevin χ f x at hf
  change _ = hsGroundStateMultiplier χ x * hsLangevin χ g x at hg
  rw [hf, hg]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring

variable {n : ℕ}

/-- The real anchored ground-state operator `U* L₀* (U*)⁻¹`. -/
def anchoredGroundStateOperator (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    Lp ℝ 2 (volume.restrict (anchoredSimplex n)) →ₗ.[ℝ]
      Lp ℝ 2 (volume.restrict (anchoredSimplex n)) :=
  conjugatePartialOperator (anchoredGroundStateEquiv χ hc).toLinearEquiv (anchoredTestL2Operator χ hc)

/-- The complex anchored ground-state source operator. -/
def anchoredComplexGroundStateOperator (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    Lp ℂ 2 (volume.restrict (anchoredSimplex n)) →ₗ.[ℂ]
      Lp ℂ 2 (volume.restrict (anchoredSimplex n)) :=
  conjugatePartialOperator (anchoredGroundStateUnitary χ hc).toLinearEquiv
    (anchoredComplexTestL2Operator χ hc)

theorem mem_anchoredGroundStateOperator_graph (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f a : Lp ℝ 2 (volume.restrict (anchoredSimplex n))) :
    (f, a) ∈ (anchoredGroundStateOperator χ hc).graph ↔
      ((anchoredGroundStateEquiv χ hc).symm f, (anchoredGroundStateEquiv χ hc).symm a) ∈
        (anchoredTestL2Operator χ hc).graph :=
  mem_conjugatePartialOperator_graph _ _ _ _

theorem mem_anchoredComplexGroundStateOperator_graph (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f a : Lp ℂ 2 (volume.restrict (anchoredSimplex n))) :
    (f, a) ∈ (anchoredComplexGroundStateOperator χ hc).graph ↔
      ((anchoredGroundStateUnitary χ hc).symm f, (anchoredGroundStateUnitary χ hc).symm a) ∈
        (anchoredComplexTestL2Operator χ hc).graph :=
  mem_conjugatePartialOperator_graph _ _ _ _

/-- On every anchored source test the transformed output is exactly `-Δ + W*`, in L². -/
theorem anchoredGroundStateOperator_schrodinger (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f : anchoredTestSubmodule n) :
    (anchoredGroundStateEquiv χ hc
      ((memLp_anchoredLangevinExpr χ hc f.property.1 f.property.2.1 f.property.2.2).toLp
        (anchoredLangevinExpr χ f.val)) : AnchoredEuclidean n → ℝ)
      =ᵐ[volume.restrict (anchoredSimplex n)] fun y =>
        -Δ (anchoredGroundStateTest χ f).val y +
          hsAnchoredGroundStatePotential χ y * (anchoredGroundStateTest χ f).val y := by
  have hac := Internal.aeSquareDensity_ac (aemeasurable_anchoredGroundStateMultiplier χ)
    (anchoredGroundStateMultiplier_pos χ hc) (anchoredMeasureE_eq_groundStateDensity χ hc)
  filter_upwards [ae_restrict_mem (measurableSet_anchoredSimplex n),
    anchoredGroundStateEquiv_coeFn χ hc
      ((memLp_anchoredLangevinExpr χ hc f.property.1 f.property.2.1 f.property.2.2).toLp
        (anchoredLangevinExpr χ f.val)),
    hac.ae_le (memLp_anchoredLangevinExpr χ hc f.property.1 f.property.2.1 f.property.2.2).coeFn_toLp]
      with y hy hU ha
  rw [hU, ha]
  exact (anchoredGroundStateTest_schrodinger χ f hy).symm

/-- The complex anchored transformed source output is exactly the anchored Schrödinger expression. -/
theorem anchoredComplexGroundStateOperator_schrodinger
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) (f g : anchoredTestSubmodule n) :
    (anchoredGroundStateUnitary χ hc (complexL2OfPair _
      ((memLp_anchoredLangevinExpr χ hc f.property.1 f.property.2.1 f.property.2.2).toLp
        (anchoredLangevinExpr χ f.val),
       (memLp_anchoredLangevinExpr χ hc g.property.1 g.property.2.1 g.property.2.2).toLp
        (anchoredLangevinExpr χ g.val))) : AnchoredEuclidean n → ℂ)
      =ᵐ[volume.restrict (anchoredSimplex n)] fun y =>
        ((-Δ (anchoredGroundStateTest χ f).val y + hsAnchoredGroundStatePotential χ y *
          (anchoredGroundStateTest χ f).val y : ℝ) : ℂ) + Complex.I *
        ((-Δ (anchoredGroundStateTest χ g).val y + hsAnchoredGroundStatePotential χ y *
          (anchoredGroundStateTest χ g).val y : ℝ) : ℂ) := by
  let μ := anchoredMeasureE χ
  let a := (memLp_anchoredLangevinExpr χ hc f.property.1 f.property.2.1 f.property.2.2).toLp
    (anchoredLangevinExpr χ f.val)
  let b := (memLp_anchoredLangevinExpr χ hc g.property.1 g.property.2.1 g.property.2.2).toLp
    (anchoredLangevinExpr χ g.val)
  have hac := Internal.aeSquareDensity_ac (aemeasurable_anchoredGroundStateMultiplier χ)
    (anchoredGroundStateMultiplier_pos χ hc) (anchoredMeasureE_eq_groundStateDensity χ hc)
  have hU := anchoredGroundStateUnitary_coeFn χ hc (complexL2OfPair μ (a, b))
  filter_upwards [ae_restrict_mem (measurableSet_anchoredSimplex n), hU,
    hac.ae_le (complexL2OfPair_ae μ a b),
    hac.ae_le (memLp_anchoredLangevinExpr χ hc f.property.1 f.property.2.1 f.property.2.2).coeFn_toLp,
    hac.ae_le (memLp_anchoredLangevinExpr χ hc g.property.1 g.property.2.1 g.property.2.2).coeFn_toLp]
      with y hy hUy hab ha hb
  rw [hUy, hab, ha, hb]
  rw [anchoredGroundStateTest_schrodinger χ f hy, anchoredGroundStateTest_schrodinger χ g hy]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring

end Riesz1
