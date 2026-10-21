/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.QuotientChartL2
public import Riesz1.ToMathlib.ExponentialDensityLp

/-!
# Lebesgue L² transport from the Gibbs quotient

The exponential density is removed before lifting, and its reciprocal
square root is restored locally. This avoids any continuity assumption on
completed Sobolev representatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace Riesz1

theorem hsHamiltonian_chamberProjection {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) (x : hsChamber N) :
    hsHamiltonian χ (hsChamberProjection x) = hsPairExpression χ x.val := by
  rw [← hsChamberProjection_representative x, hsHamiltonian_configurationMap]
  change hsPairExpression χ (WithLp.toLp 2 (hsRepresentative x).val) = _
  have he : WithLp.toLp 2 (hsRepresentative x).val =
      hsTranslate (-(⌊x.val ⟨0, N.pos⟩⌋ : ℤ) : ℝ) x.val := by
    ext i
    simp only [hsRepresentative_apply, hsTranslate_apply, sub_eq_add_neg]
  rw [he, hsPairExpression_translate]

/-- Arbitrary Gibbs L² data lift to local Lebesgue L² on the chamber,
including neighborhoods crossing the rotation seam. -/
theorem locallySquareIntegrableOn_gibbs_quotient_mk {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : HsCylinder N → F}
    (hf : MemLp (fun x : HsConfiguration N => f x.val) 2
      (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    LocallySquareIntegrableOn (hsChamber N)
      (fun x : HsEuclidean N => f (QuotientAddGroup.mk x)) := by
  have hZ0 := (hsPartitionFunction_pos χ).ne'
  have hZt := (hsPartitionFunction_lt_top χ hc).ne
  have hw : MemLp (fun x : HsConfiguration N => f x.val) 2 (hsGibbsWeight χ) := by
    have hh := hf.smul_measure hZt
    change MemLp _ 2 (hsPartitionFunction χ • ((hsPartitionFunction χ)⁻¹ • hsGibbsWeight χ)) at hh
    rwa [smul_smul, ENNReal.mul_inv_cancel hZ0 hZt, one_smul] at hh
  have hL := memLp_two_exp_neg_half (measurable_hsHamiltonian χ) hw
  let g : HsCylinder N → F := Function.extend Subtype.val
    (fun x : HsConfiguration N => Real.exp (-hsHamiltonian χ x / 2) • f x.val) (fun _ => 0)
  have hg (x : HsConfiguration N) :
      g x.val = Real.exp (-hsHamiltonian χ x / 2) • f x.val :=
    Subtype.val_injective.extend_apply _ _ x
  have hgL : MemLp (fun x : HsConfiguration N => g x.val) 2 (hsConfigurationVolume N) := by
    simpa only [hg] using hL
  have hlocal := (locallySquareIntegrableOn_quotient_mk hgL).smul_continuousOn
    (Real.continuous_exp.comp_continuousOn
      ((hsPairExpression_contDiffOn χ).continuousOn.div_const 2))
  intro K hK hKU
  apply (hlocal K hK hKU).ae_eq
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  have he := hg (hsChamberProjection ⟨x, hKU hx⟩)
  change g (QuotientAddGroup.mk x) = _ at he
  rw [hsHamiltonian_chamberProjection] at he
  rw [he, smul_smul]
  change (Real.exp (hsPairExpression χ x / 2) * Real.exp (-hsPairExpression χ x / 2)) •
    f (QuotientAddGroup.mk x) = f (QuotientAddGroup.mk x)
  rw [← Real.exp_add]
  have hz : hsPairExpression χ x / 2 + -hsPairExpression χ x / 2 = 0 := by ring
  rw [hz, Real.exp_zero, one_smul]

/-- Local L² of the actual pullback of a Gibbs representative, on every
compact subset of any injective chart (in fact injectivity is unnecessary). -/
theorem memLp_hsChamberProjection_gibbs_compact {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : HsConfiguration N → F}
    (hf : MemLp f 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    {K : Set (HsEuclidean N)} (hK : IsCompact K) (hKU : K ⊆ hsChamber N) :
    MemLp (fun x : K => f (hsChamberProjection ⟨x.val, hKU x.property⟩)) 2
      (Measure.comap (Subtype.val : K → HsEuclidean N) volume) := by
  let g : HsCylinder N → F := Function.extend Subtype.val f (fun _ => 0)
  have hg : ∀ x : HsConfiguration N, g x.val = f x :=
    Subtype.val_injective.extend_apply f (fun _ => 0)
  have hgL : MemLp (fun x : HsConfiguration N => g x.val) 2
      (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
    simpa only [hg] using hf
  have hL := locallySquareIntegrableOn_gibbs_quotient_mk χ hc hgL K hK hKU
  rw [← map_comap_subtype_coe hK.measurableSet volume,
    (MeasurableEmbedding.subtype_coe hK.measurableSet).memLp_map_measure_iff] at hL
  convert hL using 1
  funext x
  exact (hg (hsChamberProjection ⟨x.val, hKU x.property⟩)).symm

end Riesz1
