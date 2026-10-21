/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.LipschitzH1
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Cutoff products in the weighted Sobolev completion

The coefficient only needs to be `C¹` near the part of the closed domain
meeting the cutoff's topological support. Outside that support the product
is locally zero. These are the cutoff membership steps used with
the weighted Sobolev completion in Lemma 5.2 and Proposition 5.9.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff NNReal

namespace Riesz1.WeightedSobolev

/-- Local Lipschitz regularity of a real product, by composition with the smooth
multiplication map. No global boundedness assumptions are needed. -/
theorem locallyLipschitzOn_mul_real {X : Type*} [PseudoEMetricSpace X]
    {A : Set X} {η F : X → ℝ}
    (hη : LocallyLipschitzOn A η) (hF : LocallyLipschitzOn A F) :
    LocallyLipschitzOn A (fun x => η x * F x) := by
  have hm : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 * p.2) :=
    contDiff_fst.mul contDiff_snd
  exact locallyLipschitzOn_iff_restrict.mpr
    (hm.locallyLipschitz.comp (hη.restrict.prodMk hF.restrict))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasure μ] {U W O : Set E} {η F : E → ℝ} {C : ℝ≥0}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A cutoff product is locally Lipschitz where either its coefficient is `C¹`
or its cutoff is locally zero. -/
theorem locallyLipschitzOn_cutoff_mul (hW : IsOpen W) (hη : LipschitzOnWith C η W)
    (hO : IsOpen O) (hF : ContDiffOn ℝ 1 F O) :
    LocallyLipschitzOn (W ∩ (O ∪ (tsupport η)ᶜ)) (fun x => η x * F x) := by
  have hηl : LocallyLipschitzOn (W ∩ O) η := by
    intro x hx
    exact ⟨C, W, mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hx.1), hη⟩
  have hFl : LocallyLipschitzOn (W ∩ O) F := by
    intro x hx
    obtain ⟨K, t, ht, hFt⟩ := (hF.contDiffAt (hO.mem_nhds hx.2)).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hFt⟩
  have hp := locallyLipschitzOn_mul_real hηl hFl
  intro x hx
  rcases hx.2 with hxO | hxS
  · obtain ⟨K, t, ht, hpt⟩ := hp ⟨hx.1, hxO⟩
    rw [nhdsWithin_eq_nhds.mpr ((hW.inter hO).mem_nhds ⟨hx.1, hxO⟩)] at ht
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hpt⟩
  · refine ⟨0, (tsupport η)ᶜ,
      mem_nhdsWithin_of_mem_nhds (isClosed_tsupport η |>.isOpen_compl.mem_nhds hxS), ?_⟩
    intro y hy z hz
    simp only [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hz,
      zero_mul, edist_self, ENNReal.coe_zero, zero_mul, le_refl]

omit [IsFiniteMeasure μ] in
/-- The cutoff product rule for the classical gradient almost everywhere.
The uncut coefficient is unrestricted away from the cutoff's support. -/
theorem gradient_cutoff_mul_ae (hμ : ∀ᵐ x ∂μ, x ∈ U) (hac : μ ≪ volume)
    (hW : IsOpen W) (hUW : closure U ⊆ W) (hη : LipschitzOnWith C η W)
    (hO : IsOpen O) (hSO : tsupport η ∩ closure U ⊆ O) (hF : ContDiffOn ℝ 1 F O) :
    gradient (fun x => η x * F x) =ᵐ[μ]
      (fun x => η x • gradient F x + F x • gradient η x) := by
  have ha := hac.ae_le (hη.ae_differentiableWithinAt_of_mem (μ := (volume : Measure E)))
  filter_upwards [hμ, ha] with x hx hηx
  by_cases hxS : x ∈ tsupport η
  · have hdx : DifferentiableAt ℝ η x :=
      (hηx (hUW (subset_closure hx))).differentiableAt
        (hW.mem_nhds (hUW (subset_closure hx)))
    have hdF : DifferentiableAt ℝ F x :=
      (hF.contDiffAt (hO.mem_nhds (hSO ⟨hxS, subset_closure hx⟩))).differentiableAt
        (by norm_num)
    have hd := (hdx.hasFDerivAt.mul hdF.hasFDerivAt).fderiv
    change fderiv ℝ (fun y => η y * F y) x = _ at hd
    simp only [gradient, hd, map_add, map_smul]
  · have hη0 : η =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hxS] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hp0 : (fun y => η y * F y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hη0] with y hy
      simp only [hy, zero_mul]
    rw [hp0.gradient_eq, hη0.gradient_eq]
    simp only [gradient_fun_const, image_eq_zero_of_notMem_tsupport hxS,
      zero_smul, smul_zero, add_zero]

/-- A Lipschitz cutoff times a locally `C¹` coefficient belongs to the weighted
completion with the product gradient. Boundedness of the cutoff is unnecessary:
local regularity and the bounded domain already give all required integrability. -/
theorem isWeightedH1_cutoff_mul (hU : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) (hac : μ ≪ volume)
    (hW : IsOpen W) (hUW : closure U ⊆ W) (hη : LipschitzOnWith C η W)
    (hO : IsOpen O) (hSO : tsupport η ∩ closure U ⊆ O) (hF : ContDiffOn ℝ 1 F O) :
    IsWeightedH1 μ U (fun x => η x * F x)
      (fun x => η x • gradient F x + F x • gradient η x) := by
  have hV : IsOpen (W ∩ (O ∪ (tsupport η)ᶜ)) :=
    hW.inter (hO.union (isClosed_tsupport η).isOpen_compl)
  have hUV : closure U ⊆ W ∩ (O ∪ (tsupport η)ᶜ) := by
    intro x hx
    refine ⟨hUW hx, ?_⟩
    by_cases hxS : x ∈ tsupport η
    · exact Or.inl (hSO ⟨hxS, hx⟩)
    · exact Or.inr hxS
  have hm := isWeightedH1_of_locallyLipschitzOn hU hμ hac hV hUV
    (locallyLipschitzOn_cutoff_mul hW hη hO hF)
  exact hm.congr Filter.EventuallyEq.rfl (gradient_cutoff_mul_ae hμ hac hW hUW hη hO hSO hF)

end Riesz1.WeightedSobolev

end
