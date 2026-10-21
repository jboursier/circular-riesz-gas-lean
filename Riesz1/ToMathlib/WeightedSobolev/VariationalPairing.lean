/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.Graph
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Pairing identities on weighted Sobolev completions

Smooth functions near the closure of a bounded finite dimensional domain
have finite weighted norm for every finite measure carried by the domain.
A continuous linear identity on their jets therefore passes to the completion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Riesz1.WeightedSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasure μ] {U : Set E}

/-- Continuous functions on a compact closure have finite norm for a measure carried by `U`. -/
theorem memLp_of_continuousOn_closure {V : Type*} [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (hU : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {f : E → V} (hf : ContinuousOn f (closure U)) : MemLp f 2 μ := by
  obtain ⟨C, hC⟩ := hU.isCompact_closure.exists_bound_of_continuousOn hf
  have hm : AEStronglyMeasurable f μ := by
    have hm := (hf.aemeasurable isClosed_closure.measurableSet (μ := μ)).aestronglyMeasurable
    rwa [Measure.restrict_eq_self_of_ae_mem (hμ.mono fun x hx => subset_closure hx)] at hm
  exact MemLp.of_bound hm C (hμ.mono fun x hx => hC x (subset_closure hx))

/-- Both components of every smooth core jet have finite norm. -/
theorem memLp_of_smoothNearClosure (hU : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) {f : E → ℝ} (hf : SmoothNearClosure U f) :
    MemLp f 2 μ ∧ MemLp (gradient f) 2 μ := by
  obtain ⟨W, hW, hUW, hfW⟩ := hf
  refine ⟨memLp_of_continuousOn_closure hU hμ (hfW.continuousOn.mono hUW), ?_⟩
  apply memLp_of_continuousOn_closure hU hμ
  exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn
    ((hfW.continuousOn_fderiv_of_isOpen hW (by norm_num)).mono hUW)

omit [BorelSpace E] [IsFiniteMeasure μ] in
/-- Weighted Sobolev membership depends only on the two almost everywhere classes. -/
theorem IsWeightedH1.congr {F F' : E → ℝ} {G G' : E → E}
    (h : IsWeightedH1 μ U F G) (hF : F =ᵐ[μ] F') (hG : G =ᵐ[μ] G') :
    IsWeightedH1 μ U F' G' := by
  change IsGraphH1 μ (SmoothNearClosure U) id gradient F G at h
  change IsGraphH1 μ (SmoothNearClosure U) id gradient F' G'
  exact h.congr hF hG

namespace Internal

/-- A smooth-core pairing identity extends to every completed Sobolev pair. -/
theorem pairing_of_smooth (hU : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {t : E → E} (ht : MemLp t 2 μ) {q : E → ℝ} (hq : MemLp q 2 μ)
    (hcore : ∀ φ, SmoothNearClosure U φ →
      (∫ x, inner ℝ (gradient φ x) (t x) ∂μ) = ∫ x, φ x * q x ∂μ)
    {F : E → ℝ} {G : E → E} (hFG : IsWeightedH1 μ U F G) :
    (∫ x, inner ℝ (G x) (t x) ∂μ) = ∫ x, F x * q x ∂μ := by
  obtain ⟨hF, hG, φ, hφ, hv, hg⟩ := hFG
  have hm k := memLp_of_smoothNearClosure hU hμ (hφ k)
  have hv' := (tendsto_toLp_iff_lintegral_sq φ (fun k => (hm k).1) F hF).mpr hv
  have hg' := (tendsto_toLp_iff_lintegral_sq (fun k => gradient (φ k))
    (fun k => (hm k).2) G hG).mpr hg
  have heq k : inner ℝ ((hm k).2.toLp (gradient (φ k))) (ht.toLp t) =
      inner ℝ ((hm k).1.toLp (φ k)) (hq.toLp q) := by
    rw [L2.inner_def, L2.inner_def]
    calc
      _ = ∫ x, inner ℝ (gradient (φ k) x) (t x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [(hm k).2.coeFn_toLp, ht.coeFn_toLp] with x hx ht
        rw [hx, ht]
      _ = _ := hcore (φ k) (hφ k)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [(hm k).1.coeFn_toLp, hq.coeFn_toLp] with x hx hq
        rw [hx, hq, Real.inner_apply]
  have he := tendsto_nhds_unique (hg'.inner tendsto_const_nhds)
    ((hv'.inner tendsto_const_nhds).congr fun k => (heq k).symm)
  rw [L2.inner_def, L2.inner_def] at he
  calc
    _ = ∫ x, inner ℝ (hG.toLp G x) (ht.toLp t x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hG.coeFn_toLp, ht.coeFn_toLp] with x hx ht
      rw [hx, ht]
    _ = _ := he
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp, hq.coeFn_toLp] with x hx hq
      rw [hx, hq, Real.inner_apply]

end Internal

end Riesz1.WeightedSobolev

end
