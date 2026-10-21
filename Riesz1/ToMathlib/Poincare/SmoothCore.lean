/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.Completion
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Smooth functions in a weighted Sobolev completion

Finite measures supported on a bounded domain integrate every function
continuous on its closure. Smooth functions near that closure therefore
belong to the weighted Sobolev completion with their actual gradient.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Riesz1.Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {μ : Measure E} [IsFiniteMeasure μ] {U : Set E}

theorem memLp_of_continuousOn_closure {V : Type*} [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (hU : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U) {f : E → V}
    (hf : ContinuousOn f (closure U)) : MemLp f 2 μ := by
  classical
  obtain ⟨C, hC⟩ := hU.isCompact_closure.exists_bound_of_continuousOn hf
  have hm : AEStronglyMeasurable f μ := by
    have hmask : Measurable ((closure U).indicator f) :=
      (hf.measurable_piecewise continuousOn_const isClosed_closure.measurableSet)
    apply hmask.aestronglyMeasurable.congr
    filter_upwards [hμ] with x hx
    exact indicator_of_mem (subset_closure hx) f
  exact MemLp.of_bound hm C (hμ.mono fun x hx => hC x (subset_closure hx))

theorem isWeightedH1_of_smoothNearClosure
    (hU : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U) {f : E → ℝ}
    (hf : WeightedSobolev.SmoothNearClosure U f) :
    WeightedSobolev.IsWeightedH1 μ U f (gradient f) := by
  obtain ⟨W, hW, hUW, hfs⟩ := hf
  have hv := memLp_of_continuousOn_closure hU hμ (hfs.continuousOn.mono hUW)
  have hg : ContinuousOn (gradient f) (closure U) :=
    ((InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn
      (hfs.continuousOn_fderiv_of_isOpen hW (by norm_num))).mono hUW
  refine ⟨hv, memLp_of_continuousOn_closure hU hμ hg,
    fun _ => f, fun _ => ⟨W, hW, hUW, hfs⟩, ?_, ?_⟩ <;>
    simp

end Riesz1.Poincare

end
