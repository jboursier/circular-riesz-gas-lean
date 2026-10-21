/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Local integration by parts with an interior cutoff

The weight and the function need only be smooth on an open set. Their
ambient values away from that set need not even be measurable. Multiplication
by an interior compact smooth test gives a smooth zero extension.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Function Filter Topology
open scoped ContDiff

namespace Riesz1.WeightedSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {U : Set E} {f ψ : E → ℝ}

omit [NormedSpace ℝ E] in
/-- A continuous cutoff makes a locally continuous product globally continuous. -/
theorem continuous_cutoff_mul (hU : IsOpen U) (hψ : Continuous ψ)
    (hψU : tsupport ψ ⊆ U) (hf : ContinuousOn f U) :
    Continuous (fun x => ψ x * f x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · exact hψ.continuousAt.mul (hf.continuousAt (hU.mem_nhds hx))
  · have hxs : x ∉ tsupport ψ := fun h => hx (hψU h)
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxs] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- A smooth interior cutoff makes a locally smooth product globally smooth. -/
theorem contDiff_cutoff_mul (hU : IsOpen U) (hψ : ContDiff ℝ ∞ ψ)
    (hψU : tsupport ψ ⊆ U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (fun x => ψ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hψ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
  · have hxs : x ∉ tsupport ψ := fun h => hx (hψU h)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxs] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ]

/-- Local weighted integration by parts. This is an identity over the
whole ambient space, using the compact test as the zero extension. -/
theorem integral_weighted_fderiv_of_compact_test (hU : IsOpen U)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) {w : E → ℝ} (hw : ContDiffOn ℝ ∞ w U) (v : E) :
    ∫ x, (ψ x * w x) * fderiv ℝ f x v ∂μ =
      - ∫ x, f x * fderiv ℝ (fun y => ψ y * w y) x v ∂μ := by
  let g := fun x => ψ x * w x
  have hg : ContDiff ℝ ∞ g := contDiff_cutoff_mul hU hψ hψU hw
  have hgc : HasCompactSupport g := hψc.mul_right
  have hgU : tsupport g ⊆ U := tsupport_mul_subset_left.trans hψU
  have hgdU : tsupport (fun x => fderiv ℝ g x v) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ v).trans hgU
  have hdf : ContinuousOn (fun x => fderiv ℝ f x v) U :=
    (hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply continuousOn_const
  have hi₁ : Integrable (fun x => fderiv ℝ f x v * g x) μ := by
    have hi := (continuous_cutoff_mul hU hg.continuous hgU hdf).integrable_of_hasCompactSupport (μ := μ)
      hgc.mul_right
    simpa only [mul_comm] using hi
  have hi₂ : Integrable (fun x => f x * fderiv ℝ g x v) μ := by
    have hi := (continuous_cutoff_mul hU
      ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const) hgdU hf.continuousOn
      ).integrable_of_hasCompactSupport (μ := μ) (hgc.fderiv_apply ℝ v).mul_right
    simpa only [mul_comm] using hi
  have hi₀ : Integrable (fun x => f x * g x) μ := by
    have hi := (continuous_cutoff_mul hU hg.continuous hgU hf.continuousOn
      ).integrable_of_hasCompactSupport (μ := μ) hgc.mul_right
    simpa only [mul_comm] using hi
  have heq := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₀
    (fun x hx => (hf.contDiffAt (hU.mem_nhds (hgU hx))).differentiableAt (by norm_num))
    (fun x _ => hg.differentiable (by norm_num) x)
  simpa only [g, mul_comm, neg_neg] using (congrArg Neg.neg heq).symm

end Riesz1.WeightedSobolev

end
