/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.TotalVariation.VarianceTransfer
public import Riesz1.ToMathlib.Moments.Decay

/-!
# Variance transfer on a common full-measure domain

A continuous observable on a measurable domain has the usual bounded
variance transfer estimate if both probability measures live on that domain.
The value of the ambient total formula outside the domain is irrelevant.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Riesz1

/-- Bounded variance transfer for an observable continuous on a common
full-measure domain. -/
theorem abs_variance_sub_le_on {Ω : Type*} [TopologicalSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {S : Set Ω}
    (hS : MeasurableSet S) (hμS : ∀ᵐ x ∂μ, x ∈ S) (hνS : ∀ᵐ x ∂ν, x ∈ S)
    {f : Ω → ℝ} (hf : ContinuousOn f S) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x ∈ S, |f x| ≤ B) :
    |variance f μ - variance f ν| ≤ 6 * B ^ 2 * totalVariation μ ν := by
  classical
  let g := S.piecewise f (fun _ => 0)
  have hg : Measurable g := hf.measurable_piecewise continuousOn_const hS
  have hμ : f =ᵐ[μ] g := hμS.mono fun x hx => (piecewise_eq_of_mem S f _ hx).symm
  have hν : f =ᵐ[ν] g := hνS.mono fun x hx => (piecewise_eq_of_mem S f _ hx).symm
  rw [variance_congr hμ, variance_congr hν]
  apply abs_variance_sub_le_of_abs_le μ ν hg hB
  intro x
  by_cases hx : x ∈ S
  · simpa only [g, piecewise_eq_of_mem S f _ hx] using hb x hx
  · simpa only [g, piecewise_eq_of_notMem S f _ hx, abs_zero] using hB

/-- Absorb any real power into half of a stretched exponential. -/
theorem rpow_mul_exp_neg_le_half {a c D : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K →
      K ^ D * Real.exp (-c * K ^ a) ≤ C * Real.exp (-(c / 2) * K ^ a) := by
  obtain ⟨C, hC, hb⟩ := rpow_mul_exp_neg_bounded (β := D) ha (show 0 < c / 2 by linarith)
  refine ⟨C + 1, by linarith, fun K hK => ?_⟩
  have he : Real.exp (-c * K ^ a) =
      Real.exp (-(c / 2) * K ^ a) * Real.exp (-(c / 2) * K ^ a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right (hb K hK) (Real.exp_nonneg _)).trans
    (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _))

end Riesz1

end
