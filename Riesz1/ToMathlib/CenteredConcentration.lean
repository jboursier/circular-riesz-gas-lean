/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Centering a logarithmic moment bound and its two-sided tail

These measure-theoretic implications apply to every probability space.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Riesz1.Internal

/-- An uncentered logarithmic moment bound gives a centered sub-Gaussian MGF,
including exponential integrability. -/
theorem centered_subgaussian_of_log_mgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {A : Ω → ℝ} {K : ℝ≥0}
    (hI : ∀ t : ℝ, Integrable (fun x => Real.exp (t * A x)) μ)
    (hlog : ∀ t : ℝ, Real.log (∫ x, Real.exp (t * A x) ∂μ) ≤
      t * (∫ x, A x ∂μ) + (K : ℝ) * t ^ 2 / 2) :
    HasSubgaussianMGF (fun x => A x - ∫ y, A y ∂μ) K μ := by
  have he (t : ℝ) (x : Ω) : Real.exp (t * (A x - ∫ y, A y ∂μ)) =
      Real.exp (-(t * ∫ y, A y ∂μ)) * Real.exp (t * A x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨fun t => ?_, fun t => ?_⟩
  · simp_rw [he]
    exact (hI t).const_mul _
  · change (∫ x, Real.exp (t * (A x - ∫ y, A y ∂μ)) ∂μ) ≤ _
    simp_rw [he]
    rw [integral_const_mul]
    have hp : 0 < ∫ x, Real.exp (t * A x) ∂μ := integral_exp_pos (hI t)
    have hb := (Real.log_le_iff_le_exp hp).mp (hlog t)
    calc Real.exp (-(t * ∫ y, A y ∂μ)) * (∫ x, Real.exp (t * A x) ∂μ)
        ≤ Real.exp (-(t * ∫ y, A y ∂μ)) *
          Real.exp (t * (∫ y, A y ∂μ) + (K : ℝ) * t ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Two Chernoff tails, with the optimized coefficient, on an arbitrary probability space. -/
theorem subgaussian_two_sided {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ≥0}
    (h : HasSubgaussianMGF X K μ) {v : ℝ} (hv : 0 ≤ v) :
    μ.real {x | v ≤ |X x|} ≤ 2 * Real.exp (-v ^ 2 / (2 * (K : ℝ))) := by
  have he : {x | v ≤ |X x|} = {x | v ≤ X x} ∪ {x | v ≤ -X x} := by
    ext x
    simp only [mem_ofPred_eq, mem_union]
    rcases le_total 0 (X x) with hx | hx
    · rw [abs_of_nonneg hx]
      constructor
      · exact Or.inl
      · intro hh
        rcases hh with hh | hh
        · exact hh
        · linarith
    · rw [abs_of_nonpos hx]
      constructor
      · exact Or.inr
      · intro hh
        rcases hh with hh | hh
        · linarith
        · exact hh
  rw [he]
  have hn : μ.real {x | v ≤ -X x} ≤ Real.exp (-v ^ 2 / (2 * (K : ℝ))) :=
    h.neg.measure_ge_le hv
  exact (measureReal_union_le _ _).trans (by linarith [h.measure_ge_le hv])

/-- A zero sub-Gaussian coefficient gives zero mass to every positive absolute tail. -/
theorem subgaussian_zero_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (h : HasSubgaussianMGF X 0 μ) {v : ℝ} (hv : 0 < v) :
    μ {x | v ≤ |X x|} = 0 := by
  apply measure_mono_null (t := {x | X x ≠ 0})
  · intro x hx he
    simp only [mem_ofPred_eq] at hx he ⊢
    rw [he, abs_zero] at hx
    exact (not_le_of_gt hv) hx
  · exact (ae_iff.mp h.ae_eq_zero_of_hasSubgaussianMGF_zero)

end Riesz1.Internal

end
