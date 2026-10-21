/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.LogSobolevApproximation
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Limit tools for logarithmic Sobolev inequalities

The internal lemmas transfer an inequality from smooth to C¹ bounded tests, and transfer
the inequality along convergence against bounded continuous functions. Entropy uses
`Real.negMulLog`, including at zero.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Riesz1.LogSobolevInternal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A continuous real function is bounded on a bounded interval, also at zero. -/
lemma continuous_comp_bound {H : ℝ → ℝ} (hH : Continuous H) (C : ℝ) :
    ∃ K, ∀ r, |r| ≤ C → ‖H r‖ ≤ K := by
  obtain ⟨K, hK⟩ := ((isCompact_Icc : IsCompact (Icc (-C) C)).image hH).isBounded.exists_norm_le
  exact ⟨K, fun r hr => hK _ (mem_image_of_mem H (abs_le.mp hr))⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma integrable_continuous_bounded {μ : Measure E} [IsFiniteMeasure μ]
    {g : E → ℝ} (hg : Continuous g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall hC)

omit [FiniteDimensional ℝ E] in
/-- All three quantities in the smooth-test entropy inequality are actual integrals. -/
theorem test_integrable {μ : Measure E} [IsFiniteMeasure μ] {q : E → ℝ}
    (hq : ContDiff ℝ 1 q) {C D : ℝ} (hC : ∀ x, |q x| ≤ C)
    (hD : ∀ x, ‖fderiv ℝ q x‖ ≤ D) :
    Integrable (fun x => q x ^ 2) μ ∧
      Integrable (fun x => Real.negMulLog (q x ^ 2)) μ ∧
      Integrable (fun x => ‖fderiv ℝ q x‖ ^ 2) μ := by
  obtain ⟨K, hK⟩ := continuous_comp_bound (Real.continuous_negMulLog.comp (continuous_pow 2)) C
  have hqc : Continuous (fun x => q x ^ 2) := hq.continuous.pow 2
  have hdc : Continuous (fun x => ‖fderiv ℝ q x‖ ^ 2) :=
    (hq.continuous_fderiv one_ne_zero).norm.pow 2
  refine ⟨integrable_continuous_bounded hqc (C := C ^ 2) ?_,
    integrable_continuous_bounded (Real.continuous_negMulLog.comp hqc) (fun x => hK _ (hC x)),
    integrable_continuous_bounded hdc (C := D ^ 2) ?_⟩
  · intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (abs_le.mp (hC x)).1 (abs_le.mp (hC x)).2
  · intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hD x) 2

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Dominated convergence for a continuous function of uniformly bounded tests. -/
lemma tendsto_integral_comp {μ : Measure E} [IsFiniteMeasure μ]
    {qn : ℕ → E → ℝ} {q : E → ℝ} (hqn : ∀ n, Continuous (qn n)) {C : ℝ}
    (hC : ∀ n x, |qn n x| ≤ C) (hlim : ∀ x, Tendsto (fun n => qn n x) atTop (𝓝 (q x)))
    {H : ℝ → ℝ} (hH : Continuous H) :
    Tendsto (fun n => ∫ x, H (qn n x) ∂μ) atTop (𝓝 (∫ x, H (q x) ∂μ)) := by
  obtain ⟨K, hK⟩ := continuous_comp_bound hH C
  exact tendsto_integral_of_dominated_convergence (fun _ => K)
    (fun n => (hH.comp (hqn n)).aestronglyMeasurable) (integrable_const K)
    (fun n => Eventually.of_forall fun x => hK _ (hC n x))
    (Eventually.of_forall fun x => (hH.tendsto _).comp (hlim x))

/-- Internal implication: an LSI on bounded smooth tests extends to bounded C¹ tests with
bounded derivative. Its premise must be proved when using it in a main result. -/
theorem lsi_of_smooth_tests {μ : Measure E} [IsFiniteMeasure μ] (w : ℝ)
    (hLSI : ∀ q : E → ℝ, ContDiff ℝ ∞ q → (∃ C, ∀ x, |q x| ≤ C) →
      (∃ D, ∀ x, ‖fderiv ℝ q x‖ ≤ D) →
      -(∫ x, Real.negMulLog (q x ^ 2) ∂μ) + Real.negMulLog (∫ x, q x ^ 2 ∂μ) ≤
        2 * w * ∫ x, ‖fderiv ℝ q x‖ ^ 2 ∂μ)
    {q : E → ℝ} (hq : ContDiff ℝ 1 q) {C D : ℝ} (hC : ∀ x, |q x| ≤ C)
    (hD : ∀ x, ‖fderiv ℝ q x‖ ≤ D) :
    -(∫ x, Real.negMulLog (q x ^ 2) ∂μ) + Real.negMulLog (∫ x, q x ^ 2 ∂μ) ≤
      2 * w * ∫ x, ‖fderiv ℝ q x‖ ^ 2 ∂μ := by
  obtain ⟨qn, hqn, hCn, hDn, htq, htd⟩ := exists_smooth_tests hq hC hD
  have ht₁ := tendsto_integral_comp (μ := μ) (fun n => (hqn n).continuous) hCn htq
    (continuous_pow 2)
  have ht₂ := tendsto_integral_comp (μ := μ) (fun n => (hqn n).continuous) hCn htq
    (Real.continuous_negMulLog.comp (continuous_pow 2))
  have ht₃ : Tendsto (fun n => ∫ x, ‖fderiv ℝ (qn n) x‖ ^ 2 ∂μ) atTop
      (𝓝 (∫ x, ‖fderiv ℝ q x‖ ^ 2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => D ^ 2)
    · exact fun n => (((hqn n).of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)).continuous_fderiv
        one_ne_zero).norm.pow 2 |>.aestronglyMeasurable
    · exact integrable_const _
    · intro n
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hDn n x) 2
    · exact Eventually.of_forall fun x => (htd x).norm.pow 2
  exact le_of_tendsto_of_tendsto
    (ht₂.neg.add (Real.continuous_negMulLog.tendsto _ |>.comp ht₁))
    (tendsto_const_nhds.mul ht₃)
    (Eventually.of_forall fun n => hLSI (qn n) (hqn n) ⟨C, hCn n⟩ ⟨D, hDn n⟩)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Internal stability under convergence against every bounded continuous function. The test
is C¹, so its derivative energy is also bounded and continuous. -/
theorem lsi_of_tendsto_integrals {μ : Measure E} {μn : ℕ → Measure E} {w : ℝ}
    (hlim : ∀ g : E → ℝ, Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun n => ∫ x, g x ∂μn n) atTop (𝓝 (∫ x, g x ∂μ)))
    {q : E → ℝ} (hq : ContDiff ℝ 1 q) {C D : ℝ} (hC : ∀ x, |q x| ≤ C)
    (hD : ∀ x, ‖fderiv ℝ q x‖ ≤ D)
    (hLSI : ∀ n, -(∫ x, Real.negMulLog (q x ^ 2) ∂μn n) +
      Real.negMulLog (∫ x, q x ^ 2 ∂μn n) ≤ 2 * w * ∫ x, ‖fderiv ℝ q x‖ ^ 2 ∂μn n) :
    -(∫ x, Real.negMulLog (q x ^ 2) ∂μ) + Real.negMulLog (∫ x, q x ^ 2 ∂μ) ≤
      2 * w * ∫ x, ‖fderiv ℝ q x‖ ^ 2 ∂μ := by
  have hqc : Continuous (fun x => q x ^ 2) := hq.continuous.pow 2
  have hdc : Continuous (fun x => ‖fderiv ℝ q x‖ ^ 2) :=
    (hq.continuous_fderiv one_ne_zero).norm.pow 2
  obtain ⟨K, hK⟩ := continuous_comp_bound (Real.continuous_negMulLog.comp (continuous_pow 2)) C
  have ht₁ := hlim (fun x => q x ^ 2) hqc ⟨C ^ 2, fun x => by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (abs_le.mp (hC x)).1 (abs_le.mp (hC x)).2⟩
  have ht₂ := hlim (fun x => Real.negMulLog (q x ^ 2))
    (Real.continuous_negMulLog.comp hqc) ⟨K, fun x => hK _ (hC x)⟩
  have ht₃ := hlim (fun x => ‖fderiv ℝ q x‖ ^ 2) hdc ⟨D ^ 2, fun x => by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hD x) 2⟩
  exact le_of_tendsto_of_tendsto
    (ht₂.neg.add (Real.continuous_negMulLog.tendsto _ |>.comp ht₁))
    (tendsto_const_nhds.mul ht₃) (Eventually.of_forall hLSI)

end Riesz1.LogSobolevInternal

end
