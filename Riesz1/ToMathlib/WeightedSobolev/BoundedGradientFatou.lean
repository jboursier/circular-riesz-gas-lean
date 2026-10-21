/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Lower semicontinuity of the entropy functional along almost everywhere limits

For a probability measure `μ`, nonnegative functions `h n` and `h₀` with `h n → h₀` almost
everywhere, and integrable entropies `∫ h n log h n`, Fatou's lemma gives
`∫ h₀ log h₀ ≤ T` whenever the entropies are eventually bounded by a sequence `B n` converging to
`T`. The integrand `r ↦ r log r` is bounded below by `r - 1 ≥ -1` on nonnegative reals, so Fatou's
lemma applies to its translate `r log r + 1 ≥ 0`.

This is the only passage to the limit in the entropy inequality of
`Riesz1.LogSobolevEntropy.logSobolev_conditioning_H1`, which runs along a subsequence converging almost everywhere.
-/

public section

noncomputable section

open MeasureTheory Filter Topology

namespace Riesz1.WeightedSobolev

/-- The entropy integrand `r log r` is at least `r - 1 ≥ -1` on nonnegative reals. -/
theorem mul_log_add_one_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ r * Real.log r + 1 := by
  rcases hr.eq_or_lt with rfl | hpos
  · simp
  · have hlog := Real.one_sub_inv_le_log_of_pos hpos
    have hmul : r * (1 - r⁻¹) ≤ r * Real.log r := mul_le_mul_of_nonneg_left hlog hpos.le
    rw [mul_sub, mul_inv_cancel₀ hpos.ne', mul_one] at hmul
    linarith

/-- Fatou's lemma for the entropy functional along an almost everywhere convergent sequence.
If the entropies `∫ h n log h n` lie below a sequence `B n` converging to `T`, then the entropy of
the limit is integrable and at most `T`. -/
theorem integrable_mul_log_and_le_of_tendsto_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {h : ℕ → α → ℝ} {h₀ : α → ℝ}
    (hmeas : ∀ n, Measurable (h n)) (hmeas₀ : AEMeasurable h₀ μ)
    (hnn : ∀ n x, 0 ≤ h n x) (hnn₀ : ∀ x, 0 ≤ h₀ x)
    (hint : ∀ n, Integrable (fun x => h n x * Real.log (h n x)) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => h n x) atTop (𝓝 (h₀ x)))
    {B : ℕ → ℝ} {T : ℝ} (hB : ∀ n, ∫ x, h n x * Real.log (h n x) ∂μ ≤ B n)
    (hBT : Tendsto B atTop (𝓝 T)) :
    Integrable (fun x => h₀ x * Real.log (h₀ x)) μ ∧
      ∫ x, h₀ x * Real.log (h₀ x) ∂μ ≤ T := by
  have hgmeas : ∀ n, Measurable (fun x => ENNReal.ofReal (h n x * Real.log (h n x) + 1)) :=
    fun n => ENNReal.measurable_ofReal.comp
      (((hmeas n).mul (Real.measurable_log.comp (hmeas n))).add_const 1)
  -- the lower integral of each shifted entropy
  have hintg : ∀ n, ∫⁻ x, ENNReal.ofReal (h n x * Real.log (h n x) + 1) ∂μ =
      ENNReal.ofReal (∫ x, h n x * Real.log (h n x) ∂μ + 1) := by
    intro n
    have hnonneg : 0 ≤ᵐ[μ] fun x => h n x * Real.log (h n x) + 1 :=
      Eventually.of_forall fun x => mul_log_add_one_nonneg (hnn n x)
    have hint1 : Integrable (fun x => h n x * Real.log (h n x) + 1) μ :=
      (hint n).add (integrable_const 1)
    rw [← ofReal_integral_eq_lintegral_ofReal hint1 hnonneg]
    congr 1
    rw [integral_add (hint n) (integrable_const 1), integral_const]
    simp
  -- almost everywhere convergence of the shifted integrands
  have hcont : Continuous fun r : ℝ => ENNReal.ofReal (r * Real.log r + 1) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_mul_log.add continuous_const)
  have hae : ∀ᵐ x ∂μ, Tendsto (fun n => ENNReal.ofReal (h n x * Real.log (h n x) + 1)) atTop
      (𝓝 (ENNReal.ofReal (h₀ x * Real.log (h₀ x) + 1))) := by
    filter_upwards [hlim] with x hx
    exact ((hcont.tendsto _).comp hx)
  -- Fatou's lemma and the entropy bound
  have hfatou := lintegral_liminf_le (μ := μ) (u := atTop) hgmeas
  have hliminf_ae : ∫⁻ x, Filter.liminf
      (fun n => ENNReal.ofReal (h n x * Real.log (h n x) + 1)) atTop ∂μ =
      ∫⁻ x, ENNReal.ofReal (h₀ x * Real.log (h₀ x) + 1) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    exact hx.liminf_eq
  have hbound : liminf (fun n => ∫⁻ x, ENNReal.ofReal (h n x * Real.log (h n x) + 1) ∂μ)
      atTop ≤ ENNReal.ofReal (T + 1) := by
    have hB' : ∀ n, ∫⁻ x, ENNReal.ofReal (h n x * Real.log (h n x) + 1) ∂μ ≤
        ENNReal.ofReal (B n + 1) := by
      intro n
      rw [hintg n]
      exact ENNReal.ofReal_le_ofReal (by linarith [hB n])
    have hBT' : Tendsto (fun n => ENNReal.ofReal (B n + 1)) atTop
        (𝓝 (ENNReal.ofReal (T + 1))) :=
      ENNReal.tendsto_ofReal (hBT.add_const 1)
    calc liminf (fun n => ∫⁻ x, ENNReal.ofReal (h n x * Real.log (h n x) + 1) ∂μ) atTop
        ≤ liminf (fun n => ENNReal.ofReal (B n + 1)) atTop :=
          liminf_le_liminf (Eventually.of_forall hB')
      _ = ENNReal.ofReal (T + 1) := hBT'.liminf_eq
  have hle₀ : ∫⁻ x, ENNReal.ofReal (h₀ x * Real.log (h₀ x) + 1) ∂μ ≤ ENNReal.ofReal (T + 1) := by
    rw [← hliminf_ae]
    exact hfatou.trans hbound
  -- the bound `T + 1 ≥ 0`, since each entropy is at least `-1`
  have hT1 : 0 ≤ T + 1 := by
    have hlow : ∀ n, -1 ≤ B n := fun n => by
      have hnonneg : 0 ≤ ∫ x, (h n x * Real.log (h n x) + 1) ∂μ :=
        integral_nonneg fun x => mul_log_add_one_nonneg (hnn n x)
      have hμ : μ.real Set.univ = 1 := by simp [measureReal_def]
      rw [integral_add (hint n) (integrable_const 1), integral_const, hμ, one_smul] at hnonneg
      linarith [hB n]
    have := ge_of_tendsto' hBT hlow
    linarith
  -- integrability of the shifted limit, from its finite lower integral
  have hnonneg₀ : 0 ≤ᵐ[μ] fun x => h₀ x * Real.log (h₀ x) + 1 :=
    Eventually.of_forall fun x => mul_log_add_one_nonneg (hnn₀ x)
  have hint₀ : Integrable (fun x => h₀ x * Real.log (h₀ x) + 1) μ := by
    refine ⟨((hmeas₀.mul (Real.measurable_log.comp_aemeasurable hmeas₀)).add_const 1).aestronglyMeasurable, ?_⟩
    have hfin : ∫⁻ x, ‖h₀ x * Real.log (h₀ x) + 1‖ₑ ∂μ ≠ ⊤ := by
      have heq : ∫⁻ x, ‖h₀ x * Real.log (h₀ x) + 1‖ₑ ∂μ =
          ∫⁻ x, ENNReal.ofReal (h₀ x * Real.log (h₀ x) + 1) ∂μ :=
        lintegral_congr fun x => Real.enorm_eq_ofReal (mul_log_add_one_nonneg (hnn₀ x))
      rw [heq]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle₀
    exact lt_top_iff_ne_top.2 hfin
  have hval : ∫⁻ x, ENNReal.ofReal (h₀ x * Real.log (h₀ x) + 1) ∂μ =
      ENNReal.ofReal (∫ x, h₀ x * Real.log (h₀ x) + 1 ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hint₀ hnonneg₀).symm
  rw [hval] at hle₀
  have hle : ∫ x, h₀ x * Real.log (h₀ x) + 1 ∂μ ≤ T + 1 :=
    (ENNReal.ofReal_le_ofReal_iff hT1).1 hle₀
  have hintE : Integrable (fun x => h₀ x * Real.log (h₀ x)) μ :=
    (hint₀.sub (integrable_const 1)).congr (Eventually.of_forall fun x => by simp)
  refine ⟨hintE, ?_⟩
  have hsplit : ∫ x, h₀ x * Real.log (h₀ x) + 1 ∂μ = ∫ x, h₀ x * Real.log (h₀ x) ∂μ + 1 := by
    rw [integral_add hintE (integrable_const 1), integral_const]
    simp
  linarith [hle, hsplit]

end Riesz1.WeightedSobolev

end

end
