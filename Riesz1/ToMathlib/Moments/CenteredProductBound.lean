/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# A bounded factor against a centred square-integrable variable

For a probability measure `μ`, a square-integrable `F` with mean `m = ∫ F dμ`, and a function
`g` bounded by `G`, the centred product satisfies

`|∫ g (F - m) dμ| ≤ G √(∫ (F - m)² dμ)`.

This is the Cauchy–Schwarz step that bounds `Error¹_N(u)` by the square root of the variance
(Theorem 3). The proof uses only `∫ |h| ≤ √(∫ h²)` for the centred `h = F - m`,
which follows from `0 ≤ ∫ (|h| - ∫|h|)² = ∫ h² - (∫ |h|)²`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The first absolute moment of a square-integrable centred variable is at most the square
root of its second moment, for a probability measure. -/
lemma integral_abs_le_sqrt_integral_sq {μ : Measure Ω} [IsProbabilityMeasure μ] {h : Ω → ℝ}
    (hL2 : MemLp h 2 μ) :
    ∫ x, |h x| ∂μ ≤ Real.sqrt (∫ x, h x ^ 2 ∂μ) := by
  have hsq : Integrable (fun x => h x ^ 2) μ := hL2.integrable_sq
  have hab : Integrable (fun x => |h x|) μ := hL2.integrable one_le_two |>.abs
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ∫ x, |h x| ∂μ := ⟨_, rfl⟩
  -- `∫ (|h| - m)² = ∫ h² - m²`, because `∫ |h| = m` and `μ` is a probability measure.
  have hexp : ∫ x, (|h x| - m) ^ 2 ∂μ = ∫ x, h x ^ 2 ∂μ - m ^ 2 := by
    have e : ∀ x, (|h x| - m) ^ 2 = (h x ^ 2 - 2 * m * |h x|) + m ^ 2 := by
      intro x
      rw [← sq_abs (h x)]
      ring
    have hpart : Integrable (fun x => h x ^ 2 - 2 * m * |h x|) μ := hsq.sub (hab.const_mul _)
    simp_rw [e]
    rw [integral_add hpart (integrable_const _),
      integral_sub hsq (hab.const_mul _), integral_const_mul, integral_const, ← hm]
    simp
    ring
  have hnn : 0 ≤ ∫ x, (|h x| - m) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hsq_le : m ^ 2 ≤ ∫ x, h x ^ 2 ∂μ := by linarith
  have hm_nn : 0 ≤ m := hm ▸ integral_nonneg fun x => abs_nonneg _
  rw [← hm]
  calc m = Real.sqrt (m ^ 2) := (Real.sqrt_sq hm_nn).symm
    _ ≤ Real.sqrt (∫ x, h x ^ 2 ∂μ) := Real.sqrt_le_sqrt hsq_le

/-- **Centred Cauchy–Schwarz bound.** For a probability measure `μ`, a square-integrable `F`
and a function `g` with `|g| ≤ G` a.e. and strongly measurable, the centred product
`∫ g (F - ∫ F)` is bounded by `G` times the square root of the centred second moment. -/
lemma abs_integral_mul_centred_le {μ : Measure Ω} [IsProbabilityMeasure μ] {F g : Ω → ℝ}
    (hF : MemLp F 2 μ) {G : ℝ} (hG : 0 ≤ G) (hgb : ∀ x, |g x| ≤ G) :
    |∫ x, g x * (F x - ∫ y, F y ∂μ) ∂μ| ≤
      G * Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) := by
  set h : Ω → ℝ := fun x => F x - ∫ y, F y ∂μ with hh
  have hL2 : MemLp h 2 μ := hF.sub (memLp_const _)
  have hbound : |∫ x, g x * h x ∂μ| ≤ G * ∫ x, |h x| ∂μ := by
    calc |∫ x, g x * h x ∂μ| ≤ ∫ x, |g x * h x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, G * |h x| ∂μ := by
          refine integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _)
            ((hL2.integrable one_le_two |>.abs).const_mul G) (ae_of_all _ fun x => ?_)
          show |g x * h x| ≤ G * |h x|
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hgb x) (abs_nonneg _)
      _ = G * ∫ x, |h x| ∂μ := integral_const_mul _ _
  calc |∫ x, g x * (F x - ∫ y, F y ∂μ) ∂μ| = |∫ x, g x * h x ∂μ| := rfl
    _ ≤ G * ∫ x, |h x| ∂μ := hbound
    _ ≤ G * Real.sqrt (∫ x, h x ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_left (integral_abs_le_sqrt_integral_sq hL2) hG

end Riesz1

end
end
