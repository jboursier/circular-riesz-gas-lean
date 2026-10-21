/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LogConcave.Moments
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Weighted tails from exponential moments

An exponential moment controls the first moment above a threshold, with
half the exponential rate. No probability normalization is required.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- The weighted tail of a nonnegative random variable with exponential
moment at most `A` is at most `(2 A / c) exp (-c u / 2)`. -/
theorem weighted_tail_le_of_exp_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {w : Ω → ℝ} (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    {c A : ℝ} (hc : 0 < c)
    (hi : Integrable (fun x => Real.exp (c * w x)) μ)
    (hA : ∫ x, Real.exp (c * w x) ∂μ ≤ A) (u : ℝ) :
    ∫ x in {x | u < w x}, w x ∂μ ≤ (2 * A / c) * Real.exp (-c * u / 2) := by
  obtain ⟨hwi, _⟩ := moment_le_of_exp_moment_le hc w hw hw0 hi hA 1 zero_lt_one
  simp only [Real.rpow_one] at hwi
  let B := (2 / c) * Real.exp (-c * u / 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (x : Ω) (hx : u < w x) : w x ≤ B * Real.exp (c * w x) := by
    have h1 : c * w x / 2 ≤ Real.exp (c * w x / 2) := by
      linarith [Real.add_one_le_exp (c * w x / 2)]
    have h2 : Real.exp (c * w x / 2) ≤ Real.exp (c * w x - c * u / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have he : B * Real.exp (c * w x) = (2 / c) *
        Real.exp (c * w x - c * u / 2) := by
      dsimp [B]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [he]
    have hm := mul_le_mul_of_nonneg_left (h1.trans h2) (show 0 ≤ 2 / c by positivity)
    have he' : (2 / c) * (c * w x / 2) = w x := by field_simp
    rwa [he'] at hm
  calc ∫ x in {x | u < w x}, w x ∂μ
      ≤ ∫ x in {x | u < w x}, B * Real.exp (c * w x) ∂μ := by
        apply setIntegral_mono_on hwi.integrableOn (hi.const_mul B).integrableOn
          (measurableSet_lt measurable_const hw)
        exact hb
    _ ≤ ∫ x, B * Real.exp (c * w x) ∂μ :=
      setIntegral_le_integral (hi.const_mul B) (ae_of_all _ fun _ => by positivity)
    _ = B * ∫ x, Real.exp (c * w x) ∂μ := integral_const_mul _ _
    _ ≤ B * A := mul_le_mul_of_nonneg_left hA hB
    _ = _ := by dsimp [B]; ring

end Riesz1
