/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Stretched exponential decay against powers

For `a, c > 0` and any real `β`, the function `x ↦ x^β exp(-c x^a)` is bounded on `[1, ∞)`.
This is the step that absorbs polynomial factors into the stretched exponential tails of the
rigidity estimates in the loop moment bounds.
-/

public section

noncomputable section

open Real

namespace Riesz1

/-- **Stretched exponential decay.** For `a, c > 0` and every real `β`, there is `K ≥ 0` with
`x^β exp(-c x^a) ≤ K` for all `x ≥ 1`. -/
theorem rpow_mul_exp_neg_bounded {β a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x → x ^ β * Real.exp (-c * x ^ a) ≤ K := by
  -- Choose an integer `n` with `β ≤ n a`, so that the power `x^{β - n a}` is at most one.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, max β 0 / a ≤ n := ⟨⌈max β 0 / a⌉₊, Nat.le_ceil _⟩
  have hβn : β ≤ (n : ℝ) * a := by
    rw [div_le_iff₀ ha] at hn
    linarith [le_max_left β 0]
  refine ⟨(n.factorial : ℝ) / c ^ n, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx0 a
  -- `exp(c x^a) ≥ (c x^a)^n / n!`, which gives the bound on the exponential factor.
  have hexp : (c * x ^ a) ^ n / n.factorial ≤ Real.exp (c * x ^ a) :=
    pow_div_factorial_le_exp (c * x ^ a) (by positivity) n
  have hpow : (x ^ a) ^ n = x ^ ((n : ℝ) * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    ring_nf
  have hexp_neg : Real.exp (-c * x ^ a) ≤ (n.factorial : ℝ) / c ^ n * (x ^ ((n : ℝ) * a))⁻¹ := by
    have hpos : 0 < Real.exp (c * x ^ a) := Real.exp_pos _
    have h1 : Real.exp (-c * x ^ a) = (Real.exp (c * x ^ a))⁻¹ := by
      rw [← Real.exp_neg]
      ring_nf
    rw [h1]
    have hden : 0 < (c * x ^ a) ^ n := by positivity
    calc (Real.exp (c * x ^ a))⁻¹ ≤ ((c * x ^ a) ^ n / n.factorial)⁻¹ :=
          inv_anti₀ (by positivity) hexp
      _ = (n.factorial : ℝ) / c ^ n * (x ^ ((n : ℝ) * a))⁻¹ := by
          rw [mul_pow, ← hpow]
          field_simp
  have hxβ : x ^ β * (x ^ ((n : ℝ) * a))⁻¹ ≤ 1 := by
    rw [← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  calc x ^ β * Real.exp (-c * x ^ a)
      ≤ x ^ β * ((n.factorial : ℝ) / c ^ n * (x ^ ((n : ℝ) * a))⁻¹) :=
        mul_le_mul_of_nonneg_left hexp_neg (Real.rpow_nonneg hx0.le _)
    _ = (n.factorial : ℝ) / c ^ n * (x ^ β * (x ^ ((n : ℝ) * a))⁻¹) := by ring
    _ ≤ (n.factorial : ℝ) / c ^ n * 1 :=
        mul_le_mul_of_nonneg_left hxβ (by positivity)
    _ = (n.factorial : ℝ) / c ^ n := mul_one _

end Riesz1

end
end
