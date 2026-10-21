/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

/-!
# Scale comparisons for rigidity assembly

The large-scale cutoff and elementary stretched exponential comparisons
in the proof of Theorem 1.
-/

public section

open Filter

namespace Riesz1.Internal

/-- One cutoff enforces all three hypotheses needed in count inversion. -/
theorem rigidity_large_scale {s eps : ℝ} (hs : 0 < s) (heps : 0 < eps)
    (ha : s / 2 + eps < 1) :
    ∃ K0 : ℝ, 2 ≤ K0 ∧ ∀ K : ℝ, K0 ≤ K →
      2 ≤ K ^ (s / 2 + eps) ∧ K ^ (s / 2 + eps) + 1 ≤ K ∧
        (3 * K) ^ (s / 2 + eps / 2) ≤ K ^ (s / 2 + eps) / 2 := by
  have h1 := (tendsto_rpow_atTop (by linarith : 0 < s / 2 + eps)).eventually
    (eventually_ge_atTop 2)
  have h2 := (tendsto_rpow_atTop (by linarith : 0 < 1 - (s / 2 + eps))).eventually
    (eventually_ge_atTop 2)
  have h3 := (tendsto_rpow_atTop (half_pos heps)).eventually
    (eventually_ge_atTop (2 * (3 : ℝ) ^ (s / 2 + eps / 2)))
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp (h1.and (h2.and h3))
  refine ⟨max 2 K0, le_max_left _ _, fun K hK => ?_⟩
  have hK2 : 2 ≤ K := (le_max_left _ _).trans hK
  have hKpos : 0 < K := by linarith
  obtain ⟨hp1, hp2, hp3⟩ := hK0 K ((le_max_right _ _).trans hK)
  refine ⟨hp1, ?_, ?_⟩
  · have hprod : K ^ (s / 2 + eps) * K ^ (1 - (s / 2 + eps)) = K := by
      rw [← Real.rpow_add hKpos]
      simp
    have := mul_le_mul_of_nonneg_left hp2 (Real.rpow_nonneg hKpos.le (s / 2 + eps))
    nlinarith
  · have hsplit : K ^ (s / 2 + eps) =
        K ^ (s / 2 + eps / 2) * K ^ (eps / 2) := by
      rw [← Real.rpow_add hKpos]
      congr 1
      ring
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hKpos.le, hsplit]
    have := mul_le_mul_of_nonneg_left hp3
      (Real.rpow_nonneg hKpos.le (s / 2 + eps / 2))
    nlinarith

/-- Monotonicity of an exponential tail, in its rate. -/
theorem rigidity_exp_rate_mono {c d t : ℝ} (hcd : c ≤ d) (ht : 0 ≤ t) :
    Real.exp (-d * t) ≤ Real.exp (-c * t) := by
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Square-root selection halves the exponential rate. -/
theorem rigidity_sqrt_tail {p B C c t : ℝ} (hp : 0 ≤ p) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : p ≤ C * Real.exp (-c * t)) :
    B * p ^ (1 / (2 : ℝ)) ≤ B * C ^ (1 / (2 : ℝ)) * Real.exp (-(c / 2) * t) := by
  calc
    B * p ^ (1 / (2 : ℝ)) ≤ B * (C * Real.exp (-c * t)) ^ (1 / (2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp h (by norm_num)) hB
    _ = _ := by
      rw [Real.mul_rpow hC (Real.exp_pos _).le, ← Real.exp_mul]
      have he : (-c * t) * (1 / (2 : ℝ)) = -(c / 2) * t := by ring
      rw [he, mul_assoc]

end Riesz1.Internal
