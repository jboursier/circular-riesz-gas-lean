/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.InterchangeBound
public import Mathlib.Analysis.PSeries
public import Mathlib.Tactic

/-!
# Absolute summability of the interchange integrals

For `|k| ≥ 2`, the interchange integrand satisfies, for every `t > 0`,
`|u_k^x(t)| ≤ t^{-1-s/2} · (|k| + 1)/(2t) · e^{-k²/(16t)}`
(`Riesz1.abs_interchangeTerm_le`). Integrating and using the reciprocal-time Gamma integral gives
`∫_{(0,∞)} |u_k^x| dt ≤ (|k| + 1) / 2 · (k²/16)^{-(1+s/2)} Γ(1+s/2)`, which is at most a constant
times `|k|^{-(1+s)}`. The series `∑_k |k|^{-(1+s)}` converges, so the integrals are summable.

Main results:
* `Riesz1.abs_interchangeTerm_le`: the pointwise bound for `|k| ≥ 2`.
* `Riesz1.integral_abs_interchangeTerm_le`: the integrated bound.
* `Riesz1.summable_integral_abs_interchangeTerm`: `∑_k ∫_{(0,∞)} |u_k^x(t)| dt` converges.
-/

public section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- For `|k| ≥ 2`, `|u_k^x(t)| ≤ t^{-1-s/2} · (|k|+1)/(2t) · e^{-k²/(16t)}` for every `t > 0`. -/
lemma abs_interchangeTerm_le {s x : ℝ} (k : ℤ) (hk : 2 ≤ |(k : ℝ)|) (hx0 : 0 < x) (hx1 : x < 1)
    {t : ℝ} (ht : 0 < t) :
    |interchangeTerm s x k t| ≤
      t ^ (-1 - s / 2) * ((|(k : ℝ)| + 1) / (2 * t) * Real.exp (-((k : ℝ) ^ 2 / (16 * t)))) := by
  have hpow : 0 ≤ t ^ (-1 - s / 2) := Real.rpow_nonneg ht.le _
  rw [show interchangeTerm s x k t = t ^ (-1 - s / 2) *
      (Real.exp (-(x - k) ^ 2 / (4 * t)) - gaussAverage k t) from rfl]
  -- The average of the Gaussian differences over `[0, 1]` is bounded pointwise.
  have hdiff : |Real.exp (-(x - k) ^ 2 / (4 * t)) - gaussAverage k t| ≤
      (|(k : ℝ)| + 1) / (2 * t) * Real.exp (-((k : ℝ) ^ 2 / (16 * t))) := by
    have hrepr : Real.exp (-(x - k) ^ 2 / (4 * t)) - gaussAverage k t =
        ∫ y in (0 : ℝ)..1, (Real.exp (-(x - k) ^ 2 / (4 * t)) -
          Real.exp (-(y - k) ^ 2 / (4 * t))) := by
      simp only [gaussAverage]
      rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable 0 1)
        ((continuous_gauss_shift k t).intervalIntegrable 0 1)]
      simp
    rw [hrepr]
    have hC := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1)
      (C := (|(k : ℝ)| + 1) / (2 * t) * Real.exp (-((k : ℝ) ^ 2 / (16 * t))))
      (f := fun y : ℝ => Real.exp (-(x - k) ^ 2 / (4 * t)) -
        Real.exp (-(y - k) ^ 2 / (4 * t))) (fun y hy => by
        rw [uIoc_of_le zero_le_one] at hy
        rw [Real.norm_eq_abs]
        exact abs_gauss_sub_gauss_le ht k hk hx0.le hx1.le hy.1.le hy.2)
    rw [Real.norm_eq_abs] at hC
    simpa using hC
  rw [abs_mul, abs_of_nonneg hpow]
  exact mul_le_mul_of_nonneg_left hdiff hpow

/-- The rpow identity `((k²/16))^{-(1+s/2)} = 16^{1+s/2} |k|^{-(2+s)}`. -/
lemma rpow_sq_div_sixteen (s k : ℝ) :
    (k ^ 2 / 16) ^ (-(1 + s / 2)) = 16 ^ (1 + s / 2) * |k| ^ (-(2 + s)) := by
  rw [Real.div_rpow (sq_nonneg k) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16),
    div_inv_eq_mul, ← sq_abs k, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg k)]
  rw [show ((2 : ℕ) : ℝ) * -(1 + s / 2) = -(2 + s) by push_cast; ring]
  ring

/-- The reciprocal-time Gamma integral bound for the interchange integrand, for `|k| ≥ 2`:
`∫_{(0,∞)} |u_k^x(t)| dt ≤ (|k| + 1)/2 · (k²/16)^{-(1+s/2)} Γ(1+s/2)`. -/
lemma integral_abs_interchangeTerm_le {s x : ℝ} (hs0 : 0 < s) (hx0 : 0 < x) (hx1 : x < 1)
    (k : ℤ) (hk : 2 ≤ |(k : ℝ)|) :
    ∫ t in Ioi (0 : ℝ), |interchangeTerm s x k t| ≤
      (|(k : ℝ)| + 1) / 2 * (((k : ℝ) ^ 2 / 16) ^ (-(1 + s / 2)) * Real.Gamma (1 + s / 2)) := by
  have h4 : 4 ≤ (k : ℝ) ^ 2 := by
    have h := sq_abs (k : ℝ)
    nlinarith [abs_nonneg (k : ℝ)]
  have hk0 : 0 < (k : ℝ) ^ 2 / 16 := div_pos (by linarith) (by norm_num)
  have hG := integrableOn_rpow_neg_exp_div_Ioi (α := 1 + s / 2) (c := (k : ℝ) ^ 2 / 16)
    (by linarith) hk0
  have hbound : IntegrableOn (fun t : ℝ => (|(k : ℝ)| + 1) / 2 *
      (t ^ (-1 - (1 + s / 2)) * Real.exp (-((k : ℝ) ^ 2 / 16) / t))) (Ioi 0) :=
    hG.const_mul _
  have hle : ∫ t in Ioi (0 : ℝ), |interchangeTerm s x k t| ≤
      ∫ t in Ioi (0 : ℝ), (|(k : ℝ)| + 1) / 2 *
        (t ^ (-1 - (1 + s / 2)) * Real.exp (-((k : ℝ) ^ 2 / 16) / t)) := by
    refine integral_mono_of_nonneg (ae_of_all _ fun t => abs_nonneg _) hbound ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    refine (abs_interchangeTerm_le (s := s) k hk hx0 hx1 ht0).trans (le_of_eq ?_)
    have hpow : t ^ (-1 - (1 + s / 2)) = t ^ (-1 - s / 2) * t⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ht0]
      congr 1
      ring
    have hexp : Real.exp (-((k : ℝ) ^ 2 / 16) / t) = Real.exp (-((k : ℝ) ^ 2 / (16 * t))) := by
      congr 1
      ring
    rw [hpow, hexp]
    ring
  rw [integral_const_mul] at hle
  refine hle.trans (le_of_eq ?_)
  rw [integral_rpow_neg_exp_div_Ioi (α := 1 + s / 2) (c := (k : ℝ) ^ 2 / 16) (by linarith) hk0]

/-- The interchange integrals of the absolute values are summable over `k ∈ ℤ`, for `0 < s < 1` and
`0 < x < 1`: `∑_k ∫_{(0,∞)} |u_k^x(t)| dt < ∞`. -/
theorem summable_integral_abs_interchangeTerm {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hx0 : 0 < x) (hx1 : x < 1) :
    Summable (fun k : ℤ => ∫ t in Ioi (0 : ℝ), |interchangeTerm s x k t|) := by
  set K : ℝ := Real.Gamma (1 + s / 2) * 16 ^ (1 + s / 2) with hK
  have hsum : Summable (fun k : ℤ => K * |(k : ℝ)| ^ (-(1 + s))) :=
    (Real.summable_abs_int_rpow (b := 1 + s) (by linarith)).mul_left K
  refine Summable.of_norm_bounded_eventually hsum ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_Icc (-1 : ℤ) 1).subset ?_
  intro k hk
  by_contra hcon
  refine hk ?_
  have hk2 : (2 : ℝ) ≤ |(k : ℝ)| := by
    have hZ : (2 : ℤ) ≤ |k| := by
      rw [Set.mem_Icc] at hcon
      rcases le_or_gt 0 k with h0 | h0
      · rw [abs_of_nonneg h0]
        omega
      · rw [abs_of_neg h0]
        omega
    have := (Int.cast_le (R := ℝ)).2 hZ
    simpa [Int.cast_abs] using this
  have hnn : 0 ≤ ∫ t in Ioi (0 : ℝ), |interchangeTerm s x k t| :=
    setIntegral_nonneg measurableSet_Ioi (fun t _ => abs_nonneg _)
  rw [Real.norm_of_nonneg hnn]
  refine (integral_abs_interchangeTerm_le hs0 hx0 hx1 k hk2).trans ?_
  -- Compare `(|k|+1)/2 · 16^{1+s/2} |k|^{-(2+s)} Γ(1+s/2)` with `K |k|^{-(1+s)}`.
  set a : ℝ := |(k : ℝ)| with ha
  have ha1 : 1 ≤ a := by linarith
  have hsplit : a ^ (-(2 + s)) = a ^ (-(1 + s)) * a⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add (by linarith)]
    congr 1
    ring
  have hfac : (a + 1) / 2 * a⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by linarith)]
    linarith
  have hP : 0 ≤ 16 ^ (1 + s / 2) * Real.Gamma (1 + s / 2) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.Gamma_pos_of_pos (by linarith)).le
  have hR : 0 ≤ a ^ (-(1 + s)) := Real.rpow_nonneg (by linarith) _
  rw [rpow_sq_div_sixteen s (k : ℝ), ← ha, hsplit, hK]
  calc (a + 1) / 2 * (16 ^ (1 + s / 2) * (a ^ (-(1 + s)) * a⁻¹) * Real.Gamma (1 + s / 2))
      = ((a + 1) / 2 * a⁻¹) * (16 ^ (1 + s / 2) * Real.Gamma (1 + s / 2) * a ^ (-(1 + s))) := by
        ring
    _ ≤ 1 * (16 ^ (1 + s / 2) * Real.Gamma (1 + s / 2) * a ^ (-(1 + s))) :=
        mul_le_mul_of_nonneg_right hfac (mul_nonneg hP hR)
    _ = Real.Gamma (1 + s / 2) * 16 ^ (1 + s / 2) * a ^ (-(1 + s)) := by ring

end Riesz1
