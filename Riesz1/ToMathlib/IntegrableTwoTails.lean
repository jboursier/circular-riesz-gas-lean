/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Quantitative integrals with two power tails

An integral bound on a fixed central interval and two integrable power tails give
a bound independent of the remote endpoints. This supports Lemma 5.1.
-/

public section

open MeasureTheory Set intervalIntegral

namespace Riesz1

/-- A power tail below exponent `-1` has an integral bound independent of its endpoint. -/
theorem integral_abs_tail_le {q : ℝ → ℝ} {R z C e : ℝ}
    (hR : 0 < R) (hRz : R ≤ z) (hC : 0 ≤ C) (he : e < -1)
    (hi : IntervalIntegrable q volume R z)
    (hb : ∀ t ∈ Ioo R z, |q t| ≤ C * t ^ e) :
    (∫ t in R..z, |q t|) ≤ C / (-e - 1) * R ^ (e + 1) := by
  have hp : IntervalIntegrable (fun t : ℝ => C * t ^ e) volume R z := by
    apply IntervalIntegrable.const_mul
    apply intervalIntegrable_rpow
    right
    rw [uIcc_of_le hRz]
    exact fun ht => not_lt_of_ge ht.1 hR
  have hh := integral_mono_on_of_le_Ioo hRz hi.abs hp hb
  have hval : (∫ t in R..z, C * t ^ e) =
      C / (-e - 1) * (R ^ (e + 1) - z ^ (e + 1)) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow]
    · rw [show -e - 1 = -(e + 1) by ring, div_neg]
      ring
    · right
      refine ⟨by linarith, ?_⟩
      rw [uIcc_of_le hRz]
      exact fun ht => not_lt_of_ge ht.1 hR
  rw [hval] at hh
  have hn : 0 ≤ C / (-e - 1) * z ^ (e + 1) :=
    mul_nonneg (div_nonneg hC (by linarith)) (Real.rpow_nonneg (hR.le.trans hRz) _)
  nlinarith

/-- The integral of the absolute value over a symmetric interval is bounded by its
central contribution and two power tails, independently of the interval length. -/
theorem integral_abs_two_tails_le {q : ℝ → ℝ} {R z C e J : ℝ}
    (hR : 0 < R) (hRz : R ≤ z) (hC : 0 ≤ C) (he : e < -1)
    (hi : IntervalIntegrable q volume (-z) z)
    (hcenter : (∫ t in (-R)..R, |q t|) ≤ J)
    (hb : ∀ t : ℝ, R ≤ |t| → |t| ≤ z → |q t| ≤ C * |t| ^ e) :
    (∫ t in (-z)..z, |q t|) ≤ J + 2 * (C / (-e - 1) * R ^ (e + 1)) := by
  have hz : 0 ≤ z := hR.le.trans hRz
  have hip : IntervalIntegrable q volume R z := hi.mono_set (by
    rw [uIcc_of_le (by linarith : -z ≤ z), uIcc_of_le hRz]
    exact Icc_subset_Icc (by linarith) le_rfl)
  have hin : IntervalIntegrable q volume (-z) (-R) := hi.mono_set (by
    rw [uIcc_of_le (by linarith : -z ≤ z), uIcc_of_le (neg_le_neg hRz)]
    exact Icc_subset_Icc le_rfl (by linarith))
  have hic : IntervalIntegrable q volume (-R) R := hi.mono_set (by
    rw [uIcc_of_le (by linarith : -z ≤ z), uIcc_of_le (by linarith : -R ≤ R)]
    exact Icc_subset_Icc (neg_le_neg hRz) hRz)
  have hpos := integral_abs_tail_le hR hRz hC he hip (fun t ht => by
    have htp : 0 ≤ t := by linarith [ht.1]
    simpa only [abs_of_nonneg htp] using hb t
      (by simpa only [abs_of_nonneg htp] using ht.1.le)
      (by simpa only [abs_of_nonneg htp] using ht.2.le))
  have hiref : IntervalIntegrable (fun t => q (-t)) volume R z := by
    simpa only [zero_sub, neg_neg] using (hin.comp_sub_left 0).symm
  have hneg := integral_abs_tail_le hR hRz hC he hiref (fun t ht => by
    have htp : 0 ≤ t := by linarith [ht.1]
    simpa only [abs_neg, abs_of_nonneg htp] using hb (-t)
      (by simpa only [abs_neg, abs_of_nonneg htp] using ht.1.le)
      (by simpa only [abs_neg, abs_of_nonneg htp] using ht.2.le))
  rw [integral_comp_neg (fun t => |q t|)] at hneg
  rw [← integral_add_adjacent_intervals (hin.abs.trans hic.abs) hip.abs,
    ← integral_add_adjacent_intervals hin.abs hic.abs]
  linarith

end Riesz1
