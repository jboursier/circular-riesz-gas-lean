/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.Basic

/-!
# Integrals of `|y - x| ^ (-s)` over intervals of radius `R`

For `s < 1`, the singularity `|y - x| ^ (-s)` is integrable on every interval, and an interval
of a fixed radius `R` around `x` carries integral at most `2 R ^ (1 - s) / (1 - s)`. These are the
background integral estimates behind the anchored cutoff bound (Lemma 5.8).
-/

public section

open MeasureTheory Set intervalIntegral

namespace Riesz1

/-- The function `r ↦ |r| ^ (-s)` is interval integrable on `[-R, R]` when `s < 1` and `R ≥ 0`. -/
lemma intervalIntegrable_abs_rpow_neg_radius {s R : ℝ} (hs1 : s < 1) (hR : 0 ≤ R) :
    IntervalIntegrable (fun r : ℝ => |r| ^ (-s)) volume (-R) R := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
  exact integrableOn_abs_rpow (by linarith) hR

/-- The function `y ↦ |y - x| ^ (-s)` is interval integrable on `[a, b]` when `[a, b]` lies in
`[x - R, x + R]`. -/
lemma intervalIntegrable_abs_sub_rpow_radius {s x a b R : ℝ} (hs1 : s < 1) (hR : 0 ≤ R)
    (hab : a ≤ b) (ha : x - R ≤ a) (hb : b ≤ x + R) :
    IntervalIntegrable (fun y : ℝ => |y - x| ^ (-s)) volume a b := by
  have hf := intervalIntegrable_abs_rpow_neg_radius hs1 hR
  have hsub : uIcc (a - x) (b - x) ⊆ uIcc (-R) R :=
    Set.uIcc_subset_uIcc (Set.mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩))
      (Set.mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩))
  have h := (hf.mono_set hsub).comp_sub_right x
  rw [sub_add_cancel, sub_add_cancel] at h
  exact h

/-- For `s < 1`, the integral of `|y - x| ^ (-s)` over an interval `[a, b]` lying in
`[x - R, x + R]` is at most `2 R ^ (1 - s) / (1 - s)`. -/
lemma integral_abs_sub_rpow_le_radius {s x a b R : ℝ} (hs1 : s < 1) (hR : 0 ≤ R) (hab : a ≤ b)
    (ha : x - R ≤ a) (hb : b ≤ x + R) :
    ∫ y in a..b, |y - x| ^ (-s) ≤ 2 * R ^ (1 - s) / (1 - s) := by
  have hf := intervalIntegrable_abs_rpow_neg_radius hs1 hR
  calc ∫ y in a..b, |y - x| ^ (-s) = ∫ r in a - x..b - x, |r| ^ (-s) :=
        intervalIntegral.integral_comp_sub_right (fun r : ℝ => |r| ^ (-s)) x
    _ ≤ ∫ r in (-R)..R, |r| ^ (-s) :=
        intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
          (Filter.Eventually.of_forall fun r => Real.rpow_nonneg (abs_nonneg r) _) hf
    _ = 2 * R ^ (1 - s) / (1 - s) := by
        rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
        exact integral_abs_rpow_symm (by linarith) hR

end Riesz1

end
