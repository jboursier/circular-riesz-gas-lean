/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.BellRandomSumIntegrability
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# A global comparison of the averaged kernel at two points

The mean value estimate used for the random-sum part of Lemma B.1. The four
endpoint inverse powers bound the derivative on the entire intervening segment.
There is no restriction to a good event or to large block lengths.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace Riesz1

/-- A decreasing power on an interval is bounded by the sum of its endpoint powers. -/
lemma bell_rpow_segment_bound {a b z p : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hz : z ∈ uIcc a b) (hp : p ≤ 0) : z ^ p ≤ a ^ p + b ^ p := by
  have hm : 0 < min a b := lt_min ha hb
  have h := Real.rpow_le_rpow_of_nonpos hm hz.1 hp
  exact h.trans (rpow_min_le_add a b p ha hb)

/-- The derivative bound controls differences globally on `(0,N)`. This estimate
uses only endpoint inverse powers, which have uniform Gibbs moments. -/
lemma bell_kernel_difference_bound {s C : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {N : ℕ} (hN : 0 < N) {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hC : 0 ≤ C)
    (hd : ∀ z ∈ Ioo (0 : ℝ) N,
      |deriv (bellKernel s N ℓ ψ) z| ≤
        C * bellConstant ℓ ψ * min z ((N : ℝ) - z) ^ (-1 - s))
    {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) N) (hy : y ∈ Ioo (0 : ℝ) N) :
    |bellKernel s N ℓ ψ x - bellKernel s N ℓ ψ y| ≤
      C * bellConstant ℓ ψ *
        (x ^ (-1 - s) + ((N : ℝ) - x) ^ (-1 - s) +
          y ^ (-1 - s) + ((N : ℝ) - y) ^ (-1 - s)) * |x - y| := by
  have hA : 0 ≤ C * bellConstant ℓ ψ :=
    mul_nonneg hC (mul_nonneg hℓ.le (bellEnergy_nonneg hℓ))
  have hsub : uIcc y x ⊆ Ioo (0 : ℝ) N :=
    fun z hz => ⟨(lt_min hy.1 hx.1).trans_le hz.1,
      hz.2.trans_lt (max_lt hy.2 hx.2)⟩
  have hb : ∀ z ∈ uIcc y x, |deriv (bellKernel s N ℓ ψ) z| ≤
      C * bellConstant ℓ ψ *
        (x ^ (-1 - s) + ((N : ℝ) - x) ^ (-1 - s) +
          y ^ (-1 - s) + ((N : ℝ) - y) ^ (-1 - s)) := by
    intro z hz
    have hzN := hsub hz
    have hz' : (N : ℝ) - z ∈ uIcc ((N : ℝ) - x) ((N : ℝ) - y) := by
      rcases le_total y x with h | h
      · rw [uIcc_of_le h] at hz
        rw [uIcc_of_le (sub_le_sub_left h _)]
        constructor <;> linarith [hz.1, hz.2]
      · rw [uIcc_of_ge h] at hz
        rw [uIcc_of_ge (sub_le_sub_left h _)]
        constructor <;> linarith [hz.1, hz.2]
    have h1 := bell_rpow_segment_bound hy.1 hx.1 hz (show -1 - s ≤ 0 by linarith)
    have h2 := bell_rpow_segment_bound (sub_pos.mpr hx.2) (sub_pos.mpr hy.2) hz'
      (show -1 - s ≤ 0 by linarith)
    refine (hd z hzN).trans (mul_le_mul_of_nonneg_left ?_ hA)
    calc min z ((N : ℝ) - z) ^ (-1 - s)
        ≤ z ^ (-1 - s) + ((N : ℝ) - z) ^ (-1 - s) :=
          rpow_min_le_add _ _ _ hzN.1 (sub_pos.mpr hzN.2)
      _ ≤ x ^ (-1 - s) + ((N : ℝ) - x) ^ (-1 - s) +
          y ^ (-1 - s) + ((N : ℝ) - y) ^ (-1 - s) := by linarith
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hasDerivAt_bellKernel hs hs1 hN hℓ hψ (hsub hz)).differentiableAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using hb z hz)
    (convex_uIcc y x) (left_mem_uIcc) (right_mem_uIcc)
  simpa only [Real.norm_eq_abs] using hm

end Riesz1

end
