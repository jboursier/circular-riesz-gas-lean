/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.BellRandomSumIntegrability
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Comparison on the good event

When a short block stays within half its lattice length, the segment joining
it to that length stays away from both singularities. The derivative bound
then applies at the lattice scale.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace Riesz1

/-- The derivative estimate at the block scale controls the good event. -/
lemma bell_kernel_good_event {s C : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {N : ℕ} (hN : 0 < N) {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hC : 0 ≤ C)
    (hd : ∀ z ∈ Ioo (0 : ℝ) N,
      |deriv (bellKernel s N ℓ ψ) z| ≤
        C * bellConstant ℓ ψ * min z ((N : ℝ) - z) ^ (-1 - s))
    {x k t : ℝ} (hk : 0 < k) (hkN : k ≤ (N : ℝ) / 2)
    (ht : k ^ t ≤ k / 2) (hx : |x - k| ≤ k ^ t) :
    |bellKernel s N ℓ ψ x - bellKernel s N ℓ ψ k| ≤
      C * bellConstant ℓ ψ * (1 / 2 : ℝ) ^ (-1 - s) * k ^ (-1 - s + t) := by
  have hA : 0 ≤ C * bellConstant ℓ ψ :=
    mul_nonneg hC (mul_nonneg hℓ.le (bellEnergy_nonneg hℓ))
  have hx' := abs_le.mp (hx.trans ht)
  have hseg (z : ℝ) (hz : z ∈ uIcc k x) :
      k / 2 ≤ min z ((N : ℝ) - z) := by
    refine le_min ?_ ?_
    · exact (le_min (by linarith) (by linarith)).trans hz.1
    · have hh := hz.2.trans (max_le (by linarith : k ≤ (N : ℝ) - k / 2)
          (by linarith : x ≤ (N : ℝ) - k / 2))
      linarith
  have hsub (z : ℝ) (hz : z ∈ uIcc k x) : z ∈ Ioo (0 : ℝ) N := by
    have hh := hseg z hz
    have h1 := hh.trans (min_le_left _ _)
    have h2 := hh.trans (min_le_right _ _)
    constructor <;> linarith
  have hb (z : ℝ) (hz : z ∈ uIcc k x) :
      |deriv (bellKernel s N ℓ ψ) z| ≤
        C * bellConstant ℓ ψ * (k / 2) ^ (-1 - s) :=
    (hd z (hsub z hz)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) (hseg z hz) (by linarith)) hA)
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hasDerivAt_bellKernel hs hs1 hN hℓ hψ (hsub z hz)).differentiableAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using hb z hz)
    (convex_uIcc k x) left_mem_uIcc right_mem_uIcc
  have hm' : |bellKernel s N ℓ ψ x - bellKernel s N ℓ ψ k| ≤
      C * bellConstant ℓ ψ * (k / 2) ^ (-1 - s) * |x - k| := by
    simpa only [Real.norm_eq_abs] using hm
  have hbound : |bellKernel s N ℓ ψ x - bellKernel s N ℓ ψ k| ≤
      C * bellConstant ℓ ψ * (k / 2) ^ (-1 - s) * k ^ t :=
    hm'.trans
      (mul_le_mul_of_nonneg_left hx (by positivity))
  convert hbound using 1
  rw [show k / 2 = (1 / 2 : ℝ) * k by ring, Real.mul_rpow (by norm_num) hk.le]
  rw [show C * bellConstant ℓ ψ * ((1 / 2 : ℝ) ^ (-1 - s) * k ^ (-1 - s)) * k ^ t =
    C * bellConstant ℓ ψ * (1 / 2 : ℝ) ^ (-1 - s) * (k ^ (-1 - s) * k ^ t) by ring,
    ← Real.rpow_add hk]

end Riesz1

end
