/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingKernel

/-!
# Bounds for the modified kernel on the whole circle

The cutoff part of Lemma 5.8 (the bound `|F^*_γ| ≤ C C_0 K^{B_1}`). The
derivative bounds of `gradKernelH` hold only on `|r| ≤ 3/4`. This file extends them to
`3/4 < r < 1` by periodicity of the Riesz kernel `g = hurwitzKernel s`.

The reduction uses `h(r) = r g'(r) = h(r - 1) + g'(r - 1)`, which holds because `g'` is
1-periodic. Hence, for `3/4 < r < 1`, the modified kernel is bounded by a constant times
`(1 - r) ^ (-s - 1)`, the singularity of `g'` at the integer `1`.
-/

@[expose] public section

open Set Filter Topology

namespace Riesz1

noncomputable section

/-- The modified kernel `h = gradKernelH s` has two bounds, with one constant `C > 0`:
`|h(r)| ≤ C |r| ^ (-s)` for `|r| ≤ 3/4` (this includes `r = 0`, where `h(0) = 0`), and
`|h(r)| ≤ C (1 - r) ^ (-s - 1)` for `3/4 < r < 1`. -/
lemma gradKernelH_bound {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ (∀ r : ℝ, |r| ≤ 3 / 4 → |gradKernelH s r| ≤ C * |r| ^ (-s)) ∧
      (∀ r : ℝ, 3 / 4 < r → r < 1 → |gradKernelH s r| ≤ C * (1 - r) ^ (-s - 1)) := by
  obtain ⟨C, hC, hb⟩ := gradSplit_derivative_bounds s hs0 hs1
  refine ⟨2 * C, by positivity, fun r hr => ?_, fun r hr1 hr2 => ?_⟩
  · by_cases h0 : r = 0
    · subst h0
      simp [gradKernelH, Real.zero_rpow (neg_ne_zero.mpr hs0.ne')]
    · have h := (hb r (abs_pos.mpr h0) hr).2 0 (by norm_num)
      simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h
      have hx := mul_nonneg hC.le (Real.rpow_nonneg (abs_nonneg r) (-s))
      linarith
  · have hd0 : 0 < 1 - r := by linarith
    have hr0 : r - 1 < 0 := by linarith
    have habs : |r - 1| = 1 - r := by
      rw [abs_of_neg hr0]
      ring
    have hper : Function.Periodic (hurwitzKernel s) 1 := (gradient_splitting_kernel s hs0 hs1).2.1
    -- the derivative of the periodic kernel is periodic, so `g'(r - 1) = g'(r)`
    have hderiv : deriv (hurwitzKernel s) (r - 1) = deriv (hurwitzKernel s) r := by
      have h := deriv_comp_add_const (f := hurwitzKernel s) (a := 1) (x := r - 1)
      rw [show (fun y => hurwitzKernel s (y + 1)) = hurwitzKernel s from funext hper,
        sub_add_cancel] at h
      exact h
    have hsplit : gradKernelH s r = gradKernelH s (r - 1) + deriv (hurwitzKernel s) (r - 1) := by
      unfold gradKernelH
      rw [hderiv]
      ring
    have hmem : |r - 1| ≤ 3 / 4 := by
      rw [habs]
      linarith
    have h1 := (hb (r - 1) (abs_pos.mpr (ne_of_lt hr0)) hmem).2 0 (by norm_num)
    have h2 := (hb (r - 1) (abs_pos.mpr (ne_of_lt hr0)) hmem).1 1 le_rfl (by norm_num)
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h1
    simp only [iteratedDeriv_one, Nat.cast_one] at h2
    rw [habs] at h1 h2
    have hd_rpow : (1 - r) ^ (-s) ≤ (1 - r) ^ (-s - 1) := by
      rw [Real.rpow_sub_one hd0.ne' (-s), le_div_iff₀ hd0]
      exact mul_le_of_le_one_right (Real.rpow_nonneg hd0.le _) (by linarith)
    have hmul := mul_le_mul_of_nonneg_left hd_rpow hC.le
    rw [hsplit]
    calc |gradKernelH s (r - 1) + deriv (hurwitzKernel s) (r - 1)|
        ≤ |gradKernelH s (r - 1)| + |deriv (hurwitzKernel s) (r - 1)| := abs_add_le _ _
      _ ≤ C * (1 - r) ^ (-s) + C * (1 - r) ^ (-s - 1) := add_le_add h1 h2
      _ ≤ 2 * C * (1 - r) ^ (-s - 1) := by linarith

end

end Riesz1

end
