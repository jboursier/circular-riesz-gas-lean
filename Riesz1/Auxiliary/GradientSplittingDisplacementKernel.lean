/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingKernel

/-!
# Mean value bound for the kernel `h` in the displacement estimate

The displacement part of Lemma 5.7. The displacement bound
compares `h(r)` with `h(t)` for a lift separation `r` and a lattice increment `t = k/N` of the same
sign, where `|r| ≥ μ |t|` for some `μ ∈ (0, 1]`. The two points are joined by a segment whose
points `u` satisfy `u ≥ μ |t|` and `u ≤ 3/4`. The derivative of `h` on that segment is controlled
by the kernel bound `gradient_splitting_kernel`, which gives
`|h'(u)| ≤ C |u|^{-s-1}`, and the mean value inequality gives the bound
`|h(r) - h(t)| ≤ C (μ |t|)^{-s-1} |r - t|`.

Only the derivative bound on `(0, 3/4]` and the smoothness of `h` on the non-integers enter.
-/

@[expose] public section

namespace Riesz1

noncomputable section

/-- The mean value bound for `h` on the positive axis: if `μ t ≤ r`, `0 < μ ≤ 1`, and
`0 < t, r ≤ 3/4`, then `|h(r) - h(t)| ≤ C (μ t)^{-s-1} |r - t|`, where `C` bounds `h'` on
`(0, 3/4]`. -/
lemma gradKernel_sub_le_pos {s C₁ μ t r : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hC₀ : 0 ≤ C₁)
    (hC₁ : ∀ u : ℝ, 0 < u → u ≤ 3 / 4 → |iteratedDeriv 1 (gradKernelH s) u| ≤ C₁ * u ^ (-s - 1))
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (ht : 0 < t) (ht34 : t ≤ 3 / 4) (hr : μ * t ≤ r)
    (hr34 : r ≤ 3 / 4) :
    |gradKernelH s r - gradKernelH s t| ≤ C₁ * (μ * t) ^ (-s - 1) * |r - t| := by
  have hmt : 0 < μ * t := mul_pos hμ ht
  have hmt_le_t : μ * t ≤ t := mul_le_of_le_one_left ht.le hμ1
  -- every point of the segment lies in `[μ t, 3/4]`
  have hseg : ∀ u ∈ Set.uIcc r t, μ * t ≤ u ∧ u ≤ 3 / 4 := by
    intro u hu
    rw [Set.mem_uIcc] at hu
    rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨le_trans hr h1, le_trans h2 ht34⟩
    · exact ⟨le_trans hmt_le_t h1, le_trans h2 hr34⟩
  have hdiff : ∀ u ∈ Set.uIcc r t, DifferentiableAt ℝ (gradKernelH s) u := by
    intro u hu
    obtain ⟨h1, h2⟩ := hseg u hu
    have hu0 : 0 < u := lt_of_lt_of_le hmt h1
    have hx : (u : UnitAddCircle) ≠ 0 := gradSplit_coe_ne_zero (by rw [abs_of_pos hu0]; exact hu0)
      (by rw [abs_of_pos hu0]; linarith)
    rw [gradKernelH_eq]
    exact differentiableAt_id.mul
      (gradSplit_hasDerivAt_iteratedDeriv s hs0 hs1 1 hx).differentiableAt
  have hbd : ∀ u ∈ Set.uIcc r t, ‖deriv (gradKernelH s) u‖ ≤ C₁ * (μ * t) ^ (-s - 1) := by
    intro u hu
    obtain ⟨h1, h2⟩ := hseg u hu
    have hu0 : 0 < u := lt_of_lt_of_le hmt h1
    rw [Real.norm_eq_abs, ← iteratedDeriv_one]
    calc |iteratedDeriv 1 (gradKernelH s) u| ≤ C₁ * u ^ (-s - 1) := hC₁ u hu0 h2
      _ ≤ C₁ * (μ * t) ^ (-s - 1) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hmt h1 (by linarith)) hC₀
  have key := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbd (convex_uIcc r t)
    Set.left_mem_uIcc Set.right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at key
  rw [abs_sub_comm (gradKernelH s r) (gradKernelH s t), abs_sub_comm r t]
  exact key

/-- The mean value bound for `h` with both endpoints of the same nonzero sign. -/
lemma gradKernel_sub_le_sign {s C₁ μ t r : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hC₀ : 0 ≤ C₁)
    (hC₁ : ∀ u : ℝ, 0 < u → u ≤ 3 / 4 → |iteratedDeriv 1 (gradKernelH s) u| ≤ C₁ * u ^ (-s - 1))
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hrt : 0 < r * t) (hμr : μ * |t| ≤ |r|) (ht34 : |t| ≤ 3 / 4)
    (hr34 : |r| ≤ 3 / 4) :
    |gradKernelH s r - gradKernelH s t| ≤ C₁ * (μ * |t|) ^ (-s - 1) * |r - t| := by
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, mul_zero] at hrt
    exact lt_irrefl _ hrt
  rcases lt_or_gt_of_ne ht0 with htn | htp
  · -- both points negative: use the evenness `h(-x) = h(x)` and the positive case at `-r, -t`
    have hrn : r < 0 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    have h1 := gradKernel_sub_le_pos hs0 hs1 hC₀ hC₁ hμ hμ1 (t := -t) (r := -r)
      (by linarith) (by rw [abs_of_neg htn] at ht34; linarith)
      (by rw [abs_of_neg htn, abs_of_neg hrn] at hμr; linarith)
      (by rw [abs_of_neg hrn] at hr34; linarith)
    rw [gradSplit_gradKernelH_even s r, gradSplit_gradKernelH_even s t] at h1
    have e3 : |-r - -t| = |r - t| := by
      rw [show -r - -t = -(r - t) by ring, abs_neg]
    rw [e3] at h1
    rw [abs_of_neg htn]
    have e4 : μ * -t = μ * -t := rfl
    rw [e4] at h1
    exact h1
  · have hrp : 0 < r := by
      by_contra hcon
      push Not at hcon
      nlinarith
    rw [abs_of_pos htp] at hμr ht34 ⊢
    rw [abs_of_pos hrp] at hμr hr34
    exact gradKernel_sub_le_pos hs0 hs1 hC₀ hC₁ hμ hμ1 htp ht34 hμr hr34

end

end Riesz1
