/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingDisplacementPair

/-!
# Kernel increments for the gap representative

The gap part of Lemma 5.7. The gap representative `W^gap` pairs the derivative `h'` of the
modified kernel `h = gradKernelH s` at the lift
separation `r` with its value at the lattice increment `κ/N`. This file bounds that difference on an
admissible pair: for `0 < κ`, with `K = Nℓ` and `λ = K^ε`,

`N^{-1-s} |h'(r) - h'(κ/N)| ≤ C K^{(s+3)ε} κ^{-2-s/2}`.

The proof is the mean value inequality for `h'` on the segment from `κ/N` to `r`, whose derivative
`h'' = iteratedDeriv 2 (gradKernelH s)` is bounded by `gradient_splitting_kernel` on `(0, 3/4]`. The
segment stays above `K^{-ε} κ / N`, and `|r - κ/N| ≤ K^ε κ^{s/2} / N` by the event.
-/

@[expose] public section

namespace Riesz1

open Filter Topology

noncomputable section

/-- The derivative `h'` of the modified kernel has derivative `h''` at every non-integer point. -/
lemma gapKernel_hasDerivAt_deriv (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) {x : ℝ}
    (hx : (x : UnitAddCircle) ≠ 0) :
    HasDerivAt (iteratedDeriv 1 (gradKernelH s)) (iteratedDeriv 2 (gradKernelH s) x) x := by
  have hd : HasDerivAt
      (fun r => iteratedDeriv 1 (hurwitzKernel s) r + r * iteratedDeriv 2 (hurwitzKernel s) r)
      (iteratedDeriv 2 (hurwitzKernel s) x +
        (1 * iteratedDeriv 2 (hurwitzKernel s) x + x * iteratedDeriv 3 (hurwitzKernel s) x)) x :=
    (gradSplit_hasDerivAt_iteratedDeriv s hs0 hs1 1 hx).add
      ((hasDerivAt_id' x).mul (gradSplit_hasDerivAt_iteratedDeriv s hs0 hs1 2 hx))
  have hev : iteratedDeriv 1 (gradKernelH s) =ᶠ[𝓝 x]
      fun r => iteratedDeriv 1 (hurwitzKernel s) r + r * iteratedDeriv 2 (hurwitzKernel s) r :=
    Filter.eventually_of_mem (gradSplit_isOpen_nonInt.mem_nhds hx) fun r hr =>
      gradSplit_iteratedDeriv_one_gradKernelH s hs0 hs1 hr
  have h2 := gradSplit_iteratedDeriv_two_gradKernelH s hs0 hs1 hx
  refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [h2]
  ring

/-- The mean value bound for `h'` on the positive axis: if `μ t ≤ r`, `0 < μ ≤ 1`, and
`0 < t, r ≤ 3/4`, then `|h'(r) - h'(t)| ≤ C (μ t)^{-s-2} |r - t|`, where `C` bounds `h''` on
`(0, 3/4]`. -/
lemma gapKernel_deriv_sub_le_pos {s C₁ μ t r : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hC₀ : 0 ≤ C₁)
    (hC₁ : ∀ u : ℝ, 0 < u → u ≤ 3 / 4 → |iteratedDeriv 2 (gradKernelH s) u| ≤ C₁ * u ^ (-s - 2))
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (ht : 0 < t) (ht34 : t ≤ 3 / 4) (hr : μ * t ≤ r)
    (hr34 : r ≤ 3 / 4) :
    |iteratedDeriv 1 (gradKernelH s) r - iteratedDeriv 1 (gradKernelH s) t|
      ≤ C₁ * (μ * t) ^ (-s - 2) * |r - t| := by
  have hmt : 0 < μ * t := mul_pos hμ ht
  have hmt_le_t : μ * t ≤ t := mul_le_of_le_one_left ht.le hμ1
  -- every point of the segment lies in `[μ t, 3/4]`
  have hseg : ∀ u ∈ Set.uIcc r t, μ * t ≤ u ∧ u ≤ 3 / 4 := by
    intro u hu
    rw [Set.mem_uIcc] at hu
    rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨le_trans hr h1, le_trans h2 ht34⟩
    · exact ⟨le_trans hmt_le_t h1, le_trans h2 hr34⟩
  have hnon : ∀ u ∈ Set.uIcc r t, (u : UnitAddCircle) ≠ 0 := by
    intro u hu
    obtain ⟨h1, h2⟩ := hseg u hu
    have hu0 : 0 < u := lt_of_lt_of_le hmt h1
    exact gradSplit_coe_ne_zero (by rw [abs_of_pos hu0]; exact hu0)
      (by rw [abs_of_pos hu0]; linarith)
  have hdiff : ∀ u ∈ Set.uIcc r t, DifferentiableAt ℝ (iteratedDeriv 1 (gradKernelH s)) u :=
    fun u hu => (gapKernel_hasDerivAt_deriv s hs0 hs1 (hnon u hu)).differentiableAt
  have hbd : ∀ u ∈ Set.uIcc r t,
      ‖deriv (iteratedDeriv 1 (gradKernelH s)) u‖ ≤ C₁ * (μ * t) ^ (-s - 2) := by
    intro u hu
    obtain ⟨h1, h2⟩ := hseg u hu
    have hu0 : 0 < u := lt_of_lt_of_le hmt h1
    rw [Real.norm_eq_abs, (gapKernel_hasDerivAt_deriv s hs0 hs1 (hnon u hu)).deriv]
    calc |iteratedDeriv 2 (gradKernelH s) u| ≤ C₁ * u ^ (-s - 2) := hC₁ u hu0 h2
      _ ≤ C₁ * (μ * t) ^ (-s - 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hmt h1 (by linarith)) hC₀
  have key := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbd (convex_uIcc r t)
    Set.left_mem_uIcc Set.right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at key
  rw [abs_sub_comm (iteratedDeriv 1 (gradKernelH s) r) (iteratedDeriv 1 (gradKernelH s) t),
    abs_sub_comm r t]
  exact key

/-- The rpow identity `(K^{-ε} t)^{-s-2} = (K^ε)^{s+2} t^{-s-2}` for `t = κ/N`. -/
lemma gapKernel_rpow_spacing {s ε K κ N : ℝ} (hK0 : 0 < K) (hκ : 0 < κ) (hN : 0 < N) :
    (K ^ (-ε) * (κ / N)) ^ (-s - 2) = (K ^ ε) ^ (s + 2) * κ ^ (-s - 2) * N ^ (s + 2) := by
  have ha : (K ^ (-ε)) ^ (-s - 2) = (K ^ ε) ^ (s + 2) := by
    rw [← Real.rpow_mul hK0.le, ← Real.rpow_mul hK0.le]
    congr 1
    ring
  have hb : (κ / N) ^ (-s - 2) = κ ^ (-s - 2) * N ^ (s + 2) := by
    rw [Real.div_rpow hκ.le hN.le, div_eq_mul_inv, ← Real.rpow_neg hN.le,
      show -(-s - 2) = s + 2 by ring]
  rw [Real.mul_rpow (Real.rpow_nonneg hK0.le _) (div_nonneg hκ.le hN.le), ha, hb]
  ring

/-- The kernel increment of `h'` on one admissible pair (gap part of Lemma 5.7).
Let `0 < κ` be the increment of a positive path, `2κ ≤ N`, and let `D` be the lift separation with
`K^{-ε} κ ≤ N D` and `|N D - κ| ≤ K^ε κ^{s/2}`. Then the threshold `N₀ = 4^{2/(1-s/2)}` gives the
bound `D ≤ 3/4` (for `N ≥ N₀` from the event, and below `N₀` by the hypothesis `hD34`), and the mean
value inequality yields `N^{-1-s} |h'(D) - h'(κ/N)| ≤ C K^{(s+3)ε} κ^{-2-s/2}`. -/
lemma gapKernel_deriv_pair_bound {s C₁ K N κ D ε : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hC₀ : 0 ≤ C₁)
    (hC_der : ∀ u : ℝ, 0 < u → u ≤ 3 / 4 → |iteratedDeriv 2 (gradKernelH s) u| ≤ C₁ * u ^ (-s - 2))
    (hK1 : 1 ≤ K) (hKN : K ≤ N) (hε : 0 < ε) (hεs : ε < (1 - s / 2) / 8) (hN : 0 < N)
    (hκ : 0 < κ) (hκN : 2 * κ ≤ N) (hF2a : K ^ (-ε) * κ ≤ N * D)
    (hF1 : |N * D - κ| ≤ K ^ ε * κ ^ (s / 2))
    (hD34 : N < (4 : ℝ) ^ (2 / (1 - s / 2)) → D ≤ 3 / 4) :
    N ^ (-1 - s) * |iteratedDeriv 1 (gradKernelH s) D - iteratedDeriv 1 (gradKernelH s) (κ / N)|
      ≤ C₁ * K ^ ((s + 3) * ε) * κ ^ (-2 - s / 2) := by
  have hK0 : 0 < K := by linarith
  have hμ : 0 < K ^ (-ε) := Real.rpow_pos_of_pos hK0 _
  have hμ1 : K ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hK1 (by linarith)
  have ht0 : 0 < κ / N := div_pos hκ hN
  have ht34 : κ / N ≤ 3 / 4 := by
    rw [div_le_iff₀ hN]
    linarith
  -- Step 1: the endpoint `D` lies in `(0, 3/4]`
  have hD : D ≤ 3 / 4 := by
    by_cases hNN : (4 : ℝ) ^ (2 / (1 - s / 2)) ≤ N
    · have h4 := four_le_rpow_of_threshold hs1 hε hεs hNN
      have hKε : K ^ ε ≤ N ^ ε := Real.rpow_le_rpow hK0.le hKN hε.le
      have hκs : κ ^ (s / 2) ≤ N ^ (s / 2) := Real.rpow_le_rpow hκ.le (by linarith) (by linarith)
      have hprod : K ^ ε * κ ^ (s / 2) ≤ N ^ (ε + s / 2) := by
        rw [Real.rpow_add hN]
        exact mul_le_mul hKε hκs (Real.rpow_nonneg hκ.le _) (Real.rpow_nonneg hN.le _)
      have hxx : N ^ (ε + s / 2) * N ^ (1 - ε - s / 2) = N := by
        rw [← Real.rpow_add hN, show ε + s / 2 + (1 - ε - s / 2) = 1 by ring, Real.rpow_one]
      have hx4 : N ^ (ε + s / 2) * 4 ≤ N := by
        calc N ^ (ε + s / 2) * 4 ≤ N ^ (ε + s / 2) * N ^ (1 - ε - s / 2) :=
              mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hN.le _)
          _ = N := hxx
      have hN34 : N * D ≤ N * (3 / 4) := by
        have h1 := (abs_le.mp hF1).2
        linarith
      exact le_of_mul_le_mul_left hN34 hN
    · exact hD34 (not_le.mp hNN)
  -- Step 2: the lower spacing bound `K^{-ε} κ/N ≤ D`
  have hlow : K ^ (-ε) * (κ / N) ≤ D := by
    rw [← mul_div_assoc, div_le_iff₀ hN]
    linarith
  -- Step 3: the mean value inequality for `h'` and the distance `|D - κ/N|`
  have hmv := gapKernel_deriv_sub_le_pos hs0 hs1 hC₀ hC_der hμ hμ1 ht0 ht34 hlow hD
  have hdist : |D - κ / N| ≤ K ^ ε * κ ^ (s / 2) / N := by
    have h : D - κ / N = (N * D - κ) / N := by
      field_simp
    rw [h, abs_div, abs_of_pos hN]
    exact div_le_div_of_nonneg_right hF1 hN.le
  rw [gapKernel_rpow_spacing hK0 hκ hN] at hmv
  -- Step 4: collect the powers of `K`, `κ` and `N`
  have e1 : (K ^ ε) ^ (s + 2) * K ^ ε = K ^ ((s + 3) * ε) := by
    rw [← Real.rpow_mul hK0.le, ← Real.rpow_add hK0]
    congr 1
    ring
  have e2 : κ ^ (-s - 2) * κ ^ (s / 2) = κ ^ (-2 - s / 2) := by
    rw [← Real.rpow_add hκ]
    congr 1
    ring
  have e3 : N ^ (-1 - s) * N ^ (s + 2) * N⁻¹ = 1 := by
    rw [← Real.rpow_add hN, show -1 - s + (s + 2) = 1 by ring, Real.rpow_one,
      mul_inv_cancel₀ hN.ne']
  calc N ^ (-1 - s) * |iteratedDeriv 1 (gradKernelH s) D - iteratedDeriv 1 (gradKernelH s) (κ / N)|
      ≤ N ^ (-1 - s) * (C₁ * ((K ^ ε) ^ (s + 2) * κ ^ (-s - 2) * N ^ (s + 2)) *
          (K ^ ε * κ ^ (s / 2) / N)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hN.le _)
        exact hmv.trans (mul_le_mul_of_nonneg_left hdist (by positivity))
    _ = C₁ * ((K ^ ε) ^ (s + 2) * K ^ ε) * (κ ^ (-s - 2) * κ ^ (s / 2)) *
          (N ^ (-1 - s) * N ^ (s + 2) * N⁻¹) := by
        ring
    _ = C₁ * K ^ ((s + 3) * ε) * κ ^ (-2 - s / 2) := by
        rw [e1, e2, e3, mul_one]

end

end Riesz1
