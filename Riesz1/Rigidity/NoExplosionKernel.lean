/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.Derivatives

/-!
# Removing a singular pair interaction

Kernel inputs to Lemma 4.5: removing the
singularity at zero preserves convexity, and removing both endpoint
singularities leaves a bounded remainder on the unit interval.
-/

public section

noncomputable section

open Filter Topology Set

namespace Riesz1

/-- Removing the zero-endpoint singularity leaves a convex function. -/
theorem convexOn_hurwitzKernel_sub_rpow (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ConvexOn ℝ (Ioo (0 : ℝ) 1) (fun x => hurwitzKernel s x - x ^ (-s)) := by
  let d : ℝ → ℝ := fun x => deriv (hurwitzKernel s) x - (-s * x ^ (-s - 1))
  let dd : ℝ → ℝ := fun x => s * (s + 1) *
    ((∑' k : ℤ, |x - k| ^ (-s - 2)) - x ^ (-s - 2))
  have hd (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun x => hurwitzKernel s x - x ^ (-s)) (d x) x := by
    have hne := coe_ne_zero_of_mem_Ioo_int 0 x (by simpa using hx)
    exact (differentiableAt_hurwitzKernel_of_ne s hs hs1 x hne).hasDerivAt.sub
      (Real.hasDerivAt_rpow_const (p := -s) (Or.inl hx.1.ne'))
  have hdd (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt d (dd x) x := by
    have hne := coe_ne_zero_of_mem_Ioo_int 0 x (by simpa using hx)
    have hp := (Real.hasDerivAt_rpow_const (p := -s - 1) (Or.inl hx.1.ne')).const_mul (-s)
    convert (hasDerivAt_deriv_hurwitzKernel s hs hs1 x hne).sub hp using 1
    dsimp [dd]
    rw [show -s - 1 - 1 = -s - 2 by ring]
    ring
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioo _ _)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (by simpa using hx)).hasDerivWithinAt)
    (fun x hx => (hdd x (by simpa using hx)).hasDerivWithinAt) ?_
  intro x hx
  rw [interior_Ioo] at hx
  have hne := coe_ne_zero_of_mem_Ioo_int 0 x (by simpa using hx)
  have hsum := summable_abs_sub_rpow_of_ne s hs x hne
  have hle := hsum.le_tsum (0 : ℤ) (fun k _ => Real.rpow_nonneg (abs_nonneg (x - k)) _)
  simp only [Int.cast_zero, sub_zero, abs_of_pos hx.1] at hle
  exact mul_nonneg (mul_nonneg hs.le (by linarith)) (sub_nonneg.mpr hle)

/-- Both endpoint singularities can be removed with a uniformly bounded remainder. -/
theorem exists_hurwitzKernel_endpoint_remainder_bound (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ioo (0 : ℝ) 1,
      |hurwitzKernel s x - x ^ (-s) - (1 - x) ^ (-s)| ≤ C := by
  let Q : ℝ → ℝ := fun x => (∑' n, eulerTermC s (x : ℂ) n).re
  have hQ : ContinuousOn Q (Icc (0 : ℝ) 1) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_tsum_eulerTerm s hs hs1)
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hQ).isBounded.subset_closedBall (0 : ℝ)
  refine ⟨2 * C + |2 / (1 - s)|, ?_, ?_⟩
  · have h0 := hC (mem_image_of_mem Q (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num))
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h0
    linarith [abs_nonneg (Q 0), abs_nonneg (2 / (1 - s))]
  · intro x hx
    have hxQ := hC (mem_image_of_mem Q (show x ∈ Icc (0 : ℝ) 1 from ⟨hx.1.le, hx.2.le⟩))
    have hxQ' := hC (mem_image_of_mem Q
      (show 1 - x ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hx.1, hx.2]))
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hxQ hxQ'
    have he := hurwitzZetaEven_re_euler s hs hs1 x hx.1 hx.2
    change hurwitzKernel s x = x ^ (-s) + (1 - x) ^ (-s) + Q x + Q (1 - x) -
      2 / (1 - s) at he
    rw [he]
    have hid : x ^ (-s) + (1 - x) ^ (-s) + Q x + Q (1 - x) - 2 / (1 - s) -
        x ^ (-s) - (1 - x) ^ (-s) = (Q x + Q (1 - x)) - 2 / (1 - s) := by ring
    rw [hid]
    exact (abs_sub _ _).trans (by linarith [abs_add_le (Q x) (Q (1 - x))])

end Riesz1

end
