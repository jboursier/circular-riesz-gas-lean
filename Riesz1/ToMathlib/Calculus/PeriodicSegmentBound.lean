/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Ring.Periodic

/-!
# Increments of a periodic function over a short segment

Let `f` be a real `C¹` function of period `L > 0`, and let `g` be antitone on `[0, ∞)`.
Suppose that `|f'(x)| ≤ g |x|` on the half period `[-L/2, L/2]`. Then a point `u` of
`[-L/2, L/2]` and a step `0 ≤ h ≤ L` satisfy

`|f u - f (u - h)| ≤ h g (max (|u| - h) 0)`.

The point is that the bound on the derivative is only assumed on one period. Every point `x` of
the segment `[u - h, u]` is moved, by a period if needed, into `[-L/2, L/2]`. The moved point stays
at distance at least `|u| - h` from the origin, so the antitone majorant applies there. This is
the step that moves each window particle to its circle distance from the origin, in Lemma 5.2.
-/

@[expose] public section

open Set

namespace Riesz1

/-- **Segment increment of a periodic function.** See the module documentation. -/
theorem abs_sub_le_of_periodic_deriv_bound {L : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hper : Function.Periodic f L) {g : ℝ → ℝ}
    (hg : AntitoneOn g (Ici 0))
    (hder : ∀ x ∈ Icc (-(L / 2)) (L / 2), |deriv f x| ≤ g |x|)
    {u h : ℝ} (hu : |u| ≤ L / 2) (hh0 : 0 ≤ h) (hhL : h ≤ L) :
    |f u - f (u - h)| ≤ h * g (max (|u| - h) 0) := by
  set m : ℝ := max (|u| - h) 0 with hm_def
  have hm0 : 0 ≤ m := le_max_right _ _
  have hu_le : u ≤ L / 2 := (le_abs_self u).trans hu
  have hu_ge : -(L / 2) ≤ u := by linarith [neg_abs_le u]
  -- The derivative is `L`-periodic.
  have hdper : ∀ x, deriv f (x + L) = deriv f x := by
    intro x
    have h1 : deriv (fun y => f (y + L)) x = deriv f (x + L) := deriv_comp_add_const f L x
    have h2 : (fun y => f (y + L)) = f := funext hper
    rw [h2] at h1
    exact h1.symm
  -- The bound of the derivative on the whole segment `[u - h, u]`.
  have hbound : ∀ x ∈ Icc (u - h) u, |deriv f x| ≤ g m := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    -- The reduced point `xb` lies in `[-L/2, L/2]`, has the same derivative and `|xb| ≥ m`.
    obtain ⟨xb, hxb_mem, hxb_eq, hxb_m⟩ :
        ∃ xb ∈ Icc (-(L / 2)) (L / 2), deriv f xb = deriv f x ∧ m ≤ |xb| := by
      by_cases hx' : -(L / 2) ≤ x
      · refine ⟨x, ⟨hx', by linarith⟩, rfl, max_le ?_ (abs_nonneg x)⟩
        have : |u| - |x| ≤ |u - x| := abs_sub_abs_le_abs_sub u x
        have hux : |u - x| = u - x := abs_of_nonneg (by linarith)
        linarith
      · have hx'' : x < -(L / 2) := not_le.mp hx'
        refine ⟨x + L, ⟨by linarith, by linarith⟩, hdper x, ?_⟩
        have hxL : |u| - h ≤ x + L := by linarith [hu, hu_ge]
        exact max_le (hxL.trans (le_abs_self _)) (abs_nonneg _)
    rw [← hxb_eq]
    calc |deriv f xb| ≤ g |xb| := hder xb hxb_mem
      _ ≤ g m := hg (mem_Ici.2 hm0) (mem_Ici.2 (abs_nonneg xb)) hxb_m
  -- Mean value inequality on the segment.
  have hdiff : ∀ x ∈ Icc (u - h) u, HasDerivWithinAt f (deriv f x) (Icc (u - h) u) x := by
    intro x _
    exact ((hf.differentiable one_ne_zero) x).hasDerivAt.hasDerivWithinAt
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (a := u - h) (b := u)
    (f' := deriv f) hdiff
    (fun x hx => by
      rw [Real.norm_eq_abs]
      exact hbound x (Ico_subset_Icc_self hx))
  have hu' : u ∈ Icc (u - h) u := ⟨by linarith, le_rfl⟩
  have := hmvt u hu'
  rw [Real.norm_eq_abs, show u - (u - h) = h by ring] at this
  exact this.trans_eq (mul_comm _ _)
end Riesz1
