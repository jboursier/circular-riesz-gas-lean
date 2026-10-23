/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsDefs
public import Riesz1.ToMathlib.IteratedDerivOpen

/-!
# The microscopic kernel and the cutoff `Q`

Facts about `g_N = loopArcG s N` and about the cutoff `Q = loopArcQ s N`, used by Lemma B.2:

* `g_N` is `N`-periodic and even, `g_N'` is odd, and `g_N'(N/2) = 0`.
* `g_N` is smooth on `(0, N)`, with all iterated derivatives smooth there.
* for `0 < d < N/2`, the cutoff is the integral representation
  `Q(d) = ∫_d^{N/2} (r - d)(-g_N'''(r)) dr + (N/2 - d) g_N''(N/2)` (the elementary identity
  of the proof of Lemma B.2, obtained by integration by parts).

The derivatives are the Mathlib derivatives. The kernel's singularity at the multiples of `N`
lies outside `(0, N)`, where all the smoothness is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- The microscopic kernel `g_N` is `N`-periodic. -/
theorem loopArcG_periodic (s : ℝ) (N : ℕ+) : Function.Periodic (loopArcG s N) (N : ℝ) := by
  intro r
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  unfold loopArcG
  rw [show (r + N) / N = r / N + 1 by rw [add_div, div_self hN], hurwitzKernel_periodic s (r / N)]

/-- The microscopic kernel `g_N` is even. -/
theorem loopArcG_even (s : ℝ) (N : ℕ+) (r : ℝ) : loopArcG s N (-r) = loopArcG s N r := by
  unfold loopArcG
  rw [show -r / (N : ℝ) = -(r / N) by ring, gradSplit_kernel_even]

/-- The derivative of the even function `g_N` is odd. The identity holds at every point, since
`deriv` of a function that is not differentiable is zero on both sides. -/
theorem deriv_loopArcG_neg (s : ℝ) (N : ℕ+) (r : ℝ) :
    deriv (loopArcG s N) (-r) = -deriv (loopArcG s N) r := by
  have h := deriv_comp_neg (f := loopArcG s N) (x := r)
  have hfun : (fun x => loopArcG s N (-x)) = loopArcG s N := funext (loopArcG_even s N)
  rw [hfun] at h
  linarith

/-- The derivative of the microscopic kernel vanishes at the half period `N / 2`, the
endpoint `R` of the cutoff. -/
theorem deriv_loopArcG_half (s : ℝ) (N : ℕ+) : deriv (loopArcG s N) ((N : ℝ) / 2) = 0 := by
  have heven : ∀ y : ℝ, loopArcG s N (-y + (N : ℝ) / 2) = loopArcG s N (y + (N : ℝ) / 2) := by
    intro y
    rw [show -y + (N : ℝ) / 2 = -(y + (N : ℝ) / 2) + N by ring, loopArcG_periodic s N,
      loopArcG_even s N]
  have h0 := deriv_zero_of_even (fun y => loopArcG s N (y + (N : ℝ) / 2)) (fun y => heven y)
  have hshift := deriv_comp_add_const (f := loopArcG s N) (a := (N : ℝ) / 2) (x := 0)
  simp only [zero_add] at hshift
  rw [← hshift]
  exact h0

/-- The microscopic kernel is smooth on `(0, N)`, where the argument `r / N` stays in `(0, 1)`
and so avoids the integers. -/
theorem contDiffOn_loopArcG (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) :
    ContDiffOn ℝ ∞ (loopArcG s N) (Ioo 0 (N : ℝ)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hmaps : MapsTo (fun r : ℝ => r / (N : ℝ)) (Ioo 0 (N : ℝ))
      {r : ℝ | (r : UnitAddCircle) ≠ 0} := by
    intro r hr
    have h0 : 0 < r / (N : ℝ) := div_pos hr.1 hN
    have h1 : r / (N : ℝ) < 1 := (div_lt_one hN).mpr hr.2
    exact gradSplit_coe_ne_zero (by rw [abs_of_pos h0]; exact h0)
      (by rw [abs_of_pos h0]; exact h1)
  unfold loopArcG
  exact contDiffOn_const.mul
    ((gradSplit_contDiffOn_kernel s hs0 hs1).comp (contDiffOn_id.div_const (N : ℝ)) hmaps)

/-- **Integral representation of the cutoff**, the elementary identity of
Lemma B.2. For every `0 < d < N / 2`, integration by parts on `[d, N/2]`
gives `Q(d) = ∫_d^{N/2} (r - d)(-g_N'''(r)) dr + (N/2 - d) g_N''(N/2)`. -/
theorem loopArcQ_eq_integral (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) {d : ℝ}
    (hd0 : 0 < d) (hdR : d < (N : ℝ) / 2) :
    loopArcQ s N d = (∫ r in d..((N : ℝ) / 2), (r - d) * (-iteratedDeriv 3 (loopArcG s N) r))
      + ((N : ℝ) / 2 - d) * iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2) := by
  set f := loopArcG s N with hf_def
  set R : ℝ := (N : ℝ) / 2 with hR_def
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hRN : R < N := by rw [hR_def]; linarith
  have hU : IsOpen (Ioo (0 : ℝ) N) := isOpen_Ioo
  have hfU : ContDiffOn ℝ ∞ f (Ioo 0 (N : ℝ)) := contDiffOn_loopArcG s hs0 hs1 N
  -- Points of `[d, R]` lie in `(0, N)`.
  have hmem : ∀ x ∈ Icc d R, x ∈ Ioo (0 : ℝ) N := fun x hx =>
    ⟨lt_of_lt_of_le hd0 hx.1, lt_of_le_of_lt hx.2 hRN⟩
  have hint_uIcc : uIcc d R = Icc d R := uIcc_of_le hdR.le
  -- Interval integrability of the iterated derivatives on `[d, R]`.
  have hcont (k : ℕ) : ContinuousOn (iteratedDeriv k f) (Icc d R) :=
    ((contDiffOn_iteratedDeriv_open hU hfU k).continuousOn).mono
      (fun x hx => hmem x hx)
  have hint (k : ℕ) : IntervalIntegrable (iteratedDeriv k f) volume d R :=
    (hcont k).intervalIntegrable_of_Icc hdR.le
  -- Integration by parts with `u(r) = r - d` and `v = g_N''`.
  have hibp : ∫ r in d..R, (r - d) * iteratedDeriv 3 f r
      = (R - d) * iteratedDeriv 2 f R - ∫ r in d..R, iteratedDeriv 2 f r := by
    have hu : ∀ x ∈ uIcc d R, HasDerivAt (fun r : ℝ => r - d) 1 x := by
      intro x _
      simpa using (hasDerivAt_id x).sub_const d
    have hv : ∀ x ∈ uIcc d R, HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f x) x := by
      intro x hx
      rw [hint_uIcc] at hx
      have := hasDerivAt_iteratedDeriv_open hU hfU 2 (hmem x hx)
      exact this
    have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
      (by simp) (hint 3)
    simp only [one_mul, sub_self, zero_mul, sub_zero] at key
    exact key
  -- Fundamental theorem of calculus for `g_N'' = (g_N')'` on `[d, R]`.
  have hftc : ∫ r in d..R, iteratedDeriv 2 f r = deriv f R - deriv f d := by
    have hv : ∀ x ∈ uIcc d R, HasDerivAt (iteratedDeriv 1 f) (iteratedDeriv 2 f x) x := by
      intro x hx
      rw [hint_uIcc] at hx
      exact hasDerivAt_iteratedDeriv_open hU hfU 1 (hmem x hx)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hv (hint 2)]
    simp only [iteratedDeriv_one]
  have hRzero : deriv f R = 0 := deriv_loopArcG_half s N
  have hQd : loopArcQ s N d = -deriv f d := by
    have hdR' : d < (N : ℝ) / 2 := hdR
    unfold loopArcQ
    simp only [hdR', ↓reduceIte]
    rfl
  -- The integrand of the representation carries the sign of `-g_N'''`.
  have hneg : ∫ r in d..R, (r - d) * (-iteratedDeriv 3 f r)
      = -∫ r in d..R, (r - d) * iteratedDeriv 3 f r := by
    simp only [mul_neg, intervalIntegral.integral_neg]
  -- Assemble the representation.
  rw [hneg, hibp, hftc, hRzero, hQd]
  ring

end Riesz1

end
end
