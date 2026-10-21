/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.DerivativeBounds

/-!
# Kernel derivatives for the gradient splitting

The kernel part of Lemma 5.7. Here `g = hurwitzKernel s` is
the periodic Riesz kernel, and `h(r) = r g'(r)` is the modified kernel
`g̃`, given by `gradKernelH`.

The derivative bounds hold on `0 < |r| ≤ 3/4`. The parity facts and the values at `1/2` are
stated on the non-integers, where `h` is the object of the paper.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The modified kernel `h(r) = r g'(r)`, for `g = hurwitzKernel s`.
On the non-integers this is exactly the object of the paper. At an integer the value is the formula
evaluated with Mathlib's `deriv`. No statement of this file uses that value. -/
noncomputable def gradKernelH (s r : ℝ) : ℝ := r * deriv (hurwitzKernel s) r

/-- The non-integers form an open subset of `ℝ`. -/
lemma gradSplit_isOpen_nonInt : IsOpen {r : ℝ | (r : UnitAddCircle) ≠ 0} :=
  IsOpen.preimage (f := fun r : ℝ => (r : UnitAddCircle)) continuous_quotient_mk'
    isOpen_compl_singleton

/-- A real number of modulus strictly between `0` and `1` is not an integer. -/
lemma gradSplit_coe_ne_zero {r : ℝ} (h0 : 0 < |r|) (h1 : |r| < 1) : (r : UnitAddCircle) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h
  rw [zsmul_eq_mul, mul_one] at hn
  have hn1 : |(n : ℝ)| < 1 := by rw [hn]; exact h1
  have hn2 : |n| < 1 := by exact_mod_cast hn1
  have hn0 : n = 0 := by
    have := abs_lt.mp hn2
    omega
  have hr : r = 0 := by rw [← hn, hn0]; simp
  rw [hr, abs_zero] at h0
  exact lt_irrefl _ h0

/-- For `|r| ≤ 3/4`, the distance from `r` to the integers is at least `|r|/3`. -/
lemma gradSplit_abs_div_three_le_dist {r : ℝ} (hr : |r| ≤ 3 / 4) :
    |r| / 3 ≤ dist (r : UnitAddCircle) 0 := by
  rw [dist_zero_right, UnitAddCircle.norm_eq]
  have hround : |r - round r| ≤ 1 / 2 := abs_sub_round r
  have hr' := abs_le.mp hr
  have hround' := abs_le.mp hround
  have hn_hi : (round r : ℝ) < 2 := by linarith [hround'.1]
  have hn_lo : (-2 : ℝ) < round r := by linarith [hround'.2]
  have hn_hi' : round r < 2 := by exact_mod_cast hn_hi
  have hn_lo' : -2 < round r := by exact_mod_cast hn_lo
  have habs := abs_nonneg r
  rcases (show round r = -1 ∨ round r = 0 ∨ round r = 1 by omega) with h | h | h <;>
    rw [h] <;> push_cast
  · rw [abs_of_nonneg (show (0 : ℝ) ≤ r - -1 by linarith)]
    linarith
  · rw [sub_zero]
    linarith
  · rw [abs_of_neg (show r - 1 < 0 by linarith)]
    linarith

/-- A single derivative order of the kernel, on `0 < |r| ≤ 3/4`. -/
lemma gradSplit_iteratedDeriv_kernel_le (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < |r| → |r| ≤ 3 / 4 →
      |iteratedDeriv m (hurwitzKernel s) r| ≤ C * |r| ^ (-s - (m : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := iteratedDeriv_hurwitzKernel_bound s hs0 hs1 m
  refine ⟨C * 3 ^ (s + (m : ℝ)), by positivity, fun r hr0 hr1 => ?_⟩
  have hne : (r : UnitAddCircle) ≠ 0 := gradSplit_coe_ne_zero hr0 (by linarith)
  have hpos : 0 < |r| / 3 := by positivity
  have hle : dist (r : UnitAddCircle) 0 ^ (-s - (m : ℝ)) ≤ (|r| / 3) ^ (-s - (m : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hpos (gradSplit_abs_div_three_le_dist hr1) (by linarith)
  have hinv : (3 : ℝ) ^ (s + (m : ℝ)) = ((3 : ℝ) ^ (-s - (m : ℝ)))⁻¹ := by
    rw [show -s - (m : ℝ) = -(s + (m : ℝ)) by ring, Real.rpow_neg (by norm_num), inv_inv]
  have hscale : (|r| / 3) ^ (-s - (m : ℝ)) = 3 ^ (s + (m : ℝ)) * |r| ^ (-s - (m : ℝ)) := by
    rw [Real.div_rpow (abs_nonneg r) (by norm_num), hinv, div_eq_mul_inv, mul_comm]
  calc |iteratedDeriv m (hurwitzKernel s) r|
      ≤ C * dist (r : UnitAddCircle) 0 ^ (-s - (m : ℝ)) := hb r hne
    _ ≤ C * (|r| / 3) ^ (-s - (m : ℝ)) := mul_le_mul_of_nonneg_left hle hC.le
    _ = C * 3 ^ (s + (m : ℝ)) * |r| ^ (-s - (m : ℝ)) := by rw [hscale]; ring

/-- Derivative orders one to three of the kernel, on `0 < |r| ≤ 3/4`, with one constant. -/
lemma gradSplit_kernel_deriv_bound (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < |r| → |r| ≤ 3 / 4 →
      ∀ m : ℕ, 1 ≤ m → m ≤ 3 →
        |iteratedDeriv m (hurwitzKernel s) r| ≤ C * |r| ^ (-s - (m : ℝ)) := by
  obtain ⟨C1, hC1, h1⟩ := gradSplit_iteratedDeriv_kernel_le s hs0 hs1 1
  obtain ⟨C2, hC2, h2⟩ := gradSplit_iteratedDeriv_kernel_le s hs0 hs1 2
  obtain ⟨C3, hC3, h3⟩ := gradSplit_iteratedDeriv_kernel_le s hs0 hs1 3
  refine ⟨C1 + C2 + C3, by positivity, fun r hr0 hr1 m hm1 hm3 => ?_⟩
  have hpow : 0 ≤ |r| ^ (-s - (m : ℝ)) := Real.rpow_nonneg (abs_nonneg r) _
  interval_cases m
  · exact (h1 r hr0 hr1).trans (mul_le_mul_of_nonneg_right (by linarith) hpow)
  · exact (h2 r hr0 hr1).trans (mul_le_mul_of_nonneg_right (by linarith) hpow)
  · exact (h3 r hr0 hr1).trans (mul_le_mul_of_nonneg_right (by linarith) hpow)

/-- The kernel is smooth on the non-integers. -/
lemma gradSplit_contDiffOn_kernel (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ContDiffOn ℝ ∞ (hurwitzKernel s) {r : ℝ | (r : UnitAddCircle) ≠ 0} := by
  exact (contDiffOn_const (c := (2 : ℝ))).mul (contDiffOn_hurwitzZetaEven_re s hs0 hs1)

/-- Every iterated derivative of the kernel is smooth on the non-integers. -/
lemma gradSplit_contDiffOn_iteratedDeriv (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (k : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv k (hurwitzKernel s)) {r : ℝ | (r : UnitAddCircle) ≠ 0} := by
  induction k with
  | zero => rw [iteratedDeriv_zero]; exact gradSplit_contDiffOn_kernel s hs0 hs1
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen gradSplit_isOpen_nonInt (by simp)

/-- The derivative of the `k`-th iterated derivative is the next iterated derivative, at every
non-integer. -/
lemma gradSplit_hasDerivAt_iteratedDeriv (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (k : ℕ)
    {x : ℝ} (hx : (x : UnitAddCircle) ≠ 0) :
    HasDerivAt (iteratedDeriv k (hurwitzKernel s)) (iteratedDeriv (k + 1) (hurwitzKernel s) x) x := by
  have hdiff : DifferentiableAt ℝ (iteratedDeriv k (hurwitzKernel s)) x :=
    ((gradSplit_contDiffOn_iteratedDeriv s hs0 hs1 k).differentiableOn (by simp)).differentiableAt
      (gradSplit_isOpen_nonInt.mem_nhds hx)
  rw [iteratedDeriv_succ]
  exact hdiff.hasDerivAt

lemma gradKernelH_eq (s : ℝ) :
    gradKernelH s = fun r => r * iteratedDeriv 1 (hurwitzKernel s) r := by
  funext r
  simp [gradKernelH, iteratedDeriv_one]

/-- First derivative of `h` at a non-integer: `h' = g' + r g''`. -/
lemma gradSplit_iteratedDeriv_one_gradKernelH (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) {x : ℝ}
    (hx : (x : UnitAddCircle) ≠ 0) :
    iteratedDeriv 1 (gradKernelH s) x =
      iteratedDeriv 1 (hurwitzKernel s) x + x * iteratedDeriv 2 (hurwitzKernel s) x := by
  have hm : HasDerivAt (fun r => r * iteratedDeriv 1 (hurwitzKernel s) r)
      (1 * iteratedDeriv 1 (hurwitzKernel s) x + x * iteratedDeriv 2 (hurwitzKernel s) x) x :=
    (hasDerivAt_id' x).mul (gradSplit_hasDerivAt_iteratedDeriv s hs0 hs1 1 hx)
  rw [gradKernelH_eq, iteratedDeriv_one, hm.deriv]
  ring

/-- Second derivative of `h` at a non-integer: `h'' = 2 g'' + r g'''`. -/
lemma gradSplit_iteratedDeriv_two_gradKernelH (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) {x : ℝ}
    (hx : (x : UnitAddCircle) ≠ 0) :
    iteratedDeriv 2 (gradKernelH s) x =
      2 * iteratedDeriv 2 (hurwitzKernel s) x + x * iteratedDeriv 3 (hurwitzKernel s) x := by
  have hsucc : iteratedDeriv 2 (gradKernelH s) = deriv (iteratedDeriv 1 (gradKernelH s)) :=
    iteratedDeriv_succ
  have hev : iteratedDeriv 1 (gradKernelH s) =ᶠ[𝓝 x]
      fun r => iteratedDeriv 1 (hurwitzKernel s) r + r * iteratedDeriv 2 (hurwitzKernel s) r :=
    Filter.eventually_of_mem (gradSplit_isOpen_nonInt.mem_nhds hx) fun r hr =>
      gradSplit_iteratedDeriv_one_gradKernelH s hs0 hs1 hr
  have hd : HasDerivAt
      (fun r => iteratedDeriv 1 (hurwitzKernel s) r + r * iteratedDeriv 2 (hurwitzKernel s) r)
      (iteratedDeriv 2 (hurwitzKernel s) x +
        (1 * iteratedDeriv 2 (hurwitzKernel s) x + x * iteratedDeriv 3 (hurwitzKernel s) x)) x :=
    (gradSplit_hasDerivAt_iteratedDeriv s hs0 hs1 1 hx).add
      ((hasDerivAt_id' x).mul (gradSplit_hasDerivAt_iteratedDeriv s hs0 hs1 2 hx))
  rw [hsucc, hev.deriv_eq, hd.deriv]
  ring

/-- Multiplying a power of `|r|` by `|r|` raises its exponent by one. -/
lemma gradSplit_abs_mul_rpow {r : ℝ} (hr : r ≠ 0) (p q : ℝ) (hpq : p + 1 = q) :
    |r| * |r| ^ p = |r| ^ q := by
  rw [← hpq, Real.rpow_add_one (abs_pos.mpr hr).ne', mul_comm]

/-- The kernel is even. -/
lemma gradSplit_kernel_even (s r : ℝ) : hurwitzKernel s (-r) = hurwitzKernel s r := by
  unfold hurwitzKernel
  congr 1
  exact hurwitzZetaEven_re_even (s : ℂ) r

/-- Parity of every iterated derivative of the kernel. -/
lemma gradSplit_iteratedDeriv_kernel_neg (s : ℝ) (m : ℕ) (r : ℝ) :
    iteratedDeriv m (hurwitzKernel s) (-r) =
      (-1 : ℝ) ^ m * iteratedDeriv m (hurwitzKernel s) r := by
  have hfe : (fun z : ℝ => hurwitzKernel s (-z)) = hurwitzKernel s :=
    funext fun z => gradSplit_kernel_even s z
  have h := iteratedDeriv_comp_neg m (hurwitzKernel s) r
  rw [hfe] at h
  rw [h, smul_eq_mul, ← mul_assoc, ← mul_pow]
  norm_num

/-- The modified kernel `h` is even. -/
lemma gradSplit_gradKernelH_even (s r : ℝ) : gradKernelH s (-r) = gradKernelH s r := by
  have h1 := gradSplit_iteratedDeriv_kernel_neg s 1 r
  simp only [iteratedDeriv_one] at h1
  unfold gradKernelH
  rw [h1]
  ring

/-- The derivative of the modified kernel `h` is odd, at every non-integer. -/
lemma gradSplit_iteratedDeriv_one_gradKernelH_neg (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) {r : ℝ}
    (hr : (r : UnitAddCircle) ≠ 0) :
    iteratedDeriv 1 (gradKernelH s) (-r) = -iteratedDeriv 1 (gradKernelH s) r := by
  have hnr : ((-r : ℝ) : UnitAddCircle) ≠ 0 := by
    simpa using neg_ne_zero.mpr hr
  rw [gradSplit_iteratedDeriv_one_gradKernelH s hs0 hs1 hnr,
    gradSplit_iteratedDeriv_one_gradKernelH s hs0 hs1 hr,
    gradSplit_iteratedDeriv_kernel_neg s 1 r, gradSplit_iteratedDeriv_kernel_neg s 2 r]
  ring

/-- The first derivative of the kernel vanishes at `1/2`. -/
lemma gradSplit_deriv_kernel_half (s : ℝ) : deriv (hurwitzKernel s) (1 / 2) = 0 := by
  have hper : deriv (hurwitzKernel s) (-(1 / 2) + 1) = deriv (hurwitzKernel s) (-(1 / 2)) := by
    have h := deriv_comp_add_const (f := hurwitzKernel s) (a := (1 : ℝ)) (x := -(1 / 2))
    have hfun : (fun x => hurwitzKernel s (x + 1)) = hurwitzKernel s :=
      funext fun x => hurwitzKernel_periodic s x
    rw [hfun] at h
    exact h.symm
  have hodd : deriv (hurwitzKernel s) (-(1 / 2)) = -deriv (hurwitzKernel s) (1 / 2) := by
    have h := gradSplit_iteratedDeriv_kernel_neg s 1 (1 / 2)
    simp only [iteratedDeriv_one] at h
    rw [h]
    ring
  have hshift : (-(1 / 2) + 1 : ℝ) = 1 / 2 := by norm_num
  rw [hshift] at hper
  linarith

/-- The derivative of the modified kernel at `1/2` is half the second derivative of the kernel. -/
lemma gradSplit_iteratedDeriv_one_gradKernelH_half (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    iteratedDeriv 1 (gradKernelH s) (1 / 2) = iteratedDeriv 2 (hurwitzKernel s) (1 / 2) / 2 := by
  have hx : ((1 / 2 : ℝ) : UnitAddCircle) ≠ 0 :=
    gradSplit_coe_ne_zero (by norm_num) (by norm_num)
  rw [gradSplit_iteratedDeriv_one_gradKernelH s hs0 hs1 hx, iteratedDeriv_one,
    gradSplit_deriv_kernel_half s]
  ring


/-- Derivative bounds for the kernel `g` and the modified kernel `h`, with one constant. -/
lemma gradSplit_derivative_bounds (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < |r| → |r| ≤ 3 / 4 →
      (∀ m : ℕ, 1 ≤ m → m ≤ 3 →
        |iteratedDeriv m (hurwitzKernel s) r| ≤ C * |r| ^ (-s - (m : ℝ))) ∧
      (∀ m : ℕ, m ≤ 2 → |iteratedDeriv m (gradKernelH s) r| ≤ C * |r| ^ (-s - (m : ℝ))) := by
  obtain ⟨C, hC, hb⟩ := gradSplit_kernel_deriv_bound s hs0 hs1
  refine ⟨3 * C, by positivity, fun r hr0 hr1 => ?_⟩
  have hne : (r : UnitAddCircle) ≠ 0 := gradSplit_coe_ne_zero hr0 (by linarith)
  have hpow : 0 ≤ |r| ^ (-s) := Real.rpow_nonneg (abs_nonneg r) _
  have g1 := hb r hr0 hr1 1 le_rfl (by norm_num)
  have g2 := hb r hr0 hr1 2 (by norm_num) (by norm_num)
  have g3 := hb r hr0 hr1 3 (by norm_num) le_rfl
  simp only [Nat.cast_one] at g1
  simp only [Nat.cast_ofNat] at g2 g3
  refine ⟨fun m hm1 hm3 => (hb r hr0 hr1 m hm1 hm3).trans
    (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (abs_nonneg r) _)), fun m hm => ?_⟩
  interval_cases m
  · simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero]
    rw [iteratedDeriv_one] at g1
    have key := gradSplit_abs_mul_rpow (abs_pos.mp hr0) (-s - 1) (-s) (by ring)
    unfold gradKernelH
    rw [abs_mul]
    calc |r| * |deriv (hurwitzKernel s) r|
        ≤ |r| * (C * |r| ^ (-s - 1)) := mul_le_mul_of_nonneg_left g1 (abs_nonneg r)
      _ = C * |r| ^ (-s) := by linear_combination C * key
      _ ≤ 3 * C * |r| ^ (-s) := by nlinarith [mul_nonneg hC.le hpow]
  · simp only [Nat.cast_one]
    rw [gradSplit_iteratedDeriv_one_gradKernelH s hs0 hs1 hne]
    have key := gradSplit_abs_mul_rpow (abs_pos.mp hr0) (-s - 2) (-s - 1) (by ring)
    have g2' := mul_le_mul_of_nonneg_left g2 (abs_nonneg r)
    calc |iteratedDeriv 1 (hurwitzKernel s) r + r * iteratedDeriv 2 (hurwitzKernel s) r|
        ≤ |iteratedDeriv 1 (hurwitzKernel s) r| + |r * iteratedDeriv 2 (hurwitzKernel s) r| :=
          abs_add_le _ _
      _ ≤ C * |r| ^ (-s - 1) + |r| * (C * |r| ^ (-s - 2)) := by
          rw [abs_mul]
          exact add_le_add g1 g2'
      _ = 2 * C * |r| ^ (-s - 1) := by linear_combination C * key
      _ ≤ 3 * C * |r| ^ (-s - 1) := by nlinarith [mul_nonneg hC.le (Real.rpow_nonneg (abs_nonneg r) (-s - 1))]
  · rw [gradSplit_iteratedDeriv_two_gradKernelH s hs0 hs1 hne]
    have key := gradSplit_abs_mul_rpow (abs_pos.mp hr0) (-s - 3) (-s - 2) (by ring)
    simp only [Nat.cast_ofNat]
    calc |2 * iteratedDeriv 2 (hurwitzKernel s) r + r * iteratedDeriv 3 (hurwitzKernel s) r|
        ≤ |2 * iteratedDeriv 2 (hurwitzKernel s) r| + |r * iteratedDeriv 3 (hurwitzKernel s) r| :=
          abs_add_le _ _
      _ = 2 * |iteratedDeriv 2 (hurwitzKernel s) r| + |r| * |iteratedDeriv 3 (hurwitzKernel s) r| := by
          rw [abs_mul, abs_mul, abs_two]
      _ ≤ 2 * (C * |r| ^ (-s - 2)) + |r| * (C * |r| ^ (-s - 3)) :=
          add_le_add (mul_le_mul_of_nonneg_left g2 zero_le_two) (mul_le_mul_of_nonneg_left g3 (abs_nonneg r))
      _ = 3 * C * |r| ^ (-s - 2) := by linear_combination C * key

/-- The kernel part of Lemma 5.7. For `0 < s < 1`, the kernel `g = hurwitzKernel s`
is even and `1`-periodic. There is one constant `C > 0` such that, for `0 < |r| ≤ 3/4`, the
derivatives of `g` of orders `1` to `3` and the derivatives of `h = gradKernelH s` of orders `0`
to `2` are bounded by `C |r|^{-s-m}`. The modified kernel `h` is even, and `h'` is odd at every
non-integer. Finally `g'(1/2) = 0` and `h'(1/2) = g''(1/2)/2`. -/
theorem gradient_splitting_kernel (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (∀ r : ℝ, hurwitzKernel s (-r) = hurwitzKernel s r) ∧
    Function.Periodic (hurwitzKernel s) 1 ∧
    (∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < |r| → |r| ≤ 3 / 4 →
      (∀ m : ℕ, 1 ≤ m → m ≤ 3 →
        |iteratedDeriv m (hurwitzKernel s) r| ≤ C * |r| ^ (-s - (m : ℝ))) ∧
      (∀ m : ℕ, m ≤ 2 → |iteratedDeriv m (gradKernelH s) r| ≤ C * |r| ^ (-s - (m : ℝ)))) ∧
    (∀ r : ℝ, gradKernelH s (-r) = gradKernelH s r) ∧
    (∀ r : ℝ, (r : UnitAddCircle) ≠ 0 →
      iteratedDeriv 1 (gradKernelH s) (-r) = -iteratedDeriv 1 (gradKernelH s) r) ∧
    deriv (hurwitzKernel s) (1 / 2) = 0 ∧
    iteratedDeriv 1 (gradKernelH s) (1 / 2) = iteratedDeriv 2 (hurwitzKernel s) (1 / 2) / 2 :=
  ⟨gradSplit_kernel_even s, hurwitzKernel_periodic s, gradSplit_derivative_bounds s hs0 hs1,
    gradSplit_gradKernelH_even s,
    fun _ hr => gradSplit_iteratedDeriv_one_gradKernelH_neg s hs0 hs1 hr,
    gradSplit_deriv_kernel_half s, gradSplit_iteratedDeriv_one_gradKernelH_half s hs0 hs1⟩

end Riesz1

end
