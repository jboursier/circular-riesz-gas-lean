/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.Regularity
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Analysis.PSeries

/-!
# Second derivative of the Hurwitz kernel

For `0 < s < 1` the kernel `g x = 2 * Re (hurwitzZetaEven x s)` is twice
differentiable off the integers. Its second derivative is the positive series
`s (s + 1) ∑ₖ |x - k| ^ (-s - 2)`. The proof differentiates the unit-interval Euler
representation of `Regularity.lean` on `(0,1)`, where the derivatives of the Euler remainder are
the series `∑ₙ (n + 1 + w) ^ (-a)`, and transports the result to every non-integer point by
periodicity. Convexity on each open unit interval follows from the positive second derivative.

Lemma 2.1, derivative claims.
-/

public section

open Filter Topology MeasureTheory Set Complex
open scoped ContDiff
namespace Riesz1

/-- The project kernel `g s x = 2 * Re (hurwitzZetaEven x s)`, as a function of a
real variable. -/
@[expose] noncomputable def hurwitzKernel (s x : ℝ) : ℝ :=
  2 * (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (s : ℂ)).re

/-- The series `∑ₙ (n + 1 + w) ^ (-a)` over `n : ℕ`, the building block of the derivatives of the
Euler remainder `eulerTermC`. -/
@[expose] noncomputable def shiftPowSum (a : ℝ) (w : ℂ) : ℂ :=
  ∑' n : ℕ, ((n : ℂ) + 1 + w) ^ (-(a : ℂ))

lemma norm_shift_cpow_le (a : ℝ) (ha : 0 < a) (n : ℕ) (w : ℂ) (hw : -(1 / 2 : ℝ) < w.re) :
    ‖((n : ℂ) + 1 + w) ^ (-(a : ℂ))‖ ≤ (2 : ℝ) ^ a * ((n : ℝ) + 1) ^ (-a) := by
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  have hre : ((n : ℝ) + 1) / 2 ≤ ‖(n : ℂ) + 1 + w‖ := by
    have h := Complex.re_le_norm ((n : ℂ) + 1 + w)
    simp only [add_re, natCast_re, one_re] at h
    linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [show -(a : ℂ) = ((-a : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]
  calc ‖(n : ℂ) + 1 + w‖ ^ (-a) ≤ (((n : ℝ) + 1) / 2) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hre (by linarith)
    _ = (2 : ℝ) ^ a * ((n : ℝ) + 1) ^ (-a) := by
        rw [Real.div_rpow hpos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          div_inv_eq_mul, mul_comm]

lemma summable_nat_add_one_rpow (a : ℝ) (ha : 1 < a) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-a)) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (show -a < -1 by linarith))
  simpa only [Nat.cast_add, Nat.cast_one] using h

lemma summable_shift_cpow (a : ℝ) (ha : 1 < a) (w : ℂ) (hw : -(1 / 2 : ℝ) < w.re) :
    Summable (fun n : ℕ => ((n : ℂ) + 1 + w) ^ (-(a : ℂ))) :=
  Summable.of_norm_bounded ((summable_nat_add_one_rpow a ha).mul_left _)
    (fun n => norm_shift_cpow_le a (by linarith) n w hw)

lemma hasDerivAt_shift_cpow (a : ℝ) (n : ℕ) (w : ℂ) (hw : -(1 / 2 : ℝ) < w.re) :
    HasDerivAt (fun v : ℂ => ((n : ℂ) + 1 + v) ^ (-(a : ℂ)))
      (-(a : ℂ) * ((n : ℂ) + 1 + w) ^ (-(a : ℂ) - 1)) w := by
  have hslit : (n : ℂ) + 1 + w ∈ slitPlane := by
    apply Or.inl
    simp only [add_re, natCast_re, one_re]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  simpa only [mul_one, id_eq] using
    ((hasDerivAt_id w).const_add ((n : ℂ) + 1)).cpow_const hslit

lemma norm_shift_deriv_le (a : ℝ) (ha : 0 < a) (n : ℕ) (w : ℂ) (hw : -(1 / 2 : ℝ) < w.re) :
    ‖-(a : ℂ) * ((n : ℂ) + 1 + w) ^ (-(a : ℂ) - 1)‖ ≤
      a * ((2 : ℝ) ^ (a + 1) * ((n : ℝ) + 1) ^ (-(a + 1))) := by
  rw [show -(a : ℂ) - 1 = -((a + 1 : ℝ) : ℂ) by push_cast; ring, norm_mul, norm_neg,
    Complex.norm_real, Real.norm_of_nonneg ha.le]
  exact mul_le_mul_of_nonneg_left (norm_shift_cpow_le (a + 1) (by linarith) n w hw) ha.le

lemma tsum_shift_deriv (a : ℝ) (w : ℂ) :
    ∑' n : ℕ, -(a : ℂ) * ((n : ℂ) + 1 + w) ^ (-(a : ℂ) - 1) =
      -(a : ℂ) * shiftPowSum (a + 1) w := by
  unfold shiftPowSum
  rw [tsum_mul_left]
  congr 1
  refine tsum_congr fun n => ?_
  rw [show -(a : ℂ) - 1 = -((a + 1 : ℝ) : ℂ) by push_cast; ring]

lemma hasDerivAt_shiftPowSum (a : ℝ) (ha : 1 < a) (w : ℂ) (hw : -(1 / 2 : ℝ) < w.re) :
    HasDerivAt (shiftPowSum a) (-(a : ℂ) * shiftPowSum (a + 1) w) w := by
  rw [← tsum_shift_deriv a w]
  exact hasDerivAt_tsum_of_isPreconnected
    (g := fun (n : ℕ) (v : ℂ) => ((n : ℂ) + 1 + v) ^ (-(a : ℂ)))
    (g' := fun (n : ℕ) (v : ℂ) => -(a : ℂ) * ((n : ℂ) + 1 + v) ^ (-(a : ℂ) - 1))
    (u := fun n : ℕ => a * ((2 : ℝ) ^ (a + 1) * ((n : ℝ) + 1) ^ (-(a + 1))))
    (t := {v : ℂ | -(1 / 2 : ℝ) < v.re}) (y₀ := w) (y := w)
    (((summable_nat_add_one_rpow (a + 1) (by linarith)).mul_left _).mul_left a)
    (isOpen_lt continuous_const Complex.continuous_re)
    (convex_halfSpace_re_gt _).isPreconnected
    (fun n v hv => hasDerivAt_shift_cpow a n v hv)
    (fun n v hv => norm_shift_deriv_le a (by linarith) n v hv)
    hw (summable_shift_cpow a ha w hw) hw

lemma hasDerivAt_euler_sum (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (w : ℂ)
    (hw : -(1 / 2 : ℝ) < w.re) :
    HasDerivAt (fun v : ℂ => ∑' n : ℕ, eulerTermC s v n)
      (-(s : ℂ) * shiftPowSum (s + 1) w) w := by
  rw [← tsum_shift_deriv s w]
  exact hasDerivAt_tsum_of_isPreconnected
    (g := fun (n : ℕ) (v : ℂ) => eulerTermC s v n)
    (g' := fun (n : ℕ) (v : ℂ) => -(s : ℂ) * ((n : ℂ) + 1 + v) ^ (-(s : ℂ) - 1))
    (u := fun n : ℕ => s * ((2 : ℝ) ^ (s + 1) * ((n : ℝ) + 1) ^ (-(s + 1))))
    (t := {v : ℂ | -(1 / 2 : ℝ) < v.re}) (y₀ := w) (y := w)
    (((summable_nat_add_one_rpow (s + 1) (by linarith)).mul_left _).mul_left s)
    (isOpen_lt continuous_const Complex.continuous_re)
    (convex_halfSpace_re_gt _).isPreconnected
    (fun n v hv => (hasDerivAt_shift_cpow s n v hv).sub_const
      ((((n : ℂ) + 2) ^ (1 - (s : ℂ)) - ((n : ℂ) + 1) ^ (1 - (s : ℂ))) / (1 - (s : ℂ))))
    (fun n v hv => norm_shift_deriv_le s hs0 n v hv)
    hw (summable_eulerTermC s hs0 hs1 w hw) hw

/-- The real part of `shiftPowSum` at a nonnegative real point is a real series. -/
lemma shiftPowSum_re_ofReal (a : ℝ) (y : ℝ) (hy : 0 ≤ y) :
    (shiftPowSum a (y : ℂ)).re = ∑' n : ℕ, ((n : ℝ) + 1 + y) ^ (-a) := by
  have h : shiftPowSum a (y : ℂ) = ((∑' n : ℕ, ((n : ℝ) + 1 + y) ^ (-a) : ℝ) : ℂ) := by
    unfold shiftPowSum
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [Complex.ofReal_cpow (by linarith [Nat.cast_nonneg (α := ℝ) n])]
    push_cast
    rfl
  rw [h, Complex.ofReal_re]

/-- Real part of a complex derivative along the reflected real variable `1 - x`. -/
lemma hasDerivAt_re_one_sub {Φ : ℂ → ℂ} {Φ' : ℂ} {y : ℝ}
    (h : HasDerivAt Φ Φ' ((1 - y : ℝ) : ℂ)) :
    HasDerivAt (fun x : ℝ => (Φ ((1 - x : ℝ) : ℂ)).re) (-Φ'.re) y := by
  have h' : HasDerivAt Φ Φ' (1 - (y : ℂ)) := by simpa using h
  have hl : HasDerivAt (fun w : ℂ => 1 - w) (-1) (y : ℂ) := by
    simpa using (hasDerivAt_id' (y : ℂ)).const_sub 1
  have hc := (h'.comp (y : ℂ) hl).real_of_complex
  simpa [Complex.ofReal_sub] using hc

/-- The unit-interval kernel expression, with derivative on `(0,1)`. -/
lemma hasDerivAt_kernel_euler (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (y : ℝ) (hy0 : 0 < y)
    (hy1 : y < 1) :
    HasDerivAt (fun x : ℝ => x ^ (-s) + (1 - x) ^ (-s) + (∑' n, eulerTermC s (x : ℂ) n).re +
        (∑' n, eulerTermC s ((1 - x : ℝ) : ℂ) n).re - 2 / (1 - s))
      (-s * y ^ (-s - 1) + s * (1 - y) ^ (-s - 1) - s * (shiftPowSum (s + 1) y).re +
        s * (shiftPowSum (s + 1) ((1 - y : ℝ) : ℂ)).re) y := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ (-s)) (-s * y ^ (-s - 1)) y :=
    Real.hasDerivAt_rpow_const (p := -s) (Or.inl hy0.ne')
  have h2 : HasDerivAt (fun x : ℝ => (1 - x) ^ (-s)) (s * (1 - y) ^ (-s - 1)) y := by
    have h := ((hasDerivAt_id' y).const_sub 1).rpow_const (p := -s)
      (Or.inl (by linarith : (1 : ℝ) - y ≠ 0))
    convert h using 1
    ring
  have h3 : HasDerivAt (fun x : ℝ => (∑' n, eulerTermC s (x : ℂ) n).re)
      (-s * (shiftPowSum (s + 1) y).re) y := by
    have h := (hasDerivAt_euler_sum s hs0 hs1 (y : ℂ) (by simp; linarith)).real_of_complex
    convert h using 1
    simp [Complex.mul_re]
  have h4 : HasDerivAt (fun x : ℝ => (∑' n, eulerTermC s ((1 - x : ℝ) : ℂ) n).re)
      (s * (shiftPowSum (s + 1) ((1 - y : ℝ) : ℂ)).re) y := by
    have h := hasDerivAt_re_one_sub (Φ := fun v : ℂ => ∑' n, eulerTermC s v n)
      (hasDerivAt_euler_sum s hs0 hs1 ((1 - y : ℝ) : ℂ) (by simp; linarith))
    convert h using 1
    simp [shiftPowSum]
  have h := (((h1.add h2).add h3).add h4).sub_const (2 / (1 - s))
  exact h.congr_deriv (by ring)

/-- The integer sum of `|y - k| ^ e` on `(0,1)`, split into `k = 0`, `k = 1`, `k ≥ 2` and `k < 0`.
-/
lemma summable_and_tsum_int_abs_rpow (e : ℝ) (he : e < -1) (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) :
    Summable (fun k : ℤ => |y - k| ^ e) ∧
      ∑' k : ℤ, |y - k| ^ e = y ^ e + (1 - y) ^ e + ∑' n : ℕ, ((n : ℝ) + 1 + y) ^ e +
        ∑' n : ℕ, ((n : ℝ) + 1 + (1 - y)) ^ e := by
  have hp : 1 < -e := by linarith
  have hA : Summable (fun n : ℕ => |y - ((n : ℤ) : ℝ)| ^ e) := by
    refine ((Real.summable_one_div_nat_add_rpow (-y) (-e)).mpr hp).congr fun n => ?_
    rw [show y - ((n : ℤ) : ℝ) = -((n : ℝ) + -y) by push_cast; ring, abs_neg,
      Real.rpow_neg (abs_nonneg _), one_div, inv_inv]
  have hB : Summable (fun n : ℕ => |y - ((-((n : ℤ) + 1) : ℤ) : ℝ)| ^ e) := by
    refine ((Real.summable_one_div_nat_add_rpow (1 + y) (-e)).mpr hp).congr fun n => ?_
    rw [show y - ((-((n : ℤ) + 1) : ℤ) : ℝ) = (n : ℝ) + (1 + y) by push_cast; ring,
      Real.rpow_neg (abs_nonneg _), one_div, inv_inv]
  refine ⟨Summable.of_nat_of_neg_add_one hA hB, ?_⟩
  have h0 : |y - (((0 : ℕ) : ℤ) : ℝ)| ^ e = y ^ e := by
    rw [Nat.cast_zero, Int.cast_zero, sub_zero, abs_of_pos hy0]
  have h1 : |y - ((((0 : ℕ) + 1 : ℕ) : ℤ) : ℝ)| ^ e = (1 - y) ^ e := by
    rw [show y - ((((0 : ℕ) + 1 : ℕ) : ℤ) : ℝ) = -(1 - y) by push_cast; ring, abs_neg,
      abs_of_pos (by linarith : (0 : ℝ) < 1 - y)]
  have h2 : ∀ n : ℕ, |y - ((((n + 1 + 1 : ℕ)) : ℤ) : ℝ)| ^ e = ((n : ℝ) + 1 + (1 - y)) ^ e := by
    intro n
    rw [show y - ((((n + 1 + 1 : ℕ)) : ℤ) : ℝ) = -((n : ℝ) + 1 + (1 - y)) by push_cast; ring,
      abs_neg, abs_of_pos (by linarith [Nat.cast_nonneg (α := ℝ) n] :
        (0 : ℝ) < (n : ℝ) + 1 + (1 - y))]
  have h3 : ∀ n : ℕ, |y - ((-((n : ℤ) + 1) : ℤ) : ℝ)| ^ e = ((n : ℝ) + 1 + y) ^ e := by
    intro n
    rw [show y - ((-((n : ℤ) + 1) : ℤ) : ℝ) = (n : ℝ) + 1 + y by push_cast; ring,
      abs_of_pos (by linarith [Nat.cast_nonneg (α := ℝ) n] : (0 : ℝ) < (n : ℝ) + 1 + y)]
  rw [tsum_of_nat_of_neg_add_one (f := fun k : ℤ => |y - k| ^ e) hA hB, hA.tsum_eq_zero_add,
    ((summable_nat_add_iff 1).mpr hA).tsum_eq_zero_add]
  simp only [h0, h1, h2, h3]
  ring

/-- Second derivative on `(0,1)`: the derivative of the first-derivative formula. -/
lemma hasDerivAt_first_deriv (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (y : ℝ) (hy0 : 0 < y)
    (hy1 : y < 1) :
    HasDerivAt (fun x : ℝ => -s * x ^ (-s - 1) + s * (1 - x) ^ (-s - 1) -
        s * (shiftPowSum (s + 1) x).re + s * (shiftPowSum (s + 1) ((1 - x : ℝ) : ℂ)).re)
      (s * (s + 1) * (y ^ (-s - 2) + (1 - y) ^ (-s - 2) + (shiftPowSum (s + 2) y).re +
        (shiftPowSum (s + 2) ((1 - y : ℝ) : ℂ)).re)) y := by
  have hp1 : HasDerivAt (fun x : ℝ => x ^ (-s - 1)) ((-s - 1) * y ^ (-s - 2)) y := by
    have h := Real.hasDerivAt_rpow_const (p := -s - 1) (Or.inl hy0.ne')
    rw [show (-s - 1 - 1 : ℝ) = -s - 2 by ring] at h
    exact h
  have hp2 : HasDerivAt (fun x : ℝ => (1 - x) ^ (-s - 1)) ((-1) * (-s - 1) * (1 - y) ^ (-s - 2))
      y := by
    have h := ((hasDerivAt_id' y).const_sub 1).rpow_const (p := -s - 1)
      (Or.inl (by linarith : (1 : ℝ) - y ≠ 0))
    rw [show (-s - 1 - 1 : ℝ) = -s - 2 by ring] at h
    exact h
  have hre1 : HasDerivAt (fun x : ℝ => (shiftPowSum (s + 1) x).re)
      (-(s + 1) * (shiftPowSum (s + 2) y).re) y := by
    have h := (hasDerivAt_shiftPowSum (s + 1) (by linarith) (y : ℂ)
      (by simp; linarith)).real_of_complex
    rw [show s + 1 + 1 = s + 2 by ring] at h
    convert h using 1
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hre2 : HasDerivAt (fun x : ℝ => (shiftPowSum (s + 1) ((1 - x : ℝ) : ℂ)).re)
      ((s + 1) * (shiftPowSum (s + 2) ((1 - y : ℝ) : ℂ)).re) y := by
    have h := hasDerivAt_re_one_sub (Φ := shiftPowSum (s + 1)) (y := y)
      (hasDerivAt_shiftPowSum (s + 1) (by linarith) ((1 - y : ℝ) : ℂ)
        (by simp; linarith))
    rw [show s + 1 + 1 = s + 2 by ring] at h
    convert h using 1
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have h := (((hp1.const_mul (-s)).add (hp2.const_mul s)).sub (hre1.const_mul s)).add
    (hre2.const_mul s)
  exact h.congr_deriv (by ring)

/-- The kernel is `1`-periodic. -/
lemma hurwitzKernel_periodic (s : ℝ) : Function.Periodic (hurwitzKernel s) 1 := fun x => by
  unfold hurwitzKernel
  congr 1
  exact hurwitzZetaEven_re_periodic (s : ℂ) x

lemma hurwitzKernel_sub_int (s : ℝ) (n : ℤ) (z : ℝ) :
    hurwitzKernel s (z - n) = hurwitzKernel s z := by
  simpa using (hurwitzKernel_periodic s).sub_int_mul_eq (x := z) n

lemma hurwitzKernel_eq_euler (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ) (hx0 : 0 < x)
    (hx1 : x < 1) :
    hurwitzKernel s x = x ^ (-s) + (1 - x) ^ (-s) + (∑' n, eulerTermC s (x : ℂ) n).re +
      (∑' n, eulerTermC s ((1 - x : ℝ) : ℂ) n).re - 2 / (1 - s) := by
  unfold hurwitzKernel
  exact hurwitzZetaEven_re_euler s hs0 hs1 x hx0 hx1

/-- Second derivative of the kernel on `(0,1)`, as an integer series. -/
lemma hasDerivAt_deriv_hurwitzKernel_unit (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (y : ℝ)
    (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt (deriv (hurwitzKernel s)) (s * (s + 1) * ∑' k : ℤ, |y - k| ^ (-s - 2)) y := by
  have hK : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (hurwitzKernel s)
      (-s * x ^ (-s - 1) + s * (1 - x) ^ (-s - 1) - s * (shiftPowSum (s + 1) x).re +
        s * (shiftPowSum (s + 1) ((1 - x : ℝ) : ℂ)).re) x := fun x hx =>
    (hasDerivAt_kernel_euler s hs0 hs1 x hx.1 hx.2).congr_of_eventuallyEq
      (Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) fun z hz =>
        hurwitzKernel_eq_euler s hs0 hs1 z hz.1 hz.2)
  have hev : deriv (hurwitzKernel s) =ᶠ[𝓝 y] fun x : ℝ => -s * x ^ (-s - 1) +
      s * (1 - x) ^ (-s - 1) - s * (shiftPowSum (s + 1) x).re +
        s * (shiftPowSum (s + 1) ((1 - x : ℝ) : ℂ)).re :=
    Filter.eventually_of_mem (Ioo_mem_nhds hy0 hy1) fun x hx => (hK x hx).deriv
  refine ((hasDerivAt_first_deriv s hs0 hs1 y hy0 hy1).congr_of_eventuallyEq hev).congr_deriv ?_
  obtain ⟨-, htsum⟩ := summable_and_tsum_int_abs_rpow (-s - 2) (by linarith) y hy0 hy1
  have hexp : -(s + 2) = -s - 2 := by ring
  rw [htsum, shiftPowSum_re_ofReal (s + 2) y hy0.le,
    shiftPowSum_re_ofReal (s + 2) (1 - y) (by linarith), hexp]

/-- A real number whose class in the unit circle is nonzero lies strictly between consecutive
integers, after shifting by its floor. -/
lemma fract_pos_of_coe_ne_zero (x : ℝ) (hx : (x : UnitAddCircle) ≠ 0) :
    0 < x - (⌊x⌋ : ℝ) := by
  have h0 : 0 < Int.fract x := by
    apply lt_of_le_of_ne (Int.fract_nonneg x)
    intro h
    apply hx
    have heq := AddCircle.coe_fract x
    rw [← h, AddCircle.coe_zero] at heq
    exact heq.symm
  exact h0

lemma coe_ne_zero_of_mem_Ioo_int (n : ℤ) (x : ℝ) (hx : x ∈ Ioo (n : ℝ) (n + 1)) :
    (x : UnitAddCircle) ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h
  rw [zsmul_eq_mul, mul_one] at hm
  have h1 : (n : ℝ) < m := by rw [hm]; exact hx.1
  have h2 : (m : ℝ) < n + 1 := by rw [hm]; exact hx.2
  have h3 : n < m := by exact_mod_cast h1
  have h4 : m < n + 1 := by exact_mod_cast h2
  omega

/-- The kernel is differentiable at every point off the integers, with the first-derivative
formula of `hasDerivAt_kernel_euler` at the shifted point. -/
lemma differentiableAt_hurwitzKernel_of_ne (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ)
    (hx : (x : UnitAddCircle) ≠ 0) : DifferentiableAt ℝ (hurwitzKernel s) x := by
  have hy0 := fract_pos_of_coe_ne_zero x hx
  have hy1 : x - (⌊x⌋ : ℝ) < 1 := by
    have := Int.fract_lt_one x
    unfold Int.fract at this
    exact this
  have hK : ∀ z ∈ Ioo (0 : ℝ) 1, HasDerivAt (hurwitzKernel s)
      (-s * z ^ (-s - 1) + s * (1 - z) ^ (-s - 1) - s * (shiftPowSum (s + 1) z).re +
        s * (shiftPowSum (s + 1) ((1 - z : ℝ) : ℂ)).re) z := fun z hz =>
    (hasDerivAt_kernel_euler s hs0 hs1 z hz.1 hz.2).congr_of_eventuallyEq
      (Filter.eventually_of_mem (Ioo_mem_nhds hz.1 hz.2) fun w hw =>
        hurwitzKernel_eq_euler s hs0 hs1 w hw.1 hw.2)
  have hd : DifferentiableAt ℝ (fun z : ℝ => hurwitzKernel s (z - ⌊x⌋)) x := by
    have h := ((hK _ ⟨hy0, hy1⟩).comp_sub_const x (⌊x⌋ : ℝ)).differentiableAt
    exact h
  have hfun : (fun z : ℝ => hurwitzKernel s (z - ⌊x⌋)) = hurwitzKernel s :=
    funext fun z => hurwitzKernel_sub_int s ⌊x⌋ z
  exact hfun ▸ hd

/-- Second derivative of the project kernel, at every point off the integers
(Lemma 2.1, derivative claims). -/
theorem hasDerivAt_deriv_hurwitzKernel (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ)
    (hx : (x : UnitAddCircle) ≠ 0) :
    HasDerivAt (deriv (hurwitzKernel s)) (s * (s + 1) * ∑' k : ℤ, |x - k| ^ (-s - 2)) x := by
  have hy0 := fract_pos_of_coe_ne_zero x hx
  have hy1 : x - (⌊x⌋ : ℝ) < 1 := by
    have := Int.fract_lt_one x
    unfold Int.fract at this
    exact this
  have hder := hasDerivAt_deriv_hurwitzKernel_unit s hs0 hs1 (x - ⌊x⌋) hy0 hy1
  have hdK : deriv (hurwitzKernel s) = fun z => deriv (hurwitzKernel s) (z - ⌊x⌋) := by
    funext z
    rw [← deriv_comp_sub_const]
    congr 1
    funext w
    exact (hurwitzKernel_sub_int s ⌊x⌋ w).symm
  have hshift : ∑' k : ℤ, |x - k| ^ (-s - 2) = ∑' k : ℤ, |(x - ⌊x⌋) - k| ^ (-s - 2) := by
    rw [← (Equiv.subRight (⌊x⌋ : ℤ)).tsum_eq (fun k : ℤ => |(x - ⌊x⌋) - (k : ℝ)| ^ (-s - 2))]
    exact tsum_congr fun k => by
      show |x - k| ^ (-s - 2) = |(x - ⌊x⌋) - ((k - ⌊x⌋ : ℤ) : ℝ)| ^ (-s - 2)
      rw [show (x - ⌊x⌋) - ((k - ⌊x⌋ : ℤ) : ℝ) = x - k by push_cast; ring]
  rw [hdK]
  exact ((hder.comp_sub_const x (⌊x⌋ : ℝ))).congr_deriv (by rw [hshift])

/-- The shifted series is summable at every point off the integers. -/
lemma summable_abs_sub_rpow_of_ne (s : ℝ) (hs0 : 0 < s) (x : ℝ) (hx : (x : UnitAddCircle) ≠ 0) :
    Summable (fun k : ℤ => |x - k| ^ (-s - 2)) := by
  have hy0 := fract_pos_of_coe_ne_zero x hx
  have hy1 : x - (⌊x⌋ : ℝ) < 1 := by
    have := Int.fract_lt_one x
    unfold Int.fract at this
    exact this
  obtain ⟨hsumF, -⟩ := summable_and_tsum_int_abs_rpow (-s - 2) (by linarith) _ hy0 hy1
  refine ((Equiv.subRight (⌊x⌋ : ℤ)).summable_iff.mpr hsumF).congr fun k => ?_
  show |(x - ⌊x⌋) - ((k - ⌊x⌋ : ℤ) : ℝ)| ^ (-s - 2) = |x - k| ^ (-s - 2)
  rw [show (x - ⌊x⌋) - ((k - ⌊x⌋ : ℤ) : ℝ) = x - k by push_cast; ring]

/-- The second derivative value is positive off the integers. -/
lemma pos_second_deriv_value (s : ℝ) (hs0 : 0 < s) (x : ℝ) (hx : (x : UnitAddCircle) ≠ 0) :
    0 < s * (s + 1) * ∑' k : ℤ, |x - k| ^ (-s - 2) := by
  have hx0 : x ≠ 0 := fun h => hx (by rw [h, AddCircle.coe_zero])
  have hpos : 0 < ∑' k : ℤ, |x - k| ^ (-s - 2) :=
    Summable.tsum_pos (summable_abs_sub_rpow_of_ne s hs0 x hx)
      (fun k => Real.rpow_nonneg (abs_nonneg _) _) 0
      (Real.rpow_pos_of_pos (by simpa using abs_pos.mpr hx0) _)
  exact mul_pos (mul_pos hs0 (by linarith)) hpos

/-- Strict convexity of the kernel on each open unit interval (Lemma 2.1,
convexity from the positive second derivative). -/
theorem strictConvexOn_hurwitzKernel (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (n : ℤ) :
    StrictConvexOn ℝ (Ioo (n : ℝ) (n + 1)) (hurwitzKernel s) := by
  refine strictConvexOn_of_deriv2_pos (convex_Ioo _ _) ?_ ?_
  · intro x hx
    exact (differentiableAt_hurwitzKernel_of_ne s hs0 hs1 x
      (coe_ne_zero_of_mem_Ioo_int n x hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    have hne := coe_ne_zero_of_mem_Ioo_int n x hx
    have h2 : deriv^[2] (hurwitzKernel s) x = deriv (deriv (hurwitzKernel s)) x := rfl
    rw [h2, (hasDerivAt_deriv_hurwitzKernel s hs0 hs1 x hne).deriv]
    exact pos_second_deriv_value s hs0 x hne

/-- Second derivative of the kernel off the integers (Lemma 2.1): the
derivative `g'` is differentiable with derivative `s (s + 1) ∑ₖ |x - k| ^ (-s - 2)`, this series
is summable, and its value is positive. -/
theorem second_derivative_hurwitzKernel (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ)
    (hx : (x : UnitAddCircle) ≠ 0) :
    HasDerivAt (deriv (hurwitzKernel s)) (s * (s + 1) * ∑' k : ℤ, |x - k| ^ (-s - 2)) x ∧
      Summable (fun k : ℤ => |x - k| ^ (-s - 2)) ∧
      0 < s * (s + 1) * ∑' k : ℤ, |x - k| ^ (-s - 2) :=
  ⟨hasDerivAt_deriv_hurwitzKernel s hs0 hs1 x hx, summable_abs_sub_rpow_of_ne s hs0 x hx,
    pos_second_deriv_value s hs0 x hx⟩

end Riesz1
