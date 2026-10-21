/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.Euler
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Hurwitz zeta at a real point, for exponents of positive real part

For a real point `x` and a complex exponent `w`, `hurwitzAt x w` is Mathlib's Hurwitz zeta
function at the image of `x` in the unit circle. For `0 < x < 1` and `0 < Re w`, `w ≠ 1`, the
Euler representation of `Riesz1.euler_eq_hurwitzZeta` writes it as a locally convergent series.
This file differentiates that representation in the real point `x`. It proves the derivative
identity `∂_x ζ(w, x) = -w ζ(w + 1, x)` of Lemma 2.1 in this range, and the smoothness of
`x ↦ ζ(w, x)` on `(0, 1)`.
-/

public section

open Complex Set Filter Topology
open scoped ContDiff
namespace Riesz1

/-- The Hurwitz zeta function `ζ(w, x)` at the real point `x`, as Mathlib's function on the
unit circle. -/
@[expose] noncomputable def hurwitzAt (x : ℝ) (w : ℂ) : ℂ :=
  HurwitzZeta.hurwitzZeta (x : UnitAddCircle) w

/-- The real-variable derivative of `v ↦ (n + 1 + v)^(-w)` at a point `y` with `n + 1 + y > 0`. -/
lemma hasDerivAt_shift_cpow_real (w : ℂ) (n : ℕ) {y : ℝ} (hy : 0 < (n : ℝ) + 1 + y) :
    HasDerivAt (fun v : ℝ => ((n : ℂ) + 1 + (v : ℂ)) ^ (-w))
      (-w * ((n : ℂ) + 1 + (y : ℂ)) ^ (-w - 1)) y := by
  have hslit : (n : ℂ) + 1 + (y : ℂ) ∈ slitPlane := by
    apply Or.inl
    simp only [add_re, natCast_re, one_re, ofReal_re]
    linarith
  have hc : HasDerivAt (fun v : ℂ => ((n : ℂ) + 1 + v) ^ (-w))
      (-w * ((n : ℂ) + 1 + (y : ℂ)) ^ (-w - 1)) (y : ℂ) := by
    have h := ((hasDerivAt_id (y : ℂ)).const_add ((n : ℂ) + 1)).cpow_const (c := -w) hslit
    simpa only [mul_one, id_eq] using h
  exact hc.comp_ofReal

/-- The real-variable derivative of the Euler term `n` at a point `y` with `n + 1 + y > 0`. -/
lemma hasDerivAt_eulerTerm_real (w : ℂ) (n : ℕ) {y : ℝ} (hy : 0 < (n : ℝ) + 1 + y) :
    HasDerivAt (fun v : ℝ => eulerTerm v w n) (-w * ((n : ℂ) + 1 + (y : ℂ)) ^ (-w - 1)) y := by
  have heq : (fun v : ℝ => eulerTerm v w n) = fun v : ℝ =>
      ((n : ℂ) + 1 + (v : ℂ)) ^ (-w) -
        (((n : ℂ) + 2) ^ (1 - w) - ((n : ℂ) + 1) ^ (1 - w)) / (1 - w) := by
    funext v
    simp only [eulerTerm]
  rw [heq]
  exact (hasDerivAt_shift_cpow_real w n hy).sub_const _

/-- Euler term derivative bound: for `Re w > 0` and `0 ≤ y`, the derivative of the `n`-th
Euler term is at most `‖w‖ (n + 1)^(-Re w - 1)` in norm, uniformly in `y ≥ 0`. -/
lemma norm_eulerTerm_deriv_le (w : ℂ) (hw : 0 < w.re) (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    ‖-w * ((n : ℂ) + 1 + (y : ℂ)) ^ (-w - 1)‖ ≤ ‖w‖ * ((n : ℝ) + 1) ^ (-w.re - 1) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 + y := by positivity
  have hpos' : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : ((n : ℂ) + 1 + (y : ℂ)) = (((n : ℝ) + 1 + y : ℝ) : ℂ) := by push_cast; ring
  rw [norm_mul, norm_neg, hcast, norm_cpow_eq_rpow_re_of_pos hpos]
  simp only [sub_re, neg_re, one_re]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact Real.rpow_le_rpow_of_nonpos hpos' (by linarith) (by linarith)

/-- The Hurwitz zeta series at a point `x ∈ [0, 1]` and exponent `Re w > 1`. -/
lemma hasSum_hurwitzAt {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {w : ℂ} (hw : 1 < w.re) :
    HasSum (fun n : ℕ => ((n : ℂ) + x) ^ (-w)) (hurwitzAt x w) := by
  have h := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re (a := x) ⟨hx0, hx1⟩ hw
  have hfun : (fun n : ℕ => ((n : ℂ) + x) ^ (-w)) = fun n : ℕ => 1 / ((n : ℂ) + x) ^ w := by
    funext n
    rw [one_div, cpow_neg]
  rw [hfun]
  exact h

/-- Splitting off the first term of the Hurwitz series: for `x ∈ [0, 1]` and `Re w > 1`,
`ζ(w, x) = x^(-w) + ∑ₙ (n + 1 + x)^(-w)`. -/
lemma hurwitzAt_eq_zero_add {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {w : ℂ} (hw : 1 < w.re) :
    hurwitzAt x w = (x : ℂ) ^ (-w) + ∑' n : ℕ, ((n : ℂ) + 1 + x) ^ (-w) := by
  have h := hasSum_hurwitzAt hx0 hx1 hw
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  congr 1
  · simp
  · congr 1
    funext n
    push_cast
    ring_nf

/-- The derivative of the Hurwitz zeta function in its real point, on `(0, 1)`, for
`Re w > 0`: `∂_x ζ(w, x) = -w ζ(w + 1, x)`. This is the identity of Lemma 2.1 in the range
`Re w > 0`, where the Euler representation converges. -/
theorem hasDerivAt_hurwitzAt_of_re_pos {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun v : ℝ => hurwitzAt v w) (-w * hurwitzAt x (w + 1)) x := by
  set E : ℝ → ℂ := fun v => (v : ℂ) ^ (-w) + ∑' n, eulerTerm v w n - 1 / (1 - w) with hE
  have hev : (fun v : ℝ => hurwitzAt v w) =ᶠ[𝓝 x] E := by
    filter_upwards [Ioo_mem_nhds hx0 hx1] with v hv
    exact (euler_eq_hurwitzZeta v hv.1 hv.2.le w hw hw1).symm
  have hsum : HasDerivAt (fun v : ℝ => ∑' n, eulerTerm v w n)
      (∑' n : ℕ, -w * ((n : ℂ) + 1 + (x : ℂ)) ^ (-w - 1)) x := by
    have hu : Summable (fun n : ℕ => ‖w‖ * ((n : ℝ) + 1) ^ (-w.re - 1)) := by
      apply Summable.mul_left
      simpa only [Nat.cast_add, Nat.cast_one] using
        (summable_nat_add_iff 1).mpr
          (Real.summable_nat_rpow.mpr (show -w.re - 1 < -1 by linarith))
    refine hasDerivAt_tsum_of_isPreconnected (g := fun n v => eulerTerm v w n)
      (g' := fun n y => -w * ((n : ℂ) + 1 + (y : ℂ)) ^ (-w - 1)) hu isOpen_Ioo
      isPreconnected_Ioo (fun n y hy => hasDerivAt_eulerTerm_real w n (by linarith [hy.1]))
      (fun n y hy => norm_eulerTerm_deriv_le w hw n hy.1.le) ⟨hx0, hx1⟩
      (summable_eulerTerm x hx0.le hx1.le w hw hw1) ⟨hx0, hx1⟩
  have hw0 : -w ≠ 0 := by
    intro h
    have : w = 0 := by linear_combination -h
    rw [this] at hw
    simp at hw
  have hpow : HasDerivAt (fun v : ℝ => (v : ℂ) ^ (-w)) ((-w) * (x : ℂ) ^ (-w - 1)) x :=
    hasDerivAt_ofReal_cpow_const hx0.ne' hw0
  have hE' : HasDerivAt E ((-w) * (x : ℂ) ^ (-w - 1) +
      ∑' n : ℕ, -w * ((n : ℂ) + 1 + (x : ℂ)) ^ (-w - 1)) x :=
    (hpow.add hsum).sub_const _
  have hw' : 1 < (w + 1).re := by simp; linarith
  have hneg : -(w + 1) = -w - 1 := by ring
  have hvalue : (-w) * (x : ℂ) ^ (-w - 1) + ∑' n : ℕ, -w * ((n : ℂ) + 1 + (x : ℂ)) ^ (-w - 1) =
      -w * hurwitzAt x (w + 1) := by
    rw [hurwitzAt_eq_zero_add hx0.le hx1.le hw', tsum_mul_left, hneg]
    ring
  rw [← hvalue]
  exact hE'.congr_of_eventuallyEq hev

/-- The Hurwitz zeta function is `C^k` in its real point on `(0, 1)`, for every finite `k`
and every exponent `Re w > 0`, `w ≠ 1`. The derivative of order `k + 1` is the same family
at the exponent `w + 1`. -/
theorem contDiffOn_hurwitzAt_of_re_pos (k : ℕ) :
    ∀ {w : ℂ}, 0 < w.re → w ≠ 1 → ContDiffOn ℝ k (fun v : ℝ => hurwitzAt v w) (Ioo 0 1) := by
  induction k with
  | zero =>
    intro w hw hw1
    refine contDiffOn_zero.mpr (fun x hx => ?_)
    exact (hasDerivAt_hurwitzAt_of_re_pos hw hw1 hx.1 hx.2).continuousAt.continuousWithinAt
  | succ k ih =>
    intro w hw hw1
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
    refine (contDiffOn_succ_iff_deriv_of_isOpen (f := fun v : ℝ => hurwitzAt v w)
      (n := (k : WithTop ℕ∞)) isOpen_Ioo).mpr ⟨?_, ?_, ?_⟩
    · intro x hx
      exact (hasDerivAt_hurwitzAt_of_re_pos hw hw1 hx.1 hx.2).differentiableAt.differentiableWithinAt
    · intro h
      exact absurd h (by simp)
    · have hw' : 0 < (w + 1).re := by simp; linarith
      have hw1' : w + 1 ≠ 1 := by
        intro h
        exact hw0 (by linear_combination h)
      have hderiv : EqOn (deriv (fun v : ℝ => hurwitzAt v w))
          (fun v : ℝ => -w * hurwitzAt v (w + 1)) (Ioo 0 1) := by
        intro x hx
        exact (hasDerivAt_hurwitzAt_of_re_pos hw hw1 hx.1 hx.2).deriv
      exact ((contDiffOn_const (c := -w)).mul (ih hw' hw1')).congr hderiv

/-- The Hurwitz zeta function is `C^∞` in its real point on `(0, 1)`, for `Re w > 0`,
`w ≠ 1`. -/
theorem contDiffOn_infty_hurwitzAt_of_re_pos {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    ContDiffOn ℝ ∞ (fun v : ℝ => hurwitzAt v w) (Ioo 0 1) :=
  contDiffOn_infty.mpr fun k => contDiffOn_hurwitzAt_of_re_pos k hw hw1

end Riesz1

end
