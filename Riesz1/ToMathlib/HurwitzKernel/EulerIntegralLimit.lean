/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.Euler
public import Riesz1.ToMathlib.HurwitzKernel.EulerIntegralSawtooth
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Hurwitz zeta function at real `x > 0`: Euler limit for every `x`

Lemma 2.1. The function `hurwitzZetaPos z x` is the
Hurwitz zeta function `ζ(z, x)` for real `x > 0`. It is Mathlib's
continuation `HurwitzZeta.hurwitzZeta` at the representative of `x` in `(0, 1]`, corrected by the
finite sum that shifts `x` into that interval. For `x ∈ (0, 1]` it is Mathlib's function itself.

The file proves the Euler limit of equation (2.11) (first line) for every `x > 0` and `Re z > 0`,
reducing to Euler summation on `(0, 1]` in `Riesz1.tendsto_hurwitzZeta_sub`. The shift
`x ↦ x + m` changes the regularized partial sums by a finite sum and by the term
`((M + m)^{1-z} - M^{1-z})/(1-z)`, which tends to zero.
-/

public section

open MeasureTheory Set Filter Topology intervalIntegral

namespace Riesz1

/-- The Hurwitz zeta function `ζ(z, x)` for real `x > 0`, as Mathlib's
continuation at the representative of `x` in `(0, 1]`, minus the finite sum over the integer
shift `m = ⌈x⌉₊ - 1`. It is meaningful for `z ≠ 1`, the only pole. -/
@[expose] noncomputable def hurwitzZetaPos (z : ℂ) (x : ℝ) : ℂ :=
  HurwitzZeta.hurwitzZeta ((x - (⌈x⌉₊ : ℝ) + 1 : ℝ) : UnitAddCircle) z -
    ∑ j ∈ Finset.range (⌈x⌉₊ - 1), ((x - (⌈x⌉₊ : ℝ) + 1 + j : ℝ) : ℂ) ^ (-z)

/-- Representation with any integer shift `m` bringing `x` into `(0, 1]`. -/
lemma hurwitzZetaPos_eq_of_shift (z : ℂ) {x : ℝ} {m : ℕ} (hx0 : 0 < x - m) (hx1 : x - m ≤ 1) :
    hurwitzZetaPos z x = HurwitzZeta.hurwitzZeta ((x - m : ℝ) : UnitAddCircle) z -
      ∑ j ∈ Finset.range m, ((x - m + j : ℝ) : ℂ) ^ (-z) := by
  have hceil : ⌈x⌉₊ = m + 1 := by
    rw [Nat.ceil_eq_iff (by omega)]
    push_cast
    constructor <;> linarith
  unfold hurwitzZetaPos
  rw [hceil, Nat.add_sub_cancel]
  have e1 : (x - ((m + 1 : ℕ) : ℝ) + 1) = x - m := by push_cast; ring
  rw [e1]

/-- The power `t ↦ (t + x)^w` is integrable on `(0, ∞)` when `Re w < -1` and `x > 0`. -/
lemma integrableOn_Ioi_add_cpow {x : ℝ} (hx : 0 < x) {w : ℂ} (hw : w.re < -1) :
    IntegrableOn (fun t : ℝ => ((t : ℂ) + x) ^ w) (Ioi 0) := by
  have hreal : IntegrableOn (fun t : ℝ => (t + x) ^ w.re) (Ioi 0) := by
    have h1 : IntegrableOn (fun u : ℝ => u ^ w.re) (Ioi x) := integrableOn_Ioi_rpow_of_lt hw hx
    have h2 : Integrable ((Ioi x).indicator fun u : ℝ => u ^ w.re) :=
      (integrable_indicator_iff measurableSet_Ioi).mpr h1
    have h3 := h2.comp_add_right x
    refine (h3.integrableOn).congr_fun ?_ measurableSet_Ioi
    intro t ht
    have hpos : x < t + x := by linarith [mem_Ioi.mp ht]
    simp [Set.indicator, hpos]
  refine Integrable.mono' hreal ?_ ?_
  · exact ((Measurable.pow_const (by fun_prop : Measurable fun t : ℝ => (t : ℂ) + x) w).aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hpos : 0 < (t : ℝ) + x := by linarith [mem_Ioi.mp ht]
    have e : ((t : ℂ) + x) = (((t + x : ℝ)) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_cpow_eq_rpow_re_of_pos hpos]

/-- The shifted power difference `(M + h)^w - M^w` tends to zero when `Re w < 1`. -/
lemma norm_cpow_add_sub_le {w : ℂ} (hw : w.re < 1) {M h : ℝ} (hM : 0 < M) (hh : 0 ≤ h) :
    ‖((M + h : ℝ) : ℂ) ^ w - (M : ℂ) ^ w‖ ≤ ‖w‖ * M ^ (w.re - 1) * h := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simp
  have hderiv : ∀ x ∈ Icc M (M + h), HasDerivWithinAt (fun t : ℝ => (t : ℂ) ^ w)
      (w * (x : ℂ) ^ (w - 1)) (Icc M (M + h)) x := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hM hx.1
    exact (hasDerivAt_ofReal_cpow_const hxpos.ne' hw0).hasDerivWithinAt
  have hbound : ∀ x ∈ Ico M (M + h), ‖w * (x : ℂ) ^ (w - 1)‖ ≤ ‖w‖ * M ^ (w.re - 1) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hM hx.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    simp only [Complex.sub_re, Complex.one_re]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.rpow_le_rpow_of_nonpos hM hx.1 (by linarith)
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (M + h) ⟨by linarith, le_rfl⟩
  simp only [add_sub_cancel_left] at key
  calc ‖((M + h : ℝ) : ℂ) ^ w - (M : ℂ) ^ w‖ ≤ ‖w‖ * M ^ (w.re - 1) * h := key

/-- Shifted powers: `((M + h)^w - M^w) → 0` as `M → ∞` for `Re w < 1` and `h ≥ 0`. -/
lemma tendsto_cpow_add_sub {w : ℂ} (hw : w.re < 1) {h : ℝ} (hh : 0 ≤ h) :
    Tendsto (fun M : ℕ => ((((M : ℝ) + h : ℝ)) : ℂ) ^ w - (M : ℂ) ^ w) atTop (𝓝 0) := by
  have hp : 0 < 1 - w.re := by linarith
  have hlim : Tendsto (fun M : ℕ => ‖w‖ * h * ((M : ℝ)) ^ (-(1 - w.re))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hp).comp tendsto_natCast_atTop_atTop).const_mul (‖w‖ * h)
    simpa using this
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have := norm_cpow_add_sub_le hw hMpos hh
  have e : w.re - 1 = -(1 - w.re) := by ring
  rw [e] at this
  simp only [Complex.ofReal_natCast] at this
  exact this.trans (le_of_eq (by ring))

/-- The shifted power `(M + h)^w` against `M^w`: the same bound in `ℕ`-indexed form. -/
lemma tendsto_natCast_add_cpow_sub {w : ℂ} (hw : w.re < 1) (m : ℕ) :
    Tendsto (fun M : ℕ => ((M + m : ℕ) : ℂ) ^ w - (M : ℂ) ^ w) atTop (𝓝 0) := by
  have h := tendsto_cpow_add_sub hw (h := (m : ℝ)) (Nat.cast_nonneg m)
  refine h.congr (fun M => ?_)
  push_cast
  ring_nf

/-- Euler summation for `ζ(z, x)` at every real `x > 0`, for `Re z > 0` and `z ≠ 1`:
the regularized partial sums converge to `hurwitzZetaPos z x` (equation (2.11),
first line, with `x` arbitrary). -/
theorem tendsto_hurwitzZetaPos {x : ℝ} (hx : 0 < x) {z : ℂ} (hz : 0 < z.re) (hz1 : z ≠ 1) :
    Tendsto (fun M : ℕ => (∑ n ∈ Finset.range (M + 1), ((n : ℂ) + x) ^ (-z)) -
      (M : ℂ) ^ (1 - z) / (1 - z)) atTop (𝓝 (hurwitzZetaPos z x)) := by
  have hn0 : ⌈x⌉₊ ≠ 0 := (Nat.ceil_pos.mpr hx).ne'
  have hceilA := (Nat.ceil_eq_iff hn0).mp rfl
  set m : ℕ := ⌈x⌉₊ - 1 with hm
  have hcast : (⌈x⌉₊ : ℝ) = (m : ℝ) + 1 := by
    rw [hm, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn0)]
    push_cast
    ring
  have hy0 : 0 < x - m := by linarith [hceilA.1]
  have hy1 : x - m ≤ 1 := by linarith [hceilA.2, hcast]
  set y : ℝ := x - m with hy
  rw [hurwitzZetaPos_eq_of_shift z hy0 hy1]
  have hE := (tendsto_hurwitzZeta_sub y hy0 hy1 z hz hz1).comp (tendsto_add_atTop_nat m)
  have hS := tendsto_natCast_add_cpow_sub (w := 1 - z) (by simp; linarith) m
  have hL := (hE.sub_const (∑ j ∈ Finset.range m, ((y + j : ℝ) : ℂ) ^ (-z))).add
    (hS.div_const (1 - z))
  rw [zero_div, add_zero] at hL
  refine hL.congr (fun M => ?_)
  have hsum : ∑ n ∈ Finset.range (M + 1), ((n : ℂ) + x) ^ (-z) =
      (∑ n ∈ Finset.range (M + m + 1), ((n : ℂ) + y) ^ (-z)) -
        ∑ j ∈ Finset.range m, ((y + j : ℝ) : ℂ) ^ (-z) := by
    have h1 := Finset.sum_range_add (fun k : ℕ => ((k : ℂ) + y) ^ (-z)) m (M + 1)
    have h2 : m + (M + 1) = M + m + 1 := by omega
    rw [h2] at h1
    have h3 : ∑ n ∈ Finset.range (M + 1), ((n : ℂ) + x) ^ (-z) =
        ∑ i ∈ Finset.range (M + 1), (((m + i : ℕ) : ℂ) + y) ^ (-z) :=
      Finset.sum_congr rfl (fun i _ => by
        congr 1
        simp only [hy]
        push_cast
        ring)
    have hcastsum : ∑ j ∈ Finset.range m, ((y + j : ℝ) : ℂ) ^ (-z) =
        ∑ j ∈ Finset.range m, ((j : ℂ) + y) ^ (-z) :=
      Finset.sum_congr rfl (fun j _ => by
        congr 1
        push_cast
        ring)
    rw [h3, hcastsum]
    linear_combination -h1
  simp only [Function.comp_apply]
  rw [hsum]
  push_cast
  ring

end Riesz1

end
