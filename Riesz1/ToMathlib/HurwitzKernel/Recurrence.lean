/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.EulerIntegralAnalytic

/-!
# Recurrence, smoothness and the derivative of the Hurwitz zeta function

Lemma 2.1. For real `x > 0` and `z` in the domain of the continued
formula:

* the recurrence `ζ(z, x) = x^{-z} + ζ(z, x + 1)` holds for every `z`, directly from the
  definition `Riesz1.hurwitzZetaPos` by a shift of the integer part.
* `x ↦ ζ(z, x)` is smooth on `(0, ∞)` for `Re z > -1`, `z ≠ 1`, through the continued formula.
* `∂_x ζ(z, x) = -z ζ(z + 1, x)` for `Re z > -1`, `z ≠ 0, 1`.

The derivative identity is checked on `zetaRhs`, whose three elementary terms and second-order
term differentiate termwise: the second-order integral has derivative `-(2+z) zetaB2Int (z+1) x`.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ContDiff

namespace Riesz1

/-! ### The recurrence, from the definition -/

/-- The Hurwitz zeta recurrence `ζ(z, x) = x^{-z} + ζ(z, x + 1)` for `x > 0` and every `z`
(Lemma 2.1, recurrence). It is a shift of the integer part in the
definition `hurwitzZetaPos`. -/
theorem hurwitzZetaPos_recurrence {x : ℝ} (hx : 0 < x) (z : ℂ) :
    hurwitzZetaPos z x = (x : ℂ) ^ (-z) + hurwitzZetaPos z (x + 1) := by
  have hn0 : ⌈x⌉₊ ≠ 0 := (Nat.ceil_pos.mpr hx).ne'
  have hceilA := (Nat.ceil_eq_iff hn0).mp rfl
  set m : ℕ := ⌈x⌉₊ - 1 with hm
  have hcast : (⌈x⌉₊ : ℝ) = (m : ℝ) + 1 := by
    rw [hm, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn0)]
    push_cast
    ring
  have h0 : 0 < x - m := by linarith [hceilA.1]
  have h1 : x - m ≤ 1 := by linarith [hceilA.2, hcast]
  have hA := hurwitzZetaPos_eq_of_shift z h0 h1
  have hB := hurwitzZetaPos_eq_of_shift z (x := x + 1) (m := m + 1)
    (by push_cast; linarith) (by push_cast; linarith)
  have e : x + 1 - ((m + 1 : ℕ) : ℝ) = x - m := by push_cast; ring
  rw [hA, hB]
  simp only [e]
  rw [Finset.sum_range_succ, sub_add_cancel]
  ring

/-! ### Derivatives of the elementary pieces -/

/-- The derivative of `y ↦ y^w` on `(0, ∞)`, with the value `w x^{w-1}`. -/
lemma hasDerivAt_ofReal_cpow_pos {x : ℝ} (hx : 0 < x) (w : ℂ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ w) (w * (x : ℂ) ^ (w - 1)) x := by
  rcases eq_or_ne w 0 with rfl | hw
  · have hf : (fun y : ℝ => (y : ℂ) ^ (0 : ℂ)) = fun _ => (1 : ℂ) := by
      funext y
      simp
    rw [hf]
    simpa using hasDerivAt_const x (1 : ℂ)
  · exact hasDerivAt_ofReal_cpow_const hx.ne' hw

/-- Smoothness of `y ↦ y^w` on `(0, ∞)`, of every finite order. -/
lemma contDiffOn_ofReal_cpow_pos (n : ℕ) : ∀ w : ℂ,
    ContDiffOn ℝ n (fun y : ℝ => (y : ℂ) ^ w) (Ioi 0) := by
  induction n with
  | zero =>
    intro w
    rw [Nat.cast_zero, contDiffOn_zero]
    intro y hy
    exact (hasDerivAt_ofReal_cpow_pos (mem_Ioi.mp hy) w).continuousAt.continuousWithinAt
  | succ n ih =>
    intro w
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hcast, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun y hy => ((hasDerivAt_ofReal_cpow_pos (mem_Ioi.mp hy) w).differentiableAt).differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have heq : EqOn (deriv fun y : ℝ => (y : ℂ) ^ w) (fun y : ℝ => w * (y : ℂ) ^ (w - 1))
        (Ioi 0) := fun y hy => (hasDerivAt_ofReal_cpow_pos (mem_Ioi.mp hy) w).deriv
    exact ((contDiffOn_const (c := w)).mul (ih (w - 1))).congr heq

/-- The `y`-derivative of `(t + y)^w` at `y = x`, for `t + x > 0`. -/
lemma hasDerivAt_cpow_add_param {t x : ℝ} (ht : 0 < t + x) (w : ℂ) :
    HasDerivAt (fun y : ℝ => ((t : ℂ) + y) ^ w) (w * ((t : ℂ) + x) ^ (w - 1)) x := by
  have hs : ((t : ℂ) + x) ∈ Complex.slitPlane := by
    have h : (((t + x : ℝ)) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr ht
    push_cast at h
    exact h
  have he : HasDerivAt (fun u : ℂ => ((t : ℂ) + u) ^ w) (w * ((t : ℂ) + x) ^ (w - 1) * 1)
      (x : ℂ) :=
    ((hasDerivAt_id (x : ℂ)).const_add (t : ℂ)).cpow_const hs
  simpa using he.comp_ofReal

/-! ### The second-order integral in `x` -/

/-- Measurability of the `x`-derivative integrand of `zetaB2Int`, in `t`. -/
lemma measurable_zetaB2_x_deriv (y : ℝ) (z : ℂ) :
    Measurable (fun t : ℝ => (sawtoothB2 t : ℂ) *
      (-(2 + z) * ((t : ℂ) + y) ^ (-(2 + z) - 1))) := by
  apply Measurable.mul
  · exact Complex.continuous_ofReal.measurable.comp sawtoothB2_measurable
  · apply Measurable.mul measurable_const
    exact Measurable.pow_const (by fun_prop) _

/-- The derivative of `zetaB2Int` in `x`: `∂_x ∫ B_2(t)(t+x)^{-2-z} dt = -(2+z) ∫ B_2(t)(t+x)^{-3-z} dt`,
the second integral being `zetaB2Int (z + 1) x`. -/
theorem hasDerivAt_zetaB2Int_x {z : ℂ} (hz : -1 < z.re) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => zetaB2Int z y) (-(2 + z) * zetaB2Int (z + 1) x) x := by
  have hball : Metric.ball x (x / 2) ∈ 𝓝 x := Metric.ball_mem_nhds x (by linarith)
  have hpos : ∀ y ∈ Metric.ball x (x / 2), x / 2 < y := by
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
    linarith [hy.1]
  set p : ℝ := -(3 + z.re) with hpdef
  have hp1 : p < -1 := by rw [hpdef]; linarith
  have hp0 : p ≤ 0 := by rw [hpdef]; linarith
  have hbound_int : IntegrableOn (fun t : ℝ => (t + x / 2) ^ p) (Ioi 0) :=
    integrableOn_Ioi_add_rpow (by linarith) hp1
  have hF_int : Integrable (fun t : ℝ => (sawtoothB2 t : ℂ) * ((t : ℂ) + x) ^ (-(2 + z)))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine Integrable.bdd_mul (c := 1 / 12) (integrableOn_Ioi_add_cpow hx ?_) ?_ ?_
    · simp; linarith
    · exact (Complex.continuous_ofReal.measurable.comp sawtoothB2_measurable).aestronglyMeasurable
    · exact ae_of_all _ (fun t => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_sawtoothB2_le t)
  have hbound : ∀ y ∈ Metric.ball x (x / 2), ∀ t : ℝ, 0 < t →
      ‖(sawtoothB2 t : ℂ) * (-(2 + z) * ((t : ℂ) + y) ^ (-(2 + z) - 1))‖ ≤
        (1 / 12) * ‖(2 + z)‖ * (t + x / 2) ^ p := by
    intro y hy t ht
    have hy' := hpos y hy
    have hu : 0 < t + y := by linarith
    have hu' : 0 < t + x / 2 := by linarith
    have hcplx : ((t : ℂ) + y) = (((t + y : ℝ)) : ℂ) := by push_cast; ring
    have hnorm : ‖((t : ℂ) + y) ^ (-(2 + z) - 1)‖ = (t + y) ^ p := by
      rw [hcplx, Complex.norm_cpow_eq_rpow_re_of_pos hu, hpdef]
      congr 1
      simp
      ring
    have hmono : (t + y) ^ p ≤ (t + x / 2) ^ p :=
      Real.rpow_le_rpow_of_nonpos hu' (by linarith) hp0
    have hB2 : ‖(sawtoothB2 t : ℂ)‖ ≤ 1 / 12 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_sawtoothB2_le t
    rw [norm_mul, norm_mul, norm_neg, hnorm]
    have hw0 : 0 ≤ (t + y) ^ p := Real.rpow_nonneg hu.le p
    calc ‖(sawtoothB2 t : ℂ)‖ * (‖(2 + z)‖ * (t + y) ^ p)
        ≤ (1 / 12) * (‖(2 + z)‖ * (t + y) ^ p) :=
          mul_le_mul_of_nonneg_right hB2 (by positivity)
      _ ≤ (1 / 12) * (‖(2 + z)‖ * (t + x / 2) ^ p) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
      _ = (1 / 12) * ‖(2 + z)‖ * (t + x / 2) ^ p := by ring
  have hF'_int : Integrable (fun t : ℝ => (1 / 12) * ‖(2 + z)‖ * (t + x / 2) ^ p)
      (volume.restrict (Ioi (0 : ℝ))) :=
    hbound_int.const_mul _
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (x₀ := x) (s := Metric.ball x (x / 2))
    (F := fun y : ℝ => fun t : ℝ => (sawtoothB2 t : ℂ) * ((t : ℂ) + y) ^ (-(2 + z)))
    (F' := fun y : ℝ => fun t : ℝ => (sawtoothB2 t : ℂ) *
      (-(2 + z) * ((t : ℂ) + y) ^ (-(2 + z) - 1)))
    (bound := fun t : ℝ => (1 / 12) * ‖(2 + z)‖ * (t + x / 2) ^ p)
    hball
    (Eventually.of_forall (fun y => (measurable_zetaB2_integrand y z).aestronglyMeasurable))
    (by simpa using hF_int)
    (measurable_zetaB2_x_deriv x z).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro y hy
      exact hbound y hy t ht)
    hF'_int
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro y hy
      have hy' := hpos y hy
      have h := hasDerivAt_cpow_add_param (t := t) (x := y) (by linarith [mem_Ioi.mp ht]) (-(2 + z))
      exact h.const_mul (sawtoothB2 t : ℂ))
  have hval : ∫ t in Ioi (0 : ℝ), (sawtoothB2 t : ℂ) *
      (-(2 + z) * ((t : ℂ) + x) ^ (-(2 + z) - 1)) = -(2 + z) * zetaB2Int (z + 1) x := by
    show _ = -(2 + z) * ∫ t in Ioi (0 : ℝ), (sawtoothB2 t : ℂ) * ((t : ℂ) + x) ^ (-(2 + (z + 1)))
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext t
    rw [show -(2 + (z + 1)) = -(2 + z) - 1 by ring]
    ring
  rw [hval] at hdiff
  exact hdiff.2

/-! ### Smoothness and the derivative identity -/

/-- Smoothness of `x ↦ zetaB2Int z x` on `(0, ∞)` for `Re z > -1`, of every finite order. -/
theorem contDiffOn_zetaB2Int (n : ℕ) : ∀ z : ℂ, -1 < z.re →
    ContDiffOn ℝ n (fun x : ℝ => zetaB2Int z x) (Ioi 0) := by
  induction n with
  | zero =>
    intro z hz
    rw [Nat.cast_zero, contDiffOn_zero]
    intro x hx
    exact (hasDerivAt_zetaB2Int_x hz (mem_Ioi.mp hx)).continuousAt.continuousWithinAt
  | succ n ih =>
    intro z hz
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hcast, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun x hx => (hasDerivAt_zetaB2Int_x hz (mem_Ioi.mp hx)).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have hz1 : -1 < (z + 1).re := by simp; linarith
    have heq : EqOn (deriv fun x : ℝ => zetaB2Int z x)
        (fun x : ℝ => -(2 + z) * zetaB2Int (z + 1) x) (Ioi 0) :=
      fun x hx => (hasDerivAt_zetaB2Int_x hz (mem_Ioi.mp hx)).deriv
    exact ((contDiffOn_const (c := -(2 + z))).mul (ih (z + 1) hz1)).congr heq

/-- Smoothness of `x ↦ zetaRhs z x` on `(0, ∞)` for `Re z > -1`. -/
theorem contDiffOn_zetaRhs {z : ℂ} (hz : -1 < z.re) :
    ContDiffOn ℝ ∞ (fun x : ℝ => zetaRhs z x) (Ioi 0) := by
  have h1 : ∀ w : ℂ, ContDiffOn ℝ ∞ (fun x : ℝ => (x : ℂ) ^ w) (Ioi 0) := fun w =>
    contDiffOn_infty.mpr (fun n => contDiffOn_ofReal_cpow_pos n w)
  have h2 : ContDiffOn ℝ ∞ (fun x : ℝ => zetaB2Int z x) (Ioi 0) :=
    contDiffOn_infty.mpr (fun n => contDiffOn_zetaB2Int n z hz)
  unfold zetaRhs
  exact ((((((h1 (1 - z)).div_const (z - 1)).add ((h1 (-z)).div_const 2)).add
    (((contDiffOn_const (c := z)).mul (h1 (-(1 + z)))).div_const 12)).sub
    ((contDiffOn_const (c := z * (1 + z))).mul h2)))

/-- The derivative of the continued formula in `x`: `∂_x zetaRhs z x = -z zetaRhs (z+1) x`,
for `Re z > -1`, `z ≠ 0`, `z ≠ 1` and `x > 0`. -/
theorem hasDerivAt_zetaRhs {z : ℂ} (hz : -1 < z.re) (hz0 : z ≠ 0) (hz1 : z ≠ 1) {x : ℝ}
    (hx : 0 < x) : HasDerivAt (fun x : ℝ => zetaRhs z x) (-z * zetaRhs (z + 1) x) x := by
  have hne3 : -(1 + z) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have d1 := (hasDerivAt_ofReal_cpow_pos hx (1 - z)).div_const (z - 1)
  have d2 := (hasDerivAt_ofReal_cpow_pos hx (-z)).div_const 2
  have d3 := ((hasDerivAt_ofReal_cpow_pos hx (-(1 + z))).const_mul z).div_const 12
  have d4 := (hasDerivAt_zetaB2Int_x hz hx).const_mul (z * (1 + z))
  have hsum := ((d1.add d2).add d3).sub d4
  unfold zetaRhs
  convert hsum using 1
  have e1 : (1 : ℂ) - (z + 1) = -z := by ring
  have e2 : (z + 1) - 1 = z := by ring
  have e3 : -(z + 1) = -z - 1 := by ring
  have e4 : -(1 + (z + 1)) = -(2 + z) := by ring
  have e5 : (1 : ℂ) - z - 1 = -z := by ring
  have e6 : -(1 + z) - 1 = -(2 + z) := by ring
  have e7 : (1 : ℂ) - z = 1 - z := rfl
  simp only [e1, e2, e3, e4, e5, e6]
  have hzz : (z - 1) ≠ 0 := sub_ne_zero.mpr hz1
  field_simp
  ring

/-- `ζ(z, ·)` is smooth on `(0, ∞)` for `Re z > -1`, `z ≠ 1` (Lemma 2.1). -/
theorem contDiffOn_hurwitzZetaPos {z : ℂ} (hz : -1 < z.re) (hz1 : z ≠ 1) :
    ContDiffOn ℝ ∞ (fun x : ℝ => hurwitzZetaPos z x) (Ioi 0) :=
  (contDiffOn_zetaRhs hz).congr (fun _x hx => hurwitzZetaPos_eq_zetaRhs_of_re_gt (mem_Ioi.mp hx) hz hz1)

/-- The derivative identity `∂_x ζ(z, x) = -z ζ(z + 1, x)` for `x > 0`
(Lemma 2.1). -/
theorem hasDerivAt_hurwitzZetaPos {z : ℂ} (hz : -1 < z.re) (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => hurwitzZetaPos z x) (-z * hurwitzZetaPos (z + 1) x) x := by
  have hz1' : z + 1 ≠ 1 := fun h => hz0 (by linear_combination h)
  have hre1 : -1 < (z + 1).re := by simp; linarith
  have hd := hasDerivAt_zetaRhs hz hz0 hz1 hx
  have hev : (fun x : ℝ => hurwitzZetaPos z x) =ᶠ[𝓝 x] (fun x : ℝ => zetaRhs z x) :=
    Filter.eventually_of_mem (Ioi_mem_nhds hx) (fun y hy =>
      hurwitzZetaPos_eq_zetaRhs_of_re_gt (mem_Ioi.mp hy) hz hz1)
  have h := hd.congr_of_eventuallyEq hev
  rw [hurwitzZetaPos_eq_zetaRhs_of_re_gt hx hre1 hz1']
  exact h

end Riesz1

end
