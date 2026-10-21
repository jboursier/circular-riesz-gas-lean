/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Euler summation for the Hurwitz zeta function

The error between a power and its integral on a unit interval has a summable
bound locally uniform in the exponent on `0 < re z`. Its sum identifies the
regularized partial sums with Mathlib's meromorphic continuation, by analytic
uniqueness. This proves the first line of equation (2.11) in
Lemma 2.1.
-/

public section

open Complex Set MeasureTheory Filter
open scoped Topology
namespace Riesz1

/-- The unit-interval error in Euler summation, starting at `n + 1`. -/
@[expose] noncomputable def eulerTerm (x : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) + 1 + x) ^ (-z) -
    (((n : ℂ) + 2) ^ (1 - z) - ((n : ℂ) + 1) ^ (1 - z)) / (1 - z)

lemma eulerTerm_eq_integral (x : ℝ) (z : ℂ) (hz : z ≠ 1) (n : ℕ) :
    eulerTerm x z n = ∫ t : ℝ in (n : ℝ) + 1..(n : ℝ) + 2,
      (((n : ℂ) + 1 + x) ^ (-z) - (t : ℂ) ^ (-z)) := by
  have hpos : (0 : ℝ) ∉ uIcc ((n : ℝ) + 1) ((n : ℝ) + 2) := by
    rw [uIcc_of_le (by linarith)]
    simp only [mem_Icc, not_and]
    intro h
    linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_cpow (Or.inr hpos)),
    integral_cpow (Or.inr ⟨by intro h; apply hz; linear_combination -h, hpos⟩)]
  rw [intervalIntegral.integral_const]
  have hlen : (n : ℝ) + 2 - ((n : ℝ) + 1) = 1 := by ring
  rw [hlen, one_smul]
  simp only [eulerTerm, neg_add_eq_sub, ofReal_add, ofReal_natCast, ofReal_one,
    ofReal_ofNat]

lemma norm_cpow_sub_le (z : ℂ) (hz : 0 < z.re) (A u v : ℝ) (hA : 0 < A)
    (hu : u ∈ Icc A (A + 1)) (hv : v ∈ Icc A (A + 1)) :
    ‖(v : ℂ) ^ (-z) - (u : ℂ) ^ (-z)‖ ≤ ‖z‖ * A ^ (-z.re - 1) := by
  have hz0 : -z ≠ 0 := neg_ne_zero.mpr (by intro h; simp [h] at hz)
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (𝕜 := ℝ) (C := ‖z‖ * A ^ (-z.re - 1)) (f := fun t : ℝ => (t : ℂ) ^ (-z))
    (fun t ht => ((hasDerivAt_ofReal_cpow_const
      (ne_of_gt (hA.trans_le ht.1)) hz0).hasFDerivAt.hasFDerivWithinAt))
    (fun t ht => ?_) (convex_Icc A (A + 1)) hu hv
  · have hnorm : ‖v - u‖ ≤ 1 := by rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨by linarith [hv.1, hu.2], by linarith [hu.1, hv.2]⟩
    exact h.trans (mul_le_of_le_one_right (by positivity) hnorm)
  · rw [ContinuousLinearMap.norm_toSpanSingleton, norm_mul,
      norm_neg, norm_cpow_eq_rpow_re_of_pos (hA.trans_le ht.1)]
    simp only [sub_re, neg_re, one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hA ht.1 (by linarith)) (norm_nonneg _)

lemma norm_eulerTerm_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (z : ℂ)
    (hz : 0 < z.re) (hz1 : z ≠ 1) (n : ℕ) :
    ‖eulerTerm x z n‖ ≤ ‖z‖ * ((n : ℝ) + 1) ^ (-z.re - 1) := by
  rw [eulerTerm_eq_integral x z hz1 n]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (n : ℝ) + 1) (b := (n : ℝ) + 2)
    (C := ‖z‖ * ((n : ℝ) + 1) ^ (-z.re - 1)) (f := fun t : ℝ =>
      ((n : ℂ) + 1 + x) ^ (-z) - (t : ℂ) ^ (-z)) ?_
  · simpa only [show (n : ℝ) + 2 - ((n : ℝ) + 1) = 1 by ring, abs_one, mul_one] using h
  · intro t ht
    rw [uIoc_of_le (by linarith)] at ht
    have hb := norm_cpow_sub_le z hz ((n : ℝ) + 1) t ((n : ℝ) + 1 + x)
      (by positivity) ⟨ht.1.le, by linarith [ht.2]⟩ ⟨by linarith, by linarith⟩
    simpa only [ofReal_add, ofReal_natCast, ofReal_one] using hb

lemma summable_eulerTerm (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (z : ℂ)
    (hz : 0 < z.re) (hz1 : z ≠ 1) : Summable (eulerTerm x z) := by
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => ‖z‖ * ((n : ℝ) + 1) ^ (-z.re - 1))
  · apply Summable.mul_left
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr
        (Real.summable_nat_rpow.mpr (show -z.re - 1 < -1 by linarith))
  · exact norm_eulerTerm_le x hx0 hx1 z hz hz1

lemma differentiableAt_eulerTerm (x : ℝ) (hx0 : 0 ≤ x) (n : ℕ) (z : ℂ)
    (hz1 : z ≠ 1) : DifferentiableAt ℂ (fun w => eulerTerm x w n) z := by
  unfold eulerTerm
  have h1 : (n : ℂ) + 1 + x ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    simp only [add_re, natCast_re, one_re, ofReal_re, zero_re]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have h2 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (show (n : ℝ) + 1 ≠ 0 by positivity)
  have h3 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (show (n : ℝ) + 2 ≠ 0 by positivity)
  exact ((differentiableAt_id.neg).const_cpow (Or.inl h1)).sub
    ((((differentiableAt_const 1).sub differentiableAt_id).const_cpow (Or.inl h3)).sub
      (((differentiableAt_const 1).sub differentiableAt_id).const_cpow (Or.inl h2)) |>.div
        ((differentiableAt_const 1).sub differentiableAt_id) (sub_ne_zero.mpr (Ne.symm hz1)))

lemma differentiableAt_tsum_eulerTerm (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (z : ℂ) (hz : 0 < z.re) (hz1 : z ≠ 1) :
    DifferentiableAt ℂ (fun w => ∑' n, eulerTerm x w n) z := by
  let σ := z.re / 2
  let R := ‖z‖ + 1
  let U := {w : ℂ | σ < w.re ∧ ‖w‖ < R ∧ w ≠ 1}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter
      ((isOpen_lt continuous_norm continuous_const).inter isOpen_compl_singleton)
  have hzU : z ∈ U := ⟨by dsimp [σ]; linarith, by dsimp [R]; linarith, hz1⟩
  have hs : Summable (fun n : ℕ => R * ((n : ℝ) + 1) ^ (-σ - 1)) := by
    apply Summable.mul_left
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr
        (Real.summable_nat_rpow.mpr (show -σ - 1 < -1 by dsimp [σ]; linarith))
  apply (differentiableOn_tsum_of_summable_norm hs
    (fun n w hw => (differentiableAt_eulerTerm x hx0 n w hw.2.2).differentiableWithinAt)
    hU ?_).differentiableAt (hU.mem_nhds hzU)
  intro n w hw
  have hw0 : 0 < w.re := by dsimp [U, σ] at hw; linarith [hw.1]
  apply (norm_eulerTerm_le x hx0 hx1 w hw0 hw.2.2 n).trans
  apply mul_le_mul hw.2.1.le
    (Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n] : 1 ≤ (n : ℝ) + 1) (by linarith [hw.1]))
    (by positivity) (by dsimp [R]; positivity)

lemma tendsto_natCast_cpow_zero (w : ℂ) (hw : w.re < 0) :
    Tendsto (fun n : ℕ => (n : ℂ) ^ w) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (tendsto_rpow_neg_atTop (neg_pos.mpr hw)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  dsimp only [Function.comp_def] at h
  simpa only [neg_neg] using h.congr (fun n => by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
      norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n) (ne_of_lt hw)]
    simp only [neg_neg])

lemma sum_eulerTerm (x : ℝ) (z : ℂ) (M : ℕ) :
    ∑ n ∈ Finset.range M, eulerTerm x z n =
      (∑ n ∈ Finset.range (M + 1), ((n : ℂ) + x) ^ (-z)) - (x : ℂ) ^ (-z) -
        (((M : ℂ) + 1) ^ (1 - z) - 1) / (1 - z) := by
  induction M with
  | zero => simp
  | succ M h =>
    rw [Finset.sum_range_succ, h]
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [eulerTerm, Nat.cast_add, Nat.cast_one]
    rw [show (M : ℂ) + 1 + 1 = (M : ℂ) + 2 by ring]
    ring

lemma tendsto_euler_regularized (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (z : ℂ)
    (hz : 0 < z.re) (hz1 : z ≠ 1) :
    Tendsto (fun M : ℕ => (∑ n ∈ Finset.range (M + 1), ((n : ℂ) + x) ^ (-z)) -
      ((M : ℂ) + 1) ^ (1 - z) / (1 - z)) atTop
      (𝓝 ((x : ℂ) ^ (-z) + ∑' n, eulerTerm x z n - 1 / (1 - z))) := by
  have h := (((summable_eulerTerm x hx0 hx1 z hz hz1).hasSum.tendsto_sum_nat).const_add
    ((x : ℂ) ^ (-z))).sub_const (1 / (1 - z))
  apply h.congr
  intro M
  rw [sum_eulerTerm]
  ring

lemma euler_eq_hurwitzZeta_of_one_lt (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (z : ℂ) (hz : 1 < z.re) :
    (x : ℂ) ^ (-z) + ∑' n, eulerTerm x z n - 1 / (1 - z) =
      HurwitzZeta.hurwitzZeta (x : UnitAddCircle) z := by
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  have hsum := ((HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ⟨hx0, hx1⟩ hz).tendsto_sum_nat).comp
    (tendsto_add_atTop_nat 1)
  have hzero := ((tendsto_natCast_cpow_zero (1 - z) (by simpa using hz)).comp
    (tendsto_add_atTop_nat 1)).div_const (1 - z)
  have hlim := hsum.sub hzero
  simp only [Function.comp_def, Nat.cast_add, Nat.cast_one, div_eq_mul_inv,
    one_mul, ← cpow_neg, zero_mul, sub_zero] at hlim
  exact tendsto_nhds_unique (tendsto_euler_regularized x hx0 hx1 z (by linarith) hz1) (by simpa only [div_eq_mul_inv] using hlim)

lemma euler_eq_hurwitzZeta (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (z : ℂ) (hz : 0 < z.re) (hz1 : z ≠ 1) :
    (x : ℂ) ^ (-z) + ∑' n, eulerTerm x z n - 1 / (1 - z) =
      HurwitzZeta.hurwitzZeta (x : UnitAddCircle) z := by
  let c : ℝ := min (z.re / 2) (1 / 2)
  have hc0 : 0 < c := lt_min (by linarith) (by norm_num)
  have hc1 : c < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hcz : c ≤ z.re := (min_le_left _ _).trans (by linarith)
  let f : ℂ → ℂ := fun w => (↑(max c w.re) : ℂ) + w.im * I
  have hf : Continuous f := by dsimp [f]; fun_prop
  let U : Set ℂ := f '' {1}ᶜ
  have hU : IsPreconnected U :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected.image
      f hf.continuousOn
  have hmem (w : ℂ) (hw : w ∈ U) : 0 < w.re ∧ w ≠ 1 := by
    obtain ⟨v, hv, rfl⟩ := hw
    constructor
    · simpa [f] using hc0.trans_le (le_max_left c v.re)
    · intro heq
      have hre := congrArg Complex.re heq
      have him := congrArg Complex.im heq
      simp only [f, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        zero_mul, mul_zero, sub_self, add_zero, one_re] at hre
      simp only [f, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
        mul_zero, add_zero, zero_add, mul_one, one_im] at him
      rcases le_total c v.re with h | h
      · rw [max_eq_right h] at hre
        exact hv (Complex.ext hre him)
      · rw [max_eq_left h] at hre
        exact hc1.ne hre
  have hzU : z ∈ U := by
    refine ⟨z, hz1, ?_⟩
    apply Complex.ext <;> simp [f, max_eq_right hcz]
  have h2U : (2 : ℂ) ∈ U := by
    refine ⟨2, by norm_num, ?_⟩
    apply Complex.ext <;> simp [f, max_eq_right (by linarith : c ≤ 2)]
  let V := {w : ℂ | 0 < w.re ∧ w ≠ 1}
  have hV : IsOpen V := (isOpen_lt continuous_const continuous_re).inter isOpen_compl_singleton
  have hUV : U ⊆ V := hmem
  have hleftD : DifferentiableOn ℂ
      (fun w => (x : ℂ) ^ (-w) + ∑' n, eulerTerm x w n - 1 / (1 - w)) V := by
    intro w hw
    exact (((differentiableAt_id.neg.const_cpow (Or.inl (ofReal_ne_zero.mpr hx0.ne'))).add
      (differentiableAt_tsum_eulerTerm x hx0.le hx1 w hw.1 hw.2)).sub
      ((differentiableAt_const 1).div ((differentiableAt_const 1).sub differentiableAt_id)
        (sub_ne_zero.mpr hw.2.symm))).differentiableWithinAt
  have hleft := (hleftD.analyticOnNhd hV).mono hUV
  have hrightD : DifferentiableOn ℂ (HurwitzZeta.hurwitzZeta (x : UnitAddCircle)) V :=
    fun w hw => (HurwitzZeta.differentiableAt_hurwitzZeta _ hw.2).differentiableWithinAt
  have hright := (hrightD.analyticOnNhd hV).mono hUV
  apply hleft.eqOn_of_preconnected_of_eventuallyEq hright hU h2U _ hzU
  apply eventuallyEq_of_mem
    ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num : 1 < (2 : ℂ).re))
  exact fun w hw => euler_eq_hurwitzZeta_of_one_lt x hx0.le hx1 w hw

/-- Euler summation for the Hurwitz zeta function (equation (2.11), first line). -/
theorem tendsto_hurwitzZeta_sub (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (z : ℂ)
    (hz : 0 < z.re) (hz1 : z ≠ 1) :
    Tendsto (fun M : ℕ => (∑ n ∈ Finset.range (M + 1), ((n : ℂ) + x) ^ (-z)) -
      (M : ℂ) ^ (1 - z) / (1 - z)) atTop (𝓝 (HurwitzZeta.hurwitzZeta (x : UnitAddCircle) z)) := by
  have hreg := (tendsto_euler_regularized x hx0.le hx1 z hz hz1).comp (tendsto_add_atTop_nat 1)
  rw [euler_eq_hurwitzZeta x hx0 hx1 z hz hz1] at hreg
  have hzero := ((tendsto_natCast_cpow_zero (-z) (by simpa using hz)).comp
    (tendsto_add_atTop_nat 1)).sub
    ((summable_eulerTerm 0 (by rfl) zero_le_one z hz hz1).tendsto_atTop_zero)
  have hlim := hreg.add hzero
  simp only [sub_zero, add_zero] at hlim
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply hlim.congr
  intro M
  simp only [Function.comp_def, eulerTerm, Nat.cast_add, Nat.cast_one, ofReal_zero, add_zero]
  rw [show (M : ℂ) + 1 + 1 = (M : ℂ) + 2 by ring]
  ring

end Riesz1
