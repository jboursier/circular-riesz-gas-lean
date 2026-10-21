/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.OscillatoryRegularTail

/-!
# Oscillatory estimates on a central interval and two regular tails

Reflection transfers the positive-tail estimate to the negative tail. Splitting the
integral then gives a bound independent of the two remote endpoints, as needed in
the compact-profile Fourier argument.
-/

public section

open MeasureTheory Set intervalIntegral

namespace Riesz1.PuncturedDerivative

/-- The reflected regular-tail estimate, with constants independent of the far endpoint. -/
theorem norm_oscillatory_negative_tail_le {q : ℝ → ℝ} {R z M C e : ℝ}
    (hR : 0 < R) (hRz : R ≤ z) (hC : 0 ≤ C) (he : e < -1)
    (hq : ∀ t ∈ Icc (-z) (-R), DifferentiableAt ℝ q t)
    (hM : ∀ t ∈ Icc (-z) (-R), |q t| ≤ M)
    (hbound : ∀ t ∈ Icc (-z) (-R), |deriv q t| ≤ C * |t| ^ e)
    {χ : ℝ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hχ : ∀ t : ℝ, HasDerivAt χ (c * χ t) t) (hn : ∀ t : ℝ, ‖χ t‖ = 1) :
    ‖∫ t in (-z)..(-R), (q t : ℂ) * χ t‖ ≤
      (2 * M + C / (-e - 1) * R ^ (e + 1)) / ‖c‖ := by
  have hm (t : ℝ) (ht : t ∈ Icc R z) : -t ∈ Icc (-z) (-R) :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hd (t : ℝ) (ht : t ∈ Icc R z) :
      HasDerivAt (fun u => q (-u)) (-deriv q (-t)) t := by
    simpa only [Function.comp_def, mul_neg, mul_one] using
      ((hq (-t) (hm t ht)).hasDerivAt).comp t (hasDerivAt_neg t)
  have hh := norm_oscillatory_regular_tail_le hR hRz hC he
    (q := fun t => q (-t)) (fun t ht => (hd t ht).differentiableAt)
    (fun t ht => hM (-t) (hm t ht))
    (fun t ht => by
      rw [(hd t ht).deriv, abs_neg]
      simpa only [abs_neg, abs_of_pos (hR.trans_le ht.1)] using hbound (-t) (hm t ht))
    (χ := fun t => χ (-t)) (c := -c) (neg_ne_zero.mpr hc)
    (fun t => by
      simpa only [Function.comp_def, neg_one_smul, neg_mul] using
        (hχ (-t)).scomp t (hasDerivAt_neg t))
    (fun t => hn (-t))
  simp only [norm_neg] at hh
  rw [← integral_comp_neg (fun t => (q t : ℂ) * χ t)]
  exact hh

/-- A central oscillatory bound and integrable derivative tails give one bound on the
whole symmetric interval. All constants precede its remote endpoint. -/
theorem norm_oscillatory_two_tails_le {q : ℝ → ℝ} {R z M C e g K W : ℝ}
    (hR : 0 < R) (hRz : R ≤ z) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (he : e < -1) (hg : -1 ≤ g) (hW : 1 ≤ W)
    (hi : IntervalIntegrable q volume (-R) R)
    (hq : ∀ t : ℝ, R ≤ |t| → |t| ≤ z → DifferentiableAt ℝ q t)
    (hb : ∀ t : ℝ, R ≤ |t| → |t| ≤ z → |q t| ≤ M)
    (hbound : ∀ t : ℝ, R ≤ |t| → |t| ≤ z → |deriv q t| ≤ C * |t| ^ e)
    {χ : ℝ → ℂ} {c : ℂ} (hc : W ≤ ‖c‖)
    (hχ : ∀ t : ℝ, HasDerivAt χ (c * χ t) t) (hn : ∀ t : ℝ, ‖χ t‖ = 1)
    (hcenter : ‖∫ t in (-R)..R, (q t : ℂ) * χ t‖ ≤ K * ‖c‖ ^ g) :
    ‖∫ t in (-z)..z, (q t : ℂ) * χ t‖ ≤
      (K + 2 * (2 * M + C / (-e - 1) * R ^ (e + 1))) * ‖c‖ ^ g := by
  have hc1 : 1 ≤ ‖c‖ := hW.trans hc
  have hc0 : c ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hc1)
  have hχc : Continuous χ := continuous_iff_continuousAt.mpr fun t => (hχ t).continuousAt
  have hp (t : ℝ) (ht : t ∈ Icc R z) : R ≤ |t| ∧ |t| ≤ z := by
    rw [abs_of_pos (hR.trans_le ht.1)]
    exact ht
  have hm (t : ℝ) (ht : t ∈ Icc (-z) (-R)) : R ≤ |t| ∧ |t| ≤ z := by
    rw [abs_of_neg (by linarith [ht.2] : t < 0)]
    constructor <;> linarith [ht.1, ht.2]
  have hpos := norm_oscillatory_regular_tail_le hR hRz hC he
    (fun t ht => hq t (hp t ht).1 (hp t ht).2)
    (fun t ht => hb t (hp t ht).1 (hp t ht).2)
    (fun t ht => by
      simpa only [abs_of_pos (hR.trans_le ht.1)] using
        hbound t (hp t ht).1 (hp t ht).2) hc0 hχ hn
  have hneg := norm_oscillatory_negative_tail_le hR hRz hC he
    (fun t ht => hq t (hm t ht).1 (hm t ht).2)
    (fun t ht => hb t (hm t ht).1 (hm t ht).2)
    (fun t ht => hbound t (hm t ht).1 (hm t ht).2) hc0 hχ hn
  have hip : IntervalIntegrable q volume R z := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hRz]
    exact fun t ht => (hq t (hp t ht).1 (hp t ht).2).continuousAt.continuousWithinAt
  have hin : IntervalIntegrable q volume (-z) (-R) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (neg_le_neg hRz)]
    exact fun t ht => (hq t (hm t ht).1 (hm t ht).2).continuousAt.continuousWithinAt
  have hic : IntervalIntegrable (fun t => (q t : ℂ) * χ t) volume (-R) R :=
    (show IntervalIntegrable (fun t => (q t : ℂ)) volume (-R) R from
      ⟨Complex.ofRealCLM.integrable_comp hi.1, Complex.ofRealCLM.integrable_comp hi.2⟩).mul_continuousOn hχc.continuousOn
  have hipc : IntervalIntegrable (fun t => (q t : ℂ) * χ t) volume R z :=
    (show IntervalIntegrable (fun t => (q t : ℂ)) volume R z from
      ⟨Complex.ofRealCLM.integrable_comp hip.1, Complex.ofRealCLM.integrable_comp hip.2⟩).mul_continuousOn hχc.continuousOn
  have hinc : IntervalIntegrable (fun t => (q t : ℂ) * χ t) volume (-z) (-R) :=
    (show IntervalIntegrable (fun t => (q t : ℂ)) volume (-z) (-R) from
      ⟨Complex.ofRealCLM.integrable_comp hin.1, Complex.ofRealCLM.integrable_comp hin.2⟩).mul_continuousOn hχc.continuousOn
  rw [← integral_add_adjacent_intervals (hinc.trans hic) hipc,
    ← integral_add_adjacent_intervals hinc hic]
  have hpow : ‖c‖⁻¹ ≤ ‖c‖ ^ g := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hc1 hg
  have hA : 0 ≤ 2 * M + C / (-e - 1) * R ^ (e + 1) := add_nonneg (mul_nonneg (by norm_num) hM)
    (mul_nonneg (div_nonneg hC (by linarith)) (Real.rpow_nonneg hR.le _))
  have hlarge := mul_le_mul_of_nonneg_left hpow hA
  rw [div_eq_mul_inv] at hpos hneg
  have htriangle := (norm_add_le
    ((∫ t in (-z)..(-R), (q t : ℂ) * χ t) + ∫ t in (-R)..R, (q t : ℂ) * χ t)
    (∫ t in R..z, (q t : ℂ) * χ t)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  nlinarith

end Riesz1.PuncturedDerivative
