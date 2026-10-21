/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Sanity.Basic

/-!
# Analytic sanity checks

Two analytic checks. The periodic zeta combination `periodicZeta` is positive on `(0,1)`,
by the Hurwitz functional equation and a convergent cosine series. An open arc indicator
lies in the fractional Sobolev space `CircleSobolev`, by an explicit computation of its
Fourier coefficients.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators Real

namespace Riesz1

/-! ### Positivity of the periodic zeta combination -/

/-- The Gamma and power factors of the functional equation at `1 + s` are real.
The resulting constant is negative by `kr_neg`. -/
private lemma kr_cast (s : RieszExponent) :
    2 * (2 * (Real.pi : ℂ)) ^ (-(1 + (s.val : ℂ))) * Complex.Gamma (1 + (s.val : ℂ)) *
        Complex.cos (Real.pi * (1 + (s.val : ℂ)) / 2) =
      ((2 * (2 * Real.pi) ^ (-(1 + s.val)) * Real.Gamma (1 + s.val) *
        Real.cos (Real.pi * (1 + s.val) / 2) : ℝ) : ℂ) := by
  have hpos : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  push_cast
  rw [Complex.ofReal_cpow hpos, ← Complex.Gamma_ofReal]
  push_cast
  ring

/-- The real constant of the functional equation is negative. -/
private lemma kr_neg (s : RieszExponent) :
    2 * (2 * Real.pi) ^ (-(1 + s.val)) * Real.Gamma (1 + s.val) *
      Real.cos (Real.pi * (1 + s.val) / 2) < 0 := by
  have hs0 := s.property.1
  have hs1 := s.property.2
  have hcos : Real.cos (Real.pi * (1 + s.val) / 2) < 0 := by
    have h : Real.pi * (1 + s.val) / 2 = Real.pi * s.val / 2 + Real.pi / 2 := by ring
    rw [h, Real.cos_add_pi_div_two]
    have hsin : 0 < Real.sin (Real.pi * s.val / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (div_pos (mul_pos Real.pi_pos hs0) two_pos)
        (by nlinarith [Real.pi_pos])
    linarith
  have hpos : 0 < 2 * (2 * Real.pi) ^ (-(1 + s.val)) * Real.Gamma (1 + s.val) :=
    mul_pos (mul_pos two_pos (Real.rpow_pos_of_pos (by positivity) _))
      (Real.Gamma_pos_of_pos (by linarith))
  exact mul_neg_of_pos_of_neg hpos hcos

/-- The Hurwitz functional equation at `1 + s`, written with the real constant of `kr_neg`.
Every point of the circle is covered. -/
private lemma hurwitzZetaEven_neg_eq (s : RieszExponent) (a : UnitAddCircle) :
    HurwitzZeta.hurwitzZetaEven a (-(s.val : ℂ)) =
      ((2 * (2 * Real.pi) ^ (-(1 + s.val)) * Real.Gamma (1 + s.val) *
        Real.cos (Real.pi * (1 + s.val) / 2) : ℝ) : ℂ) *
        HurwitzZeta.cosZeta a (1 + (s.val : ℂ)) := by
  have hs := s.property.1
  have hne : ∀ n : ℕ, (1 + (s.val : ℂ)) ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    simp at hre
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs' : a ≠ 0 ∨ (1 + (s.val : ℂ)) ≠ 1 := by
    refine Or.inr fun h => ?_
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  rw [show -(s.val : ℂ) = 1 - (1 + (s.val : ℂ)) by ring,
    HurwitzZeta.hurwitzZetaEven_one_sub a hne hs', kr_cast]

/-- The cosine series of `cosZeta` at `1 + s` is a sum of real terms. -/
private lemma cosZeta_sub_hasSum (s : RieszExponent) (t : ℝ) :
    HasSum (fun n : ℕ =>
        ((-((1 - Real.cos (2 * Real.pi * t * n)) / (n : ℝ) ^ (1 + s.val)) : ℝ) : ℂ))
      (HurwitzZeta.cosZeta (t : UnitAddCircle) (1 + (s.val : ℂ)) -
        HurwitzZeta.cosZeta (0 : UnitAddCircle) (1 + (s.val : ℂ))) := by
  have hre : 1 < (1 + (s.val : ℂ)).re := by
    have := s.property.1
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    linarith
  refine ((HurwitzZeta.hasSum_nat_cosZeta t hre).sub
    (HurwitzZeta.hasSum_nat_cosZeta 0 hre)).congr_fun fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [show (n : ℂ) ^ (1 + (s.val : ℂ)) = (((n : ℝ) ^ (1 + s.val) : ℝ) : ℂ) by
      simp [Complex.ofReal_cpow hn'.le]]
    simp only [mul_zero, zero_mul, Real.cos_zero, Complex.ofReal_one]
    push_cast
    ring

/-- The real kernel terms are nonnegative and summable. -/
private lemma periodic_sum_summable (s : RieszExponent) (t : ℝ) :
    Summable (fun n : ℕ => (1 - Real.cos (2 * Real.pi * t * n)) / (n : ℝ) ^ (1 + s.val)) := by
  have hs := s.property.1
  have hbound : Summable (fun n : ℕ => 2 * (n : ℝ) ^ (-(1 + s.val))) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left 2
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbound
  · exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, mul_zero, Real.cos_zero, sub_self, zero_div]
      rw [Real.zero_rpow (ne_of_lt (by linarith : -(1 + s.val) < 0)), mul_zero]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hP : 0 ≤ (n : ℝ) ^ (1 + s.val) := Real.rpow_nonneg hn'.le _
      rw [Real.rpow_neg hn'.le, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (by linarith [Real.neg_one_le_cos (2 * Real.pi * t * n)]) (inv_nonneg.mpr hP)

/-- The cosine series difference is strictly positive for `0 < t < 1`: its first term
`1 - cos (2 π t)` is positive. -/
private lemma periodic_sum_pos (s : RieszExponent) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < ∑' n : ℕ, (1 - Real.cos (2 * Real.pi * t * n)) / (n : ℝ) ^ (1 + s.val) := by
  have hcos1 : Real.cos (2 * Real.pi * t) < 1 := by
    refine lt_of_le_of_ne (Real.cos_le_one _) fun h => ?_
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp h
    have htk : t = k := by
      have h2 : 2 * Real.pi * t = 2 * Real.pi * k := by linarith
      exact mul_left_cancel₀ (by positivity) h2
    have h3 : (0 : ℤ) < k := by rw [htk] at ht0; exact_mod_cast ht0
    have h4 : k < 1 := by rw [htk] at ht1; exact_mod_cast ht1
    omega
  refine (periodic_sum_summable s t).tsum_pos (fun n => ?_) 1 ?_
  · exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · simpa using sub_pos.mpr hcos1

/-- The periodic zeta combination is strictly positive on `(0,1)`. -/
theorem periodicZeta_pos (s : RieszExponent) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < periodicZeta s (t : UnitAddCircle) := by
  have hS := periodic_sum_pos s t ht0 ht1
  have hdiff : HurwitzZeta.cosZeta (t : UnitAddCircle) (1 + (s.val : ℂ)) -
      HurwitzZeta.cosZeta (0 : UnitAddCircle) (1 + (s.val : ℂ)) =
      ((-(∑' n : ℕ, (1 - Real.cos (2 * Real.pi * t * n)) / (n : ℝ) ^ (1 + s.val)) : ℝ) : ℂ) :=
    (cosZeta_sub_hasSum s t).unique
      (Complex.hasSum_ofReal.mpr (periodic_sum_summable s t).hasSum.neg)
  unfold periodicZeta
  rw [hurwitzZetaEven_neg_eq s, hurwitzZetaEven_neg_eq s, ← Complex.sub_re, ← mul_sub, hdiff,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  have h := mul_pos (neg_pos.mpr (kr_neg s)) hS
  nlinarith [h]

/-! ### Fractional Sobolev membership of an open arc indicator -/

/-- Distance on the unit circle between two real points at most half a period apart. -/
private lemma dist_coe_unit_eq (x y : ℝ) (h : |x - y| ≤ 1 / 2) :
    dist (x : UnitAddCircle) (y : UnitAddCircle) = |x - y| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).mpr (by simpa using h)

/-- The Fourier coefficients of an open arc indicator satisfy `|c_k| ≤ 1 / (π |k|)`
for `k ≠ 0`. The proof integrates the exponential over the arc. -/
private lemma arc_fourierCoeff_norm_le (center : UnitAddCircle) (a : ℝ) (ha0 : 0 < a)
    (ha1 : a < 1 / 2) (k : ℤ) (hk : k ≠ 0) :
    ‖fourierCoeff (fun x => (arcIndicator center a x : ℂ)) k‖ ≤
      1 / (Real.pi * |(k : ℝ)|) := by
  obtain ⟨cr, rfl⟩ := QuotientAddGroup.mk_surjective center
  have hk' : (0 : ℝ) < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
  have hpi := Real.pi_pos
  set c : ℂ := ((-(2 * Real.pi * k) : ℝ) : ℂ) * Complex.I with hc
  have hcnorm : ‖c‖ = 2 * Real.pi * |(k : ℝ)| := by
    simp [hc, abs_of_pos hpi]
  have hc0 : c ≠ 0 := fun h => by
    rw [h, norm_zero] at hcnorm
    have := mul_pos (mul_pos two_pos hpi) hk'
    linarith
  have hfour : ∀ x : ℝ, fourier (-k) (x : UnitAddCircle) = Complex.exp (c * x) := by
    intro x
    rw [fourier_coe_apply, hc]
    congr 1
    push_cast
    ring
  have hE : ∀ y : ℝ, ‖Complex.exp (c * y)‖ = 1 := by
    intro y
    rw [show c * (y : ℂ) = (((-(2 * Real.pi * k) * y : ℝ)) : ℂ) * Complex.I by
      rw [hc]; push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  -- The arc is the interval `(cr - a, cr + a)` inside the window `[cr - 1/2, cr + 1/2]`,
  -- so the window integral reduces to the integral over the arc.
  have hsplit : ∫ x in (cr - 1 / 2)..(cr - 1 / 2 + 1), Complex.exp (c * x) *
      (arcIndicator (cr : UnitAddCircle) a (x : UnitAddCircle) : ℂ) =
      ∫ x in (cr - a)..(cr + a), Complex.exp (c * x) := by
    rw [show cr - 1 / 2 + 1 = cr + 1 / 2 by ring]
    have hcongr : ∫ x in (cr - 1 / 2)..(cr + 1 / 2), Complex.exp (c * x) *
        (arcIndicator (cr : UnitAddCircle) a (x : UnitAddCircle) : ℂ) =
        ∫ x in (cr - 1 / 2)..(cr + 1 / 2),
          (Set.Ioo (cr - a) (cr + a)).indicator (fun y : ℝ => Complex.exp (c * y)) x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      have hd := dist_coe_unit_eq x cr (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
      by_cases hin : x ∈ Set.Ioo (cr - a) (cr + a)
      · have hlt : dist (x : UnitAddCircle) (cr : UnitAddCircle) < a := by
          rw [hd, abs_lt]; constructor <;> linarith [hin.1, hin.2]
        rw [Set.indicator_of_mem hin]
        simp [arcIndicator, hlt]
      · have hge : ¬ dist (x : UnitAddCircle) (cr : UnitAddCircle) < a := by
          intro hlt
          rw [hd, abs_lt] at hlt
          exact hin ⟨by linarith [hlt.1], by linarith [hlt.2]⟩
        rw [Set.indicator_of_notMem hin]
        simp [arcIndicator, hge]
    have hAB : cr - 1 / 2 ≤ cr + 1 / 2 := by linarith
    have hCD : cr - a ≤ cr + a := by linarith
    have hsub : Set.Ioo (cr - a) (cr + a) ⊆ Set.Ioc (cr - 1 / 2) (cr + 1 / 2) :=
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [hcongr, intervalIntegral.integral_of_le hAB, MeasureTheory.setIntegral_indicator
      measurableSet_Ioo, Set.inter_eq_right.mpr hsub,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hCD]
  rw [fourierCoeff_eq_intervalIntegral _ k (cr - 1 / 2)]
  simp only [div_one, one_smul, smul_eq_mul, hfour]
  rw [hsplit, integral_exp_mul_complex hc0]
  have hbound : ‖(Complex.exp (c * ((cr + a : ℝ) : ℂ)) -
      Complex.exp (c * ((cr - a : ℝ) : ℂ))) / c‖ ≤ 2 / (2 * Real.pi * |(k : ℝ)|) := by
    rw [norm_div, hcnorm]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact (norm_sub_le _ _).trans (by rw [hE, hE]; norm_num)
  refine hbound.trans (le_of_eq ?_)
  field_simp

/-- An open arc indicator is in the fractional Sobolev space of order `(1 - s) / 2`.
The `L²` part is `arcIndicator_memLp`. The seminorm is finite because the coefficients
decay like `|k|^(-1)` and `|k|^(1 - s) |k|^(-2)` is summable. -/
theorem arcIndicator_circleSobolev (s : RieszExponent) (center : UnitAddCircle) (a : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    CircleSobolev ((1 - s.val) / 2) (fun x => (arcIndicator center a x : ℂ)) := by
  refine ⟨arcIndicator_memLp center a, ?_⟩
  have h2r : 2 * ((1 - s.val) / 2) = 1 - s.val := by ring
  have hs := s.property.1
  have hsum : Summable (fun k : ℤ => |(k : ℝ)| ^ (-(1 + s.val)) / Real.pi ^ 2) :=
    (Real.summable_abs_int_rpow (by linarith : 1 < 1 + s.val)).div_const _
  have hterm : ∀ k : ℤ, (if k = 0 then (0 : ℝ≥0∞) else ENNReal.ofReal
      (|(k : ℝ)| ^ (2 * ((1 - s.val) / 2)) *
        ‖fourierCoeff (fun x => (arcIndicator center a x : ℂ)) k‖ ^ 2)) ≤
      ENNReal.ofReal (|(k : ℝ)| ^ (-(1 + s.val)) / Real.pi ^ 2) := by
    intro k
    by_cases hk : k = 0
    · simp [hk]
    · simp only [hk, ↓reduceIte, h2r]
      refine ENNReal.ofReal_le_ofReal ?_
      have hk' : (0 : ℝ) < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
      have hnorm := arc_fourierCoeff_norm_le center a ha0 ha1 k hk
      have hsq : ‖fourierCoeff (fun x => (arcIndicator center a x : ℂ)) k‖ ^ 2 ≤
          (1 / (Real.pi * |(k : ℝ)|)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      have hrpow : |(k : ℝ)| ^ (-(1 + s.val)) / Real.pi ^ 2 =
          |(k : ℝ)| ^ (1 - s.val) * (1 / (Real.pi * |(k : ℝ)|)) ^ 2 := by
        rw [show -(1 + s.val) = (1 - s.val) + (-2) by ring, Real.rpow_add hk',
          Real.rpow_neg hk'.le, Real.rpow_two]
        field_simp
      rw [hrpow]
      exact mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hk'.le _)
  unfold circleSobolevSq
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm) ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum]
  exact ENNReal.ofReal_lt_top

end Riesz1

end
