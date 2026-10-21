/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Bridges.ExplicitFormulasCentred
public import Riesz1.Kernel.AdmissibilityRegularitySobolev
public import Riesz1.ToMathlib.SineHarmonicDivergence

/-!
# Sharp Sobolev threshold for interval indicators

The threshold is proved for every real Sobolev index and every proper nonempty arc,
using the Sobolev predicate `CircleSobolev`.
-/

public section

open MeasureTheory

namespace Riesz1

namespace Internal

/-- Finiteness of the extended Fourier energy implies summability of its real summands. -/
lemma summable_circleSobolev_summand {r : ℝ} {f : UnitAddCircle → ℂ}
    (h : CircleSobolev r f) :
    Summable (fun k : ℤ => if k = 0 then (0 : ℝ) else
      |(k : ℝ)| ^ (2 * r) * ‖fourierCoeff f k‖ ^ 2) := by
  obtain ⟨hf, hh⟩ := h
  have hs := ENNReal.summable_toReal hh.ne
  change Summable (fun k : ℤ =>
    (if k = 0 then (0 : ENNReal) else
      ENNReal.ofReal (|(k : ℝ)| ^ (2 * r) * ‖fourierCoeff f k‖ ^ 2)).toReal) at hs
  convert hs using 1
  funext k
  split_ifs <;> simp [ENNReal.toReal_ofReal, Real.rpow_nonneg]

/-- A summable real Fourier energy gives membership in the Sobolev space. -/
lemma circleSobolev_of_summable_summand {r : ℝ} {f : UnitAddCircle → ℂ}
    (hf : MemLp f 2 volume)
    (hs : Summable (fun k : ℤ => if k = 0 then (0 : ℝ) else
      |(k : ℝ)| ^ (2 * r) * ‖fourierCoeff f k‖ ^ 2)) : CircleSobolev r f := by
  refine ⟨hf, ?_⟩
  have he : circleSobolevSq r ⟨f, hf⟩ = ∑' k : ℤ,
      ENNReal.ofReal (if k = 0 then (0 : ℝ) else
        |(k : ℝ)| ^ (2 * r) * ‖fourierCoeff f k‖ ^ 2) := by
    unfold circleSobolevSq
    refine tsum_congr fun k => ?_
    split_ifs <;> simp
  rw [he]
  exact hs.tsum_ofReal_lt_top

end Internal

/-- Subtraction preserves the circle Sobolev space. -/
lemma circleSobolev_sub {r : ℝ} {f g : UnitAddCircle → ℂ}
    (hf : CircleSobolev r f) (hg : CircleSobolev r g) : CircleSobolev r (f - g) := by
  have hsf := Internal.summable_circleSobolev_summand hf
  have hsg := Internal.summable_circleSobolev_summand hg
  obtain ⟨hfL2, _⟩ := hf
  obtain ⟨hgL2, _⟩ := hg
  have hcoef : ∀ k, fourierCoeff (f - g) k = fourierCoeff f k - fourierCoeff g k := by
    intro k
    unfold fourierCoeff
    simp only [Pi.sub_apply, smul_sub]
    apply integral_sub
    · exact ((by rw [← volume_eq_haar_circle]; exact hfL2.integrable one_le_two) :
        Integrable f AddCircle.haarAddCircle).fourier_smul _
    · exact ((by rw [← volume_eq_haar_circle]; exact hgL2.integrable one_le_two) :
        Integrable g AddCircle.haarAddCircle).fourier_smul _
  apply Internal.circleSobolev_of_summable_summand (hfL2.sub hgL2)
  refine Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) (fun k => ?_)
    ((hsf.add hsg).mul_left 2)
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte, hcoef]
    have hnorm := norm_sub_le (fourierCoeff f k) (fourierCoeff g k)
    have hsq : ‖fourierCoeff f k - fourierCoeff g k‖ ^ 2 ≤
        2 * (‖fourierCoeff f k‖ ^ 2 + ‖fourierCoeff g k‖ ^ 2) := by
      nlinarith [sq_nonneg (‖fourierCoeff f k‖ - ‖fourierCoeff g k‖),
        norm_nonneg (fourierCoeff f k - fourierCoeff g k),
        norm_nonneg (fourierCoeff f k), norm_nonneg (fourierCoeff g k)]
    calc _ ≤ |(k : ℝ)| ^ (2 * r) *
          (2 * (‖fourierCoeff f k‖ ^ 2 + ‖fourierCoeff g k‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := by ring

/-- Decreasing the Sobolev index preserves membership for the homogeneous energy. -/
lemma circleSobolev_of_le {r t : ℝ} (hrt : r ≤ t) {f : UnitAddCircle → ℂ}
    (h : CircleSobolev t f) : CircleSobolev r f := by
  obtain ⟨hf, hh⟩ := h
  refine ⟨hf, lt_of_le_of_lt (ENNReal.tsum_le_tsum fun k => ?_) hh⟩
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Int.one_le_abs hk) (by linarith)

/-- A proper arc indicator belongs to every homogeneous circle Sobolev space of index below 1/2. -/
theorem circleSobolev_arcIndicator_of_lt_half {a r : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1 / 2) (hr : r < 1 / 2) (c : UnitAddCircle) :
    CircleSobolev r (fun x => (arcIndicator c a x : ℂ)) := by
  apply circleSobolev_of_coeff_decay (g := -1) (K := Real.pi⁻¹) (by linarith)
    (memLp_arcIndicator c a) (k₀ := 1) le_rfl
  intro k hk
  have hk0 : k ≠ 0 := by intro h; simp [h] at hk
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  rw [fourierCoeff_arcIndicator_centre ha1 c k, norm_mul,
    norm_fourier_unitAddCircle_eq_one, one_mul, fourierCoeff_indicatorArc ha0 ha1 k]
  simp only [hk0, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_mul, abs_of_pos Real.pi_pos, Real.rpow_neg_one]
  calc |Real.sin (2 * Real.pi * (k : ℝ) * a)| / (Real.pi * |(k : ℝ)|)
      ≤ 1 / (Real.pi * |(k : ℝ)|) :=
        div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
    _ = Real.pi⁻¹ * |(k : ℝ)|⁻¹ := by rw [one_div, mul_inv]

/-- A proper arc indicator is excluded at the critical index 1/2. -/
theorem not_circleSobolev_half_arcIndicator {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1 / 2) (c : UnitAddCircle) :
    ¬ CircleSobolev (1 / 2) (fun x => (arcIndicator c a x : ℂ)) := by
  intro h
  have hs := (Internal.summable_circleSobolev_summand h).comp_injective
    (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℤ)))
  have hsin : Summable (fun n : ℕ => Real.sin ((n : ℝ) * (2 * Real.pi * a)) ^ 2 / (n : ℝ)) := by
    convert hs.mul_left (Real.pi ^ 2) using 1
    funext n
    by_cases hn : n = 0
    · simp [hn]
    · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      simp only [Function.comp_apply, Nat.cast_eq_zero, hn, ↓reduceIte,
        Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      rw [fourierCoeff_arcIndicator_centre ha1 c (n : ℤ), norm_mul,
        norm_fourier_unitAddCircle_eq_one, one_mul, fourierCoeff_indicatorArc ha0 ha1]
      simp only [Nat.cast_eq_zero, hn, ↓reduceIte, Int.cast_natCast,
        show 2 * (1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have he : (n : ℝ) * (2 * Real.pi * a) = 2 * Real.pi * (n : ℝ) * a := by ring
      rw [he]
      field_simp
  have hsmall : Summable (fun n : ℕ =>
      Real.sin ((n : ℝ) * (2 * Real.pi * a)) ^ 2 / ((n : ℝ) + 1)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsin
    by_cases hn : n = 0
    · simp [hn]
    · exact div_le_div_of_nonneg_left (sq_nonneg _) (by exact_mod_cast Nat.pos_of_ne_zero hn)
        (by linarith)
  exact not_summable_sin_sq_div_nat_add_one
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])).ne' hsmall

/-- The exact Sobolev threshold for every proper nonempty arc (including the negative endpoint). -/
theorem circleSobolev_arcIndicator_iff {a r : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1 / 2) (c : UnitAddCircle) :
    CircleSobolev r (fun x => (arcIndicator c a x : ℂ)) ↔ r < 1 / 2 := by
  constructor
  · intro h
    by_contra hr
    exact not_circleSobolev_half_arcIndicator ha0 ha1 c
      (circleSobolev_of_le (le_of_not_gt hr) h)
  · exact fun hr => circleSobolev_arcIndicator_of_lt_half ha0 ha1 hr c

/-- Both interval Sobolev assertions, with the exponent of the paper. -/
theorem admissible_examples_indicator_sobolev (s : RieszExponent) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1 / 2) (c : UnitAddCircle) :
    CircleSobolev ((1 - s.val) / 2) (fun x => (arcIndicator c a x : ℂ)) ∧
      ¬ CircleSobolev (1 / 2) (fun x => (arcIndicator c a x : ℂ)) :=
  ⟨circleSobolev_arcIndicator_of_lt_half ha0 ha1 (by linarith [s.2.1]) c,
    not_circleSobolev_half_arcIndicator ha0 ha1 c⟩

end Riesz1
