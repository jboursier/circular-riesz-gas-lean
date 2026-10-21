/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Riesz1.Frozen.CircleSobolevSq
public import Riesz1.ToMathlib.Mollifier.RegularizationSobolev

/-!
# Triangle inequality for the circle Sobolev seminorm

The square root of the homogeneous circle Sobolev seminorm `circleSobolevSq r` satisfies the
triangle inequality. A finite seminorm is the squared `ℓ²` norm of the nonnegative weighted
coefficient sequence `k ↦ |k|^r ‖f̂(k)‖`, so the `ℓ²` Minkowski inequality `NNReal.Lp_add_le_tsum`
applies. The reverse triangle inequality for a difference of two profiles compares the standard
deviations of the regularized and unregularized statistics (Theorem 3).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace Riesz1

/-- The nonnegative weighted Fourier coefficient `|k|^r ‖f̂(k)‖` of the circle Sobolev seminorm,
with the zero mode removed. The sum of its squares over `k` is `circleSobolevSq r f`. -/
noncomputable def circleSobolevCoeff (r : ℝ) (f : {f : UnitAddCircle → ℂ // MemLp f 2 volume})
    (k : ℤ) : ℝ≥0 :=
  if k = 0 then 0 else (|(k : ℝ)| ^ r).toNNReal * ‖fourierCoeff f.val k‖₊

/-- Each term of `circleSobolevSq r f` is the square of the corresponding weighted coefficient. -/
lemma circleSobolevSq_term_eq (r : ℝ) (f : {f : UnitAddCircle → ℂ // MemLp f 2 volume})
    (k : ℤ) :
    (if k = 0 then 0 else ENNReal.ofReal (|(k : ℝ)| ^ (2 * r) * ‖fourierCoeff f.val k‖ ^ 2)) =
      ((circleSobolevCoeff r f k ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  by_cases hk : k = 0
  · simp [circleSobolevCoeff, hk]
  · rw [ite_eq_right hk, circleSobolevCoeff, ite_eq_right hk, ENNReal.ofReal]
    congr 1
    have hpow : |(k : ℝ)| ^ (2 * r) = (|(k : ℝ)| ^ r) ^ 2 := by
      rw [show 2 * r = r * 2 by ring, Real.rpow_mul (abs_nonneg _), Real.rpow_two]
    have hr : 0 ≤ |(k : ℝ)| ^ r := Real.rpow_nonneg (abs_nonneg _) r
    apply NNReal.eq
    rw [Real.coe_toNNReal (|(k : ℝ)| ^ (2 * r) * ‖fourierCoeff f.val k‖ ^ 2)
        (by positivity), NNReal.coe_pow, NNReal.coe_mul, Real.coe_toNNReal _ hr, coe_nnnorm,
      hpow]
    ring

/-- The circle Sobolev seminorm is the sum of the squared weighted coefficients, as an
extended sum of nonnegative reals, whenever it is finite. -/
lemma circleSobolevSq_eq_tsum_coeff (r : ℝ) (f : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) :
    circleSobolevSq r f = ∑' k : ℤ, ((circleSobolevCoeff r f k ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  unfold circleSobolevSq
  exact tsum_congr fun k => circleSobolevSq_term_eq r f k

/-- The weighted coefficients are square summable when the circle Sobolev seminorm is finite. -/
lemma circleSobolevCoeff_summable {r : ℝ} {f : {f : UnitAddCircle → ℂ // MemLp f 2 volume}}
    (hf : circleSobolevSq r f ≠ ⊤) :
    Summable fun k : ℤ => circleSobolevCoeff r f k ^ 2 := by
  apply ENNReal.tsum_coe_ne_top_iff_summable.mp
  rw [← circleSobolevSq_eq_tsum_coeff]
  exact hf

/-- The seminorm is the coercion of the real sum of squared coefficients when it is finite. -/
lemma circleSobolevSq_eq_coe_tsum {r : ℝ} {f : {f : UnitAddCircle → ℂ // MemLp f 2 volume}}
    (hf : circleSobolevSq r f ≠ ⊤) :
    circleSobolevSq r f = ((∑' k : ℤ, circleSobolevCoeff r f k ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  rw [ENNReal.coe_tsum (circleSobolevCoeff_summable hf), circleSobolevSq_eq_tsum_coeff]

/-- Minkowski's inequality for `ℓ²` sums of nonnegative sequences, in the form of square roots
of sums: if `u ≤ v + w` coefficientwise, then `‖u‖₂ ≤ ‖v‖₂ + ‖w‖₂`. -/
lemma circleSobolevCoeff_minkowski {u v w : ℤ → ℝ≥0} (h : ∀ k, u k ≤ v k + w k)
    (hv : Summable fun k => v k ^ (2 : ℝ)) (hw : Summable fun k => w k ^ (2 : ℝ)) :
    (∑' k, u k ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤
      (∑' k, v k ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) + (∑' k, w k ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  obtain ⟨hs, hle⟩ := NNReal.Lp_add_le_tsum (f := v) (g := w) (p := 2) one_le_two hv hw
  have hu : Summable fun k => u k ^ (2 : ℝ) :=
    NNReal.summable_of_le (fun k => NNReal.rpow_le_rpow (h k) (by norm_num)) hs
  have hmono : ∑' k, u k ^ (2 : ℝ) ≤ ∑' k, (v k + w k) ^ (2 : ℝ) :=
    hu.tsum_le_tsum (fun k => NNReal.rpow_le_rpow (h k) (by norm_num)) hs
  calc (∑' k, u k ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ (∑' k, (v k + w k) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        NNReal.rpow_le_rpow hmono (by norm_num)
    _ ≤ _ := hle

/-- The triangle inequality for the square root of the circle Sobolev seminorm, for finite
seminorms of a profile, a second profile, and their difference:
`|√‖f‖ - √‖g‖| ≤ √‖f - g‖`. -/
theorem circleSobolevSq_sqrt_sub_le (r : ℝ) (f g : {f : UnitAddCircle → ℂ // MemLp f 2 volume})
    (hf : circleSobolevSq r f ≠ ⊤) (hg : circleSobolevSq r g ≠ ⊤)
    (he : circleSobolevSq r (subL2 f g) ≠ ⊤) :
    |Real.sqrt (circleSobolevSq r f).toReal - Real.sqrt (circleSobolevSq r g).toReal| ≤
      Real.sqrt (circleSobolevSq r (subL2 f g)).toReal := by
  set a := circleSobolevCoeff r f with ha
  set b := circleSobolevCoeff r g with hb
  set c := circleSobolevCoeff r (subL2 f g) with hc
  -- Coefficientwise: `‖f̂(k)‖ ≤ ‖ĝ(k)‖ + ‖(f - g)^(k)‖`, and symmetrically for `g`.
  have hfg : ∀ k, fourierCoeff (subL2 f g).val k = fourierCoeff f.val k - fourierCoeff g.val k :=
    fun k => fourierCoeff_subL2 f g k
  have h1 : ∀ k, a k ≤ b k + c k := by
    intro k
    by_cases hk : k = 0
    · simp [ha, hb, hc, circleSobolevCoeff, hk]
    · simp only [ha, hb, hc, circleSobolevCoeff, ite_eq_right hk, hfg]
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      have : fourierCoeff f.val k = fourierCoeff g.val k + (fourierCoeff f.val k - fourierCoeff g.val k) :=
        (add_sub_cancel _ _).symm
      calc ‖fourierCoeff f.val k‖₊
          = ‖fourierCoeff g.val k + (fourierCoeff f.val k - fourierCoeff g.val k)‖₊ := by rw [← this]
        _ ≤ ‖fourierCoeff g.val k‖₊ + ‖fourierCoeff f.val k - fourierCoeff g.val k‖₊ :=
          nnnorm_add_le _ _
  have h2 : ∀ k, b k ≤ a k + c k := by
    intro k
    by_cases hk : k = 0
    · simp [ha, hb, hc, circleSobolevCoeff, hk]
    · simp only [ha, hb, hc, circleSobolevCoeff, ite_eq_right hk, hfg]
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      have : fourierCoeff g.val k = fourierCoeff f.val k - (fourierCoeff f.val k - fourierCoeff g.val k) :=
        (sub_sub_cancel _ _).symm
      calc ‖fourierCoeff g.val k‖₊
          = ‖fourierCoeff f.val k - (fourierCoeff f.val k - fourierCoeff g.val k)‖₊ := by rw [← this]
        _ ≤ ‖fourierCoeff f.val k‖₊ + ‖fourierCoeff f.val k - fourierCoeff g.val k‖₊ :=
          nnnorm_sub_le _ _
  have hsa := circleSobolevCoeff_summable hf
  have hsb := circleSobolevCoeff_summable hg
  have hsc := circleSobolevCoeff_summable he
  have M1 := circleSobolevCoeff_minkowski h1 (by simpa only [Real.rpow_two, NNReal.rpow_two] using hsb)
    (by simpa only [Real.rpow_two, NNReal.rpow_two] using hsc)
  have M2 := circleSobolevCoeff_minkowski h2 (by simpa only [Real.rpow_two, NNReal.rpow_two] using hsa)
    (by simpa only [Real.rpow_two, NNReal.rpow_two] using hsc)
  simp only [NNReal.rpow_two] at M1 M2
  -- The square root of a finite seminorm is the nonnegative real `(∑ a²)^(1/2)`.
  have hsqrt : ∀ A : ℝ≥0, Real.sqrt (A : ℝ) = ((A ^ (1 / 2 : ℝ) : ℝ≥0) : ℝ) := fun A => by
    rw [Real.sqrt_eq_rpow, NNReal.coe_rpow]
  have hA : (circleSobolevSq r f).toReal = ((∑' k, a k ^ 2 : ℝ≥0) : ℝ) := by
    rw [circleSobolevSq_eq_coe_tsum hf, ENNReal.coe_toReal]
  have hB : (circleSobolevSq r g).toReal = ((∑' k, b k ^ 2 : ℝ≥0) : ℝ) := by
    rw [circleSobolevSq_eq_coe_tsum hg, ENNReal.coe_toReal]
  have hC : (circleSobolevSq r (subL2 f g)).toReal = ((∑' k, c k ^ 2 : ℝ≥0) : ℝ) := by
    rw [circleSobolevSq_eq_coe_tsum he, ENNReal.coe_toReal]
  rw [hA, hB, hC, hsqrt, hsqrt, hsqrt]
  have M1' := NNReal.coe_le_coe.mpr M1
  have M2' := NNReal.coe_le_coe.mpr M2
  rw [NNReal.coe_add] at M1' M2'
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

end Riesz1
