/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Mollifier.Periodization
public import Riesz1.Frozen.CircleSobolevSq
public import Mathlib.Tactic

/-!
# Fourier regularization estimate on the circle

Lemma 5.1. For a circle mollifier `ρ`, a scale `0 < h ≤ 1` and a real
`s ∈ (0, 1)`, the convolution `ξ_h = ξ ∗ ρ_h` of an `L²` function `ξ` satisfies, with `σ = (1-s)/2`,
`r = min δ 1` and the constant `16` (which depends on no parameter):

* `‖ξ - ξ_h‖²_{H^σ} ≤ 16 h^{2r} ‖ξ‖²_{H^{σ+r}}`,
* `0 ≤ ‖ξ‖²_{H^σ} - ‖ξ_h‖²_{H^σ} ≤ 16 h^{2r} ‖ξ‖²_{H^{σ+r}}`.

The Sobolev seminorms are `circleSobolevSq`, whose weight is `|k|^{2r}` on the Fourier mode `k`.
The multiplier `ρ̂(hk)` of the regularization satisfies `(1 - ρ̂(t))² ≤ 16 min(t², 1)` and
`1 - ρ̂(t)² ≤ 16 min(t², 1)` (see `Riesz1.Mollifier.Multiplier`), which gives the bounds
termwise on the Fourier modes.

Main results:
* `circleSobolevSq_regularize_le` and `circleSobolevSq_regularize_sub_le`: the bounds in
  extended nonnegative reals.
* `regularization_sobolev`: the displayed inequalities, with real `toReal` values.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- The regularization `ξ_h = ξ ∗ ρ_h` of an `L²` function, as an element of the carrier of
`circleSobolevSq`. -/
noncomputable def regularizeL2 {ρ : ℝ → ℝ} (hρ : IsCircleMollifier ρ) (h : {h : ℝ // 0 < h})
    (hh1 : h.1 ≤ 1) (ξ : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) :
    {f : UnitAddCircle → ℂ // MemLp f 2 volume} :=
  ⟨circleRegularize ρ h hρ.continuous ξ, memLp_circleRegularize hρ h hh1 ξ⟩

/-- The difference `ξ - η` of two `L²` functions, as an element of the same carrier. -/
def subL2 (ξ η : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) :
    {f : UnitAddCircle → ℂ // MemLp f 2 volume} :=
  ⟨fun x => ξ.1 x - η.1 x, ξ.2.sub η.2⟩

lemma integrable_fourier_mul (ξ : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) (k : ℤ) :
    Integrable (fun x => fourier (-k) x * ξ.1 x) volume :=
  (ξ.2.integrable one_le_two).bdd_mul (c := 1) (fourier (-k)).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => (norm_fourier_apply _ _).le)

lemma fourierCoeff_subL2 (ξ η : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) (k : ℤ) :
    fourierCoeff (subL2 ξ η).1 k = fourierCoeff ξ.1 k - fourierCoeff η.1 k := by
  rw [fourierCoeff_eq_volume, fourierCoeff_eq_volume, fourierCoeff_eq_volume,
    ← integral_sub (integrable_fourier_mul ξ k) (integrable_fourier_mul η k)]
  congr 1
  funext x
  simp only [subL2]
  ring

/-- The `k`-th Fourier coefficient of the regularization is `ξ^(k) ρ̂(h k)`. -/
lemma fourierCoeff_regularizeL2 {ρ : ℝ → ℝ} (hρ : IsCircleMollifier ρ) (h : {h : ℝ // 0 < h})
    (hh1 : h.1 ≤ 1) (ξ : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) (k : ℤ) :
    fourierCoeff (regularizeL2 hρ h hh1 ξ).1 k =
      fourierCoeff ξ.1 k * ((mollifierFT ρ (h.1 * k) : ℝ) : ℂ) := by
  show fourierCoeff (circleRegularize _ h hρ.continuous ξ) k = _
  rw [fourierCoeff_circleRegularize hρ h hh1 ξ k, fourierCoeff_circleMollifier hρ h hh1 k]

/-- Monotonicity of `circleSobolevSq` in the index, since `|k| ≥ 1` on the nonzero modes. -/
lemma circleSobolevSq_mono {a b : ℝ} (hab : a ≤ b)
    (f : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) :
    circleSobolevSq a f ≤ circleSobolevSq b f := by
  unfold circleSobolevSq
  refine ENNReal.tsum_le_tsum fun k => ?_
  split_ifs with hk
  · exact le_rfl
  · apply ENNReal.ofReal_le_ofReal
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have := Int.one_le_abs hk
      rw [← Int.cast_abs]
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hk1 (by linarith))
      (sq_nonneg _)

/-- The multiplier estimate on one Fourier mode: `(1 - ρ̂(h k))² ≤ 16 h^{2r} |k|^{2r}`. -/
lemma sq_one_sub_mollifierFT_le_rpow {ρ : ℝ → ℝ} (hρ : IsCircleMollifier ρ) {h : ℝ} (hh : 0 < h)
    (k : ℤ) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (1 - mollifierFT ρ (h * k)) ^ 2 ≤ 16 * (h ^ (2 * r) * |(k : ℝ)| ^ (2 * r)) := by
  have h1 := mollifierFT_sq_one_sub_le hρ (h * k)
  have h2 := min_sq_le_abs_rpow hr0 hr1 (h * k)
  have habs : |h * (k : ℝ)| ^ (2 * r) = h ^ (2 * r) * |(k : ℝ)| ^ (2 * r) := by
    rw [abs_mul, abs_of_pos hh, Real.mul_rpow hh.le (abs_nonneg _)]
  rw [habs] at h2
  linarith

/-- The multiplier estimate on one Fourier mode: `1 - ρ̂(h k)² ≤ 16 h^{2r} |k|^{2r}`. -/
lemma one_sub_sq_mollifierFT_le_rpow {ρ : ℝ → ℝ} (hρ : IsCircleMollifier ρ) {h : ℝ}
    (hh : 0 < h) (k : ℤ) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    1 - mollifierFT ρ (h * k) ^ 2 ≤ 16 * (h ^ (2 * r) * |(k : ℝ)| ^ (2 * r)) := by
  have h1 := one_sub_mollifierFT_sq_le hρ (h * k)
  have h2 := min_sq_le_abs_rpow hr0 hr1 (h * k)
  have habs : |h * (k : ℝ)| ^ (2 * r) = h ^ (2 * r) * |(k : ℝ)| ^ (2 * r) := by
    rw [abs_mul, abs_of_pos hh, Real.mul_rpow hh.le (abs_nonneg _)]
  rw [habs] at h2
  linarith

/-- The modulus of a complex number times a real number, squared. -/
lemma norm_sq_mul_ofReal (a : ℂ) (x : ℝ) : ‖a * (x : ℂ)‖ ^ 2 = ‖a‖ ^ 2 * x ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- The termwise bound for the difference: `|k|^{2σ} |ξ̂(k)(1 - ρ̂)|² ≤ 16 h^{2r} |k|^{2(σ+r)}|ξ̂(k)|²`
on a nonzero mode. -/
lemma termwise_sub_le {ρ : ℝ → ℝ} (hρ : IsCircleMollifier ρ) {h : ℝ} (hh : 0 < h) (k : ℤ)
    (hk : k ≠ 0) {σ r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (a : ℂ) :
    |(k : ℝ)| ^ (2 * σ) * ‖a * ((1 - mollifierFT ρ (h * k) : ℝ) : ℂ)‖ ^ 2 ≤
      16 * h ^ (2 * r) * (|(k : ℝ)| ^ (2 * (σ + r)) * ‖a‖ ^ 2) := by
  have hkpos : 0 < |(k : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hk)
  have hq := sq_one_sub_mollifierFT_le_rpow hρ hh k hr0 hr1
  have hnn : 0 ≤ |(k : ℝ)| ^ (2 * σ) * ‖a‖ ^ 2 := by positivity
  rw [norm_sq_mul_ofReal, show 2 * (σ + r) = 2 * σ + 2 * r by ring, Real.rpow_add hkpos]
  calc |(k : ℝ)| ^ (2 * σ) * (‖a‖ ^ 2 * (1 - mollifierFT ρ (h * k)) ^ 2)
      = (|(k : ℝ)| ^ (2 * σ) * ‖a‖ ^ 2) * (1 - mollifierFT ρ (h * k)) ^ 2 := by ring
    _ ≤ (|(k : ℝ)| ^ (2 * σ) * ‖a‖ ^ 2) * (16 * (h ^ (2 * r) * |(k : ℝ)| ^ (2 * r))) :=
        mul_le_mul_of_nonneg_left hq hnn
    _ = 16 * h ^ (2 * r) * (|(k : ℝ)| ^ (2 * σ) * |(k : ℝ)| ^ (2 * r) * ‖a‖ ^ 2) := by ring

/-- The termwise bound for `ξ_h`: `|k|^{2σ} |ξ̂(k)|² ≤ |k|^{2σ} |ξ̂(k)ρ̂(hk)|² + 16 h^{2r} |k|^{2(σ+r)} |ξ̂(k)|²`
on a nonzero mode. -/
lemma termwise_reg_le {ρ : ℝ → ℝ} (hρ : IsCircleMollifier ρ) {h : ℝ} (hh : 0 < h) (k : ℤ)
    (hk : k ≠ 0) {σ r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (a : ℂ) :
    |(k : ℝ)| ^ (2 * σ) * ‖a‖ ^ 2 ≤
      |(k : ℝ)| ^ (2 * σ) * ‖a * ((mollifierFT ρ (h * k) : ℝ) : ℂ)‖ ^ 2 +
        16 * h ^ (2 * r) * (|(k : ℝ)| ^ (2 * (σ + r)) * ‖a‖ ^ 2) := by
  have hkpos : 0 < |(k : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hk)
  have hq := one_sub_sq_mollifierFT_le_rpow hρ hh k hr0 hr1
  have hP : 0 ≤ |(k : ℝ)| ^ (2 * σ) := Real.rpow_nonneg (abs_nonneg _) _
  have key : ‖a‖ ^ 2 ≤ ‖a‖ ^ 2 * mollifierFT ρ (h * k) ^ 2 +
      16 * (h ^ (2 * r) * |(k : ℝ)| ^ (2 * r)) * ‖a‖ ^ 2 := by
    have hA : 0 ≤ ‖a‖ ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hq hA]
  have step := mul_le_mul_of_nonneg_left key hP
  have e : |(k : ℝ)| ^ (2 * σ) * (‖a‖ ^ 2 * mollifierFT ρ (h * k) ^ 2 +
      16 * (h ^ (2 * r) * |(k : ℝ)| ^ (2 * r)) * ‖a‖ ^ 2) =
      |(k : ℝ)| ^ (2 * σ) * (‖a‖ ^ 2 * mollifierFT ρ (h * k) ^ 2) +
        16 * h ^ (2 * r) * (|(k : ℝ)| ^ (2 * σ) * |(k : ℝ)| ^ (2 * r) * ‖a‖ ^ 2) := by
    ring
  rw [norm_sq_mul_ofReal, show 2 * (σ + r) = 2 * σ + 2 * r by ring, Real.rpow_add hkpos]
  linarith [step, e]

/-- The nonnegativity of the constant `16 h^{2r}` in the regularization estimates. -/
lemma coeff_nonneg (h : {h : ℝ // 0 < h}) (r : ℝ) : 0 ≤ 16 * h.1 ^ (2 * r) :=
  mul_nonneg (by norm_num) (Real.rpow_nonneg h.2.le _)

/-- The Sobolev seminorm of `ξ - ξ_h`, in extended nonnegative reals: the first displayed
estimate of Lemma 5.1. -/
lemma circleSobolevSq_subL2_le {ρ : ℝ → ℝ} (hρ : IsCircleMollifier ρ) (h : {h : ℝ // 0 < h})
    (hh1 : h.1 ≤ 1) (ξ : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) {σ r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    circleSobolevSq σ (subL2 ξ (regularizeL2 hρ h hh1 ξ)) ≤
      ENNReal.ofReal (16 * h.1 ^ (2 * r)) * circleSobolevSq (σ + r) ξ := by
  unfold circleSobolevSq
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte]
    rw [fourierCoeff_subL2, fourierCoeff_regularizeL2, ← ENNReal.ofReal_mul (coeff_nonneg h r)]
    have hsub : fourierCoeff ξ.1 k - fourierCoeff ξ.1 k * ((mollifierFT ρ (h.1 * k) : ℝ) : ℂ) =
        fourierCoeff ξ.1 k * ((1 - mollifierFT ρ (h.1 * k) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hsub]
    apply ENNReal.ofReal_le_ofReal
    exact termwise_sub_le hρ h.2 k hk hr0 hr1 _

/-- The Sobolev seminorm of `ξ_h` does not exceed that of `ξ`: the left inequality of the second
displayed estimate of Lemma 5.1. -/
lemma circleSobolevSq_regularizeL2_le {ρ : ℝ → ℝ} (hρ : IsCircleMollifier ρ) (h : {h : ℝ // 0 < h})
    (hh1 : h.1 ≤ 1) (ξ : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) (σ : ℝ) :
    circleSobolevSq σ (regularizeL2 hρ h hh1 ξ) ≤ circleSobolevSq σ ξ := by
  unfold circleSobolevSq
  refine ENNReal.tsum_le_tsum fun k => ?_
  split_ifs with hk
  · exact le_rfl
  · rw [fourierCoeff_regularizeL2, norm_sq_mul_ofReal]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (sq_nonneg _) (mollifierFT_sq_le_one hρ _))
      (Real.rpow_nonneg (abs_nonneg _) _)

/-- The Sobolev seminorm of `ξ` is at most that of `ξ_h` plus the remainder: the right inequality
of the second displayed estimate of Lemma 5.1. -/
lemma circleSobolevSq_le_regularizeL2_add {ρ : ℝ → ℝ} (hρ : IsCircleMollifier ρ)
    (h : {h : ℝ // 0 < h}) (hh1 : h.1 ≤ 1) (ξ : {f : UnitAddCircle → ℂ // MemLp f 2 volume})
    {σ r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    circleSobolevSq σ ξ ≤ circleSobolevSq σ (regularizeL2 hρ h hh1 ξ) +
      ENNReal.ofReal (16 * h.1 ^ (2 * r)) * circleSobolevSq (σ + r) ξ := by
  unfold circleSobolevSq
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte]
    rw [fourierCoeff_regularizeL2, ← ENNReal.ofReal_mul (coeff_nonneg h r)]
    have hX : 0 ≤ |(k : ℝ)| ^ (2 * σ) * ‖fourierCoeff ξ.1 k * ((mollifierFT ρ (h.1 * k) : ℝ) : ℂ)‖ ^ 2 :=
      by positivity
    have hY : 0 ≤ 16 * h.1 ^ (2 * r) * (|(k : ℝ)| ^ (2 * (σ + r)) * ‖fourierCoeff ξ.1 k‖ ^ 2) :=
      mul_nonneg (coeff_nonneg h r) (by positivity)
    rw [← ENNReal.ofReal_add hX hY]
    apply ENNReal.ofReal_le_ofReal
    exact termwise_reg_le hρ h.2 k hk hr0 hr1 _

/-- The displayed estimates of Lemma 5.1, with constant `C = 16`, which
depends on no parameter. The Sobolev seminorms `circleSobolevSq` are finite by assumption, so
their real values are the extended ones converted with `toReal`. The first inequality bounds
`‖ξ - ξ_h‖²_{H^σ}`. The second bounds `0 ≤ ‖ξ‖²_{H^σ} - ‖ξ_h‖²_{H^σ}` from above. Here
`σ = (1 - s)/2` and `r = min δ 1`. -/
theorem regularization_sobolev {ρ : ℝ → ℝ} (hρ : IsCircleMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s δ h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
      (ξ : {f : UnitAddCircle → ℂ // MemLp f 2 volume}),
      0 < s → s < 1 → 0 < δ → circleSobolevSq ((1 - s) / 2 + δ) ξ < ⊤ →
        (circleSobolevSq ((1 - s) / 2) (subL2 ξ (regularizeL2 hρ ⟨h, hh⟩ hh1 ξ))).toReal ≤
            C * h ^ (2 * min δ 1) * (circleSobolevSq ((1 - s) / 2 + min δ 1) ξ).toReal ∧
          0 ≤ (circleSobolevSq ((1 - s) / 2) ξ).toReal -
            (circleSobolevSq ((1 - s) / 2) (regularizeL2 hρ ⟨h, hh⟩ hh1 ξ)).toReal ∧
          (circleSobolevSq ((1 - s) / 2) ξ).toReal -
            (circleSobolevSq ((1 - s) / 2) (regularizeL2 hρ ⟨h, hh⟩ hh1 ξ)).toReal ≤
            C * h ^ (2 * min δ 1) * (circleSobolevSq ((1 - s) / 2 + min δ 1) ξ).toReal := by
  refine ⟨16, by norm_num, fun s δ h hh hh1 ξ hs0 hs1 hδ hfin => ?_⟩
  have hr0 : 0 < min δ 1 := lt_min hδ one_pos
  have hr1 : min δ 1 ≤ 1 := min_le_right _ _
  have hrδ : min δ 1 ≤ δ := min_le_left _ _
  have hD : circleSobolevSq ((1 - s) / 2 + min δ 1) ξ ≠ ⊤ :=
    ne_top_of_le_ne_top hfin.ne (circleSobolevSq_mono (by linarith) ξ)
  have hA : circleSobolevSq ((1 - s) / 2) ξ ≠ ⊤ :=
    ne_top_of_le_ne_top hfin.ne (circleSobolevSq_mono (by linarith) ξ)
  have hB : circleSobolevSq ((1 - s) / 2) (regularizeL2 hρ ⟨h, hh⟩ hh1 ξ) ≠ ⊤ :=
    ne_top_of_le_ne_top hA (circleSobolevSq_regularizeL2_le hρ ⟨h, hh⟩ hh1 ξ _)
  have hE : ENNReal.ofReal (16 * h ^ (2 * min δ 1)) * circleSobolevSq ((1 - s) / 2 + min δ 1) ξ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD
  have hK : 0 ≤ 16 * h ^ (2 * min δ 1) := coeff_nonneg ⟨h, hh⟩ _
  refine ⟨?_, ?_, ?_⟩
  · have key := ENNReal.toReal_mono hE
      (circleSobolevSq_subL2_le hρ ⟨h, hh⟩ hh1 ξ hr0 hr1)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] at key
    exact key
  · have key := ENNReal.toReal_mono hA (circleSobolevSq_regularizeL2_le hρ ⟨h, hh⟩ hh1 ξ _)
    linarith
  · have key := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hB, hE⟩)
      (circleSobolevSq_le_regularizeL2_add hρ ⟨h, hh⟩ hh1 ξ hr0 hr1)
    rw [ENNReal.toReal_add hB hE, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] at key
    linarith

end Riesz1

end
