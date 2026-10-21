/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Moment comparison under size bias

Cauchy--Schwarz transfers `L^(2p)` bounds to `L^p` bounds under a density whose second
moment is controlled. The extended seminorm formulation also covers infinite moments.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- Cauchy--Schwarz for an arbitrary nonnegative observable under a real density. -/
theorem sizeBiased_lintegral_le {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {w : A → ℝ} {F : A → ℝ≥0∞} (hw : Measurable w) (hF : Measurable F) :
    (∫⁻ x, F x ∂μ.withDensity (fun x => ENNReal.ofReal (w x))) ≤
      eLpNorm w 2 μ * (∫⁻ x, F x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  have hconj : Real.HolderConjugate 2 2 :=
    (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).mpr (by norm_num)
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj hw.enorm.aemeasurable hF.aemeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hw.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  apply le_trans _ hcs
  rw [lintegral_withDensity_eq_lintegral_mul μ hw.ennreal_ofReal hF]
  apply lintegral_mono
  intro x
  change ENNReal.ofReal (w x) * F x ≤ ‖w x‖ₑ * F x
  gcongr
  exact Real.ofReal_le_enorm _

/-- The size-biased `L^p` norm is bounded by the base `L^(2p)` norm times
the `1/p` power of the density's base `L²` norm. The estimate holds for every real `p > 0`,
and does not require the measures to be probabilities. -/
theorem sizeBiased_eLpNorm_le {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {w T : A → ℝ} (hw : Measurable w) (hT : Measurable T) {p : ℝ} (hp : 0 < p) :
    eLpNorm T (ENNReal.ofReal p) (μ.withDensity (fun x => ENNReal.ofReal (w x))) ≤
      eLpNorm w 2 μ ^ (1 / p) * eLpNorm T (ENNReal.ofReal (2 * p)) μ := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hp20 : ENNReal.ofReal (2 * p) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hconj : Real.HolderConjugate 2 2 :=
    (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).mpr (by norm_num)
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj
    hw.enorm.aemeasurable (hT.enorm.pow_const p).aemeasurable
  have hpow : (∫⁻ x, ‖T x‖ₑ ^ p * ENNReal.ofReal (w x) ∂μ) ≤
      (∫⁻ x, ‖w x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
        (∫⁻ x, ‖T x‖ₑ ^ (2 * p) ∂μ) ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ ∫⁻ x, ‖w x‖ₑ * ‖T x‖ₑ ^ p ∂μ :=
        lintegral_mono fun x => by
          rw [mul_comm]
          gcongr
          exact Real.ofReal_le_enorm _
      _ ≤ _ := by
        simpa only [Pi.mul_apply, ← ENNReal.rpow_mul, mul_comm p (2 : ℝ)] using hcs
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hT.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hw.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp20 ENNReal.ofReal_ne_top hT.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * p),
    ENNReal.toReal_ofNat]
  rw [lintegral_withDensity_eq_lintegral_mul μ hw.ennreal_ofReal (hT.enorm.pow_const p)]
  simp only [Pi.mul_apply]
  have hswap : (∫⁻ x, ENNReal.ofReal (w x) * ‖T x‖ₑ ^ p ∂μ) =
      ∫⁻ x, ‖T x‖ₑ ^ p * ENNReal.ofReal (w x) ∂μ := by
    apply lintegral_congr
    intro x
    exact mul_comm _ _
  rw [hswap]
  calc
    _ ≤ ((∫⁻ x, ‖w x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
        (∫⁻ x, ‖T x‖ₑ ^ (2 * p) ∂μ) ^ (1 / 2 : ℝ)) ^ (1 / p) :=
      ENNReal.rpow_le_rpow hpow (by positivity)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
      congr 1
      rw [← ENNReal.rpow_mul]
      congr 1
      field_simp

/-- Event probabilities transfer by a square root. This is valid without finite moments,
using the extended value of the second moment when necessary. -/
theorem sizeBiased_measure_le {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {w : A → ℝ} (hw : Measurable w) {E : Set A} (hE : MeasurableSet E) :
    μ.withDensity (fun x => ENNReal.ofReal (w x)) E ≤
      eLpNorm w 2 μ * (μ E) ^ (1 / 2 : ℝ) := by
  have hconj : Real.HolderConjugate 2 2 :=
    (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).mpr (by norm_num)
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj
    (g := E.indicator (fun _ : A => (1 : ℝ≥0∞))) hw.enorm.aemeasurable
    (measurable_const.indicator hE).aemeasurable
  have hind : (∫⁻ x, (E.indicator (fun _ : A => (1 : ℝ≥0∞)) x) ^ (2 : ℝ) ∂μ) = μ E := by
    rw [← lintegral_indicator_one hE]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ E <;> simp [hx]
  rw [hind] at hcs
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hw.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  refine le_trans ?_ hcs
  rw [withDensity_apply _ hE, ← lintegral_indicator hE]
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ E
  · simpa only [Pi.mul_apply, Set.indicator_of_mem hx, mul_one] using Real.ofReal_le_enorm (w x)
  · simp only [Pi.mul_apply, Set.indicator_of_notMem hx, mul_zero, le_refl]

end Riesz1

end
