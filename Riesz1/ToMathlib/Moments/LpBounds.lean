/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Moment bounds through integer powers

General tools for the loop moment estimates:

* `eLpNorm_le_of_lintegral_pow_le`: an `L^m` bound for natural `m` follows from a bound on
  the integral of `|f|^m`, so the norm is taken in the sense of `eLpNorm`.
* `lintegral_pow_le_of_tail`: a tail estimate on a set `A` of small probability, together
  with a moment bound of order `2m`, bounds the `m`-th moment (Cauchy--Schwarz).

The moment bounds are stated for natural exponents only. A real exponent `p` is handled by
monotonicity of `L^p` norms on a probability space, `eLpNorm_le_eLpNorm_of_exponent_le`.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- **Norm from an integer moment.** If the integral of `|f|^m` is at most `B^m`, then the
`L^m` norm of `f` is at most `B`. -/
theorem eLpNorm_le_of_lintegral_pow_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : Measurable f) {m : ℕ} (hm : 1 ≤ m) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ ω, ENNReal.ofReal (|f ω| ^ m) ∂μ ≤ ENNReal.ofReal (B ^ m)) :
    eLpNorm f (ENNReal.ofReal m) μ ≤ ENNReal.ofReal B := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hp0 : ENNReal.ofReal (m : ℝ) ≠ 0 := (ENNReal.ofReal_pos.mpr hmpos).ne'
  have hpt : ENNReal.ofReal (m : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hmpos.le]
  have hint : ∀ ω, ‖f ω‖ₑ ^ (m : ℝ) = ENNReal.ofReal (|f ω| ^ m) := by
    intro ω
    rw [← ofReal_norm, Real.norm_eq_abs, ← Real.rpow_natCast,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hmpos.le]
  simp only [hint]
  calc (∫⁻ ω, ENNReal.ofReal (|f ω| ^ m) ∂μ) ^ (1 / (m : ℝ))
      ≤ (ENNReal.ofReal (B ^ m)) ^ (1 / (m : ℝ)) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = ENNReal.ofReal B := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), one_div,
          Real.pow_rpow_inv_natCast hB (by omega)]

/-- **Tail split.** Let `f ≥ 0` be measurable and `t ≥ 0`, and let `A` be a measurable set that
contains `{f > t}`. Then the `m`-th moment is at most `t^m` times the total mass, plus the
Cauchy--Schwarz bound for the tail: `∫ f^m ≤ t^m μ(Ω) + (∫ f^{2m})^{1/2} μ(A)^{1/2}`. -/
theorem lintegral_pow_le_of_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf : Measurable f) (hnn : ∀ ω, 0 ≤ f ω) {m : ℕ} {t : ℝ}
    {A : Set Ω} (hA : MeasurableSet A) (hsub : ∀ ω, t < f ω → ω ∈ A) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ m) ∂μ ≤
      ENNReal.ofReal (t ^ m) * μ Set.univ +
        (∫⁻ ω, ENNReal.ofReal (f ω ^ (2 * m)) ∂μ) ^ (1 / 2 : ℝ) * (μ A) ^ (1 / 2 : ℝ) := by
  set F : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (f ω ^ m) with hFdef
  have hFm : Measurable F := (hf.pow_const m).ennreal_ofReal
  have hpt : ∀ ω, F ω ≤ ENNReal.ofReal (t ^ m) + A.indicator F ω := by
    intro ω
    by_cases hω : t < f ω
    · rw [Set.indicator_of_mem (hsub ω hω)]
      exact le_add_self
    · have hle : f ω ≤ t := not_lt.mp hω
      exact (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hnn ω) hle m)).trans le_self_add
  have hsplit : ∫⁻ ω, F ω ∂μ ≤ ∫⁻ ω, (ENNReal.ofReal (t ^ m) + A.indicator F ω) ∂μ :=
    lintegral_mono hpt
  rw [lintegral_add_left measurable_const, lintegral_const] at hsplit
  have hind : ∫⁻ ω, A.indicator F ω ∂μ = ∫⁻ ω, (F ω * A.indicator (fun _ => (1 : ℝ≥0∞)) ω) ∂μ := by
    refine lintegral_congr (fun ω => ?_)
    by_cases h : ω ∈ A
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  have hpq : Real.HolderConjugate 2 2 :=
    (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).mpr (by norm_num)
  have hg : Measurable (A.indicator (fun _ : Ω => (1 : ℝ≥0∞))) := measurable_const.indicator hA
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hFm.aemeasurable hg.aemeasurable
  have h1 : ∫⁻ ω, F ω ^ (2 : ℝ) ∂μ = ∫⁻ ω, ENNReal.ofReal (f ω ^ (2 * m)) ∂μ := by
    refine lintegral_congr (fun ω => ?_)
    rw [hFdef, ENNReal.ofReal_rpow_of_nonneg (pow_nonneg (hnn ω) m) (by norm_num),
      Real.rpow_two, ← pow_mul, mul_comm]
  have h2 : ∫⁻ ω, A.indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω ^ (2 : ℝ) ∂μ = μ A := by
    rw [← lintegral_indicator_one hA]
    refine lintegral_congr (fun ω => ?_)
    by_cases h : ω ∈ A
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  rw [h1, h2] at hcs
  calc ∫⁻ ω, F ω ∂μ ≤ ENNReal.ofReal (t ^ m) * μ Set.univ + ∫⁻ ω, A.indicator F ω ∂μ := hsplit
    _ = ENNReal.ofReal (t ^ m) * μ Set.univ + ∫⁻ ω, (F ω * A.indicator (fun _ => (1 : ℝ≥0∞)) ω) ∂μ := by rw [hind]
    _ ≤ ENNReal.ofReal (t ^ m) * μ Set.univ +
          (∫⁻ ω, ENNReal.ofReal (f ω ^ (2 * m)) ∂μ) ^ (1 / 2 : ℝ) * (μ A) ^ (1 / 2 : ℝ) :=
        add_le_add le_rfl hcs

/-- **Lintegral from an norm.** If the `L^m` norm of `f` is at most `B`, then the integral of
`|f|^m` is at most `B^m`. This is the converse of `eLpNorm_le_of_lintegral_pow_le`. -/
theorem lintegral_pow_le_of_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : Measurable f) {m : ℕ} (hm : 1 ≤ m) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm f (ENNReal.ofReal m) μ ≤ ENNReal.ofReal B) :
    ∫⁻ ω, ENNReal.ofReal (|f ω| ^ m) ∂μ ≤ ENNReal.ofReal (B ^ m) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hp0 : ENNReal.ofReal (m : ℝ) ≠ 0 := (ENNReal.ofReal_pos.mpr hmpos).ne'
  have hpt : ENNReal.ofReal (m : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hmpos.le] at h
  have hpow := ENNReal.rpow_le_rpow h hmpos.le
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hmpos.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hB hmpos.le, Real.rpow_natCast] at hpow
  refine le_trans (lintegral_mono (fun ω => ?_)) hpow
  rw [← ofReal_norm, Real.norm_eq_abs, ← Real.rpow_natCast,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hmpos.le]

/-- **Moment from a tail.** Let `μ` be a probability measure and `f` a measurable real function.
If the moment of order `2m` is at most `M^(2m)` and `μ {t ≤ |f|} ≤ q`, then the `m`-th
moment is at most `t^m + M^m √q`. -/
theorem lintegral_pow_le_tail_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {m : ℕ} {t M q : ℝ}
    (ht : 0 ≤ t) (hM : 0 ≤ M) (hq : 0 ≤ q)
    (hmom : ∫⁻ ω, ENNReal.ofReal (|f ω| ^ (2 * m)) ∂μ ≤ ENNReal.ofReal (M ^ (2 * m)))
    (htail : μ {ω | t ≤ |f ω|} ≤ ENNReal.ofReal q) :
    ∫⁻ ω, ENNReal.ofReal (|f ω| ^ m) ∂μ ≤ ENNReal.ofReal (t ^ m + M ^ m * Real.sqrt q) := by
  have habs : Measurable (fun ω => |f ω|) := continuous_abs.measurable.comp hf
  have hA : MeasurableSet {ω | t ≤ |f ω|} := measurableSet_le measurable_const habs
  have key := lintegral_pow_le_of_tail (μ := μ) (f := fun ω => |f ω|) habs
    (fun ω => abs_nonneg _) (m := m) (t := t) hA
    (fun ω hω => le_of_lt hω)
  have hMm : (ENNReal.ofReal (M ^ (2 * m))) ^ (1 / 2 : ℝ) = ENNReal.ofReal (M ^ m) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [show M ^ (2 * m) = (M ^ m) ^ 2 by ring, show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
  have hqq : (ENNReal.ofReal q) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt q) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hq (by norm_num), Real.sqrt_eq_rpow]
  calc ∫⁻ ω, ENNReal.ofReal (|f ω| ^ m) ∂μ
      ≤ ENNReal.ofReal (t ^ m) * μ Set.univ + (∫⁻ ω, ENNReal.ofReal (|f ω| ^ (2 * m)) ∂μ) ^
          (1 / 2 : ℝ) * (μ {ω | t ≤ |f ω|}) ^ (1 / 2 : ℝ) := key
    _ ≤ ENNReal.ofReal (t ^ m) * 1 + (ENNReal.ofReal (M ^ (2 * m))) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal q) ^ (1 / 2 : ℝ) := by
        rw [measure_univ]
        exact add_le_add le_rfl (mul_le_mul' (ENNReal.rpow_le_rpow hmom (by norm_num))
          (ENNReal.rpow_le_rpow htail (by norm_num)))
    _ = ENNReal.ofReal (t ^ m + M ^ m * Real.sqrt q) := by
        rw [hMm, hqq, mul_one, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add
          (by positivity) (by positivity)]

end Riesz1

end
end
