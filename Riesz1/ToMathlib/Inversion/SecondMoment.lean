/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Exponential

/-!
# A second moment split at a deviation threshold

Cauchy--Schwarz bounds the contribution above the threshold using a fourth
moment and the probability of the exceptional event.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

theorem inversion_secondMoment_split {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {t D q : ℝ}
    (ht : 0 ≤ t) (hD : 0 ≤ D) (hq : 0 ≤ q)
    (hmom : ∫⁻ x, ENNReal.ofReal (f x ^ 4) ∂μ ≤ ENNReal.ofReal D)
    (htail : μ {x | t ≤ |f x|} ≤ ENNReal.ofReal q) :
    ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ ≤
      ENNReal.ofReal (t ^ 2 + Real.sqrt D * Real.sqrt q) := by
  let A : Set Ω := {x | t ≤ |f x|}
  let F : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal (f x ^ 2)
  have hA : MeasurableSet A := measurableSet_le measurable_const
    (continuous_abs.measurable.comp hf)
  have hF : Measurable F := (hf.pow_const 2).ennreal_ofReal
  have hpt (x : Ω) : F x ≤ ENNReal.ofReal (t ^ 2) + A.indicator F x := by
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      exact le_add_self
    · rw [Set.indicator_of_notMem hx, add_zero]
      apply ENNReal.ofReal_le_ofReal
      have h : |f x| ≤ t := (not_le.mp hx).le
      nlinarith [sq_abs (f x), abs_nonneg (f x)]
  have hs := lintegral_mono (μ := μ) hpt
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one] at hs
  have hind : A.indicator F = fun x => F x * A.indicator (fun _ => (1 : ℝ≥0∞)) x := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  have hpq : Real.HolderConjugate 2 2 :=
    (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).mpr (by norm_num)
  have hg : Measurable (A.indicator (fun _ : Ω => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hA
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hF.aemeasurable hg.aemeasurable
  have hfour : (fun x => F x ^ (2 : ℝ)) = fun x => ENNReal.ofReal (f x ^ 4) := by
    funext x
    dsimp [F]
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), Real.rpow_two]
    congr 1
    ring
  have hone : (∫⁻ x, A.indicator (fun _ : Ω => (1 : ℝ≥0∞)) x ^ (2 : ℝ) ∂μ) = μ A := by
    rw [← lintegral_indicator_one hA]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [hfour, hone] at hcs
  have hroot (a : ℝ) (ha : 0 ≤ a) :
      (ENNReal.ofReal a) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt a) := by
    rw [ENNReal.ofReal_rpow_of_nonneg ha (by norm_num), Real.sqrt_eq_rpow]
  calc (∫⁻ x, F x ∂μ)
      ≤ ENNReal.ofReal (t ^ 2) + ∫⁻ x, A.indicator F x ∂μ := hs
    _ ≤ ENNReal.ofReal (t ^ 2) +
        (ENNReal.ofReal D) ^ (1 / 2 : ℝ) * (ENNReal.ofReal q) ^ (1 / 2 : ℝ) := by
      rw [hind]
      exact add_le_add le_rfl (hcs.trans (mul_le_mul'
        (ENNReal.rpow_le_rpow hmom (by norm_num))
        (ENNReal.rpow_le_rpow htail (by norm_num))))
    _ = _ := by
      rw [hroot D hD, hroot q hq, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
        ← ENNReal.ofReal_add (sq_nonneg _) (by positivity)]

/-- Polynomial factors can be absorbed into a stretched exponential on `[1,∞)`. -/
theorem inversion_power_exp_bounded (b : ℝ) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x →
      x ^ b * Real.exp (-c * x ^ a) ≤ K := by
  let n : ℕ := ⌈max b 0 / a⌉₊
  have hb : b ≤ (n : ℝ) * a := by
    have hn : max b 0 / a ≤ (n : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ ha] at hn
    exact (le_max_left b 0).trans hn
  refine ⟨(n.factorial : ℝ) / c ^ n, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hexp := Real.pow_div_factorial_le_exp (c * x ^ a) (by positivity) n
  have hpow : (x ^ a) ^ n = x ^ ((n : ℝ) * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, mul_comm]
  have hi : Real.exp (-c * x ^ a) ≤
      (n.factorial : ℝ) / c ^ n * (x ^ ((n : ℝ) * a))⁻¹ := by
    rw [show -c * x ^ a = -(c * x ^ a) by ring, Real.exp_neg]
    calc (Real.exp (c * x ^ a))⁻¹ ≤ ((c * x ^ a) ^ n / n.factorial)⁻¹ :=
        inv_anti₀ (by positivity) hexp
      _ = _ := by rw [mul_pow, hpow]; field_simp
  have hxb : x ^ b * (x ^ ((n : ℝ) * a))⁻¹ ≤ 1 := by
    rw [← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  calc x ^ b * Real.exp (-c * x ^ a)
      ≤ x ^ b * ((n.factorial : ℝ) / c ^ n * (x ^ ((n : ℝ) * a))⁻¹) :=
        mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg hx0.le _)
    _ = (n.factorial : ℝ) / c ^ n * (x ^ b * (x ^ ((n : ℝ) * a))⁻¹) := by ring
    _ ≤ (n.factorial : ℝ) / c ^ n * 1 :=
      mul_le_mul_of_nonneg_left hxb (by positivity)
    _ = _ := mul_one _

end Riesz1

end
end
