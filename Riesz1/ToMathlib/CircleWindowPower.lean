/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.Circle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Window integrals of functions of the circle distance

On the circle of length `L`, the window `(-L/2, L/2]` is a fundamental domain. For a function
`G` of one real variable and a point `c`, the window integral of `G(circDist L (y - c))` does not
depend on `c`, and it equals `2 ∫_{(0, L/2]} G`. This reduces every circle integral in the far
part of Lemma 5.3 to one-dimensional power integrals.

The file contains:
* `Riesz1.circDist_add_period`, `Riesz1.intervalIntegral_circDist_comp_sub`: translation
  invariance of window integrals.
* `Riesz1.setIntegral_window_circDist_comp_sub`: the reduction to `2 ∫_{(0, L/2]} G`.
* `Riesz1.integral_Ioc_rpow_of_lt_neg_one` and `Riesz1.setIntegral_Ioc_rpow_le_of_lt_neg_one`:
  the power integrals with exponent above and below `-1`.
-/

public section

open MeasureTheory Set Filter Real

namespace Riesz1

/-- The circle distance is `L`-periodic. -/
lemma circDist_add_period {L : ℝ} (hL : 0 < L) (y : ℝ) : circDist L (y + L) = circDist L y := by
  have h := circDist_add_int_mul hL y 1
  simpa using h

/-- A window integral of a function of `circDist L (y - c)` does not depend on the centre `c`. -/
theorem intervalIntegral_circDist_comp_sub {L : ℝ} (hL : 0 < L) (G : ℝ → ℝ) (c : ℝ) :
    ∫ y in (-(L / 2))..(L / 2), G (circDist L (y - c)) =
      ∫ y in (-(L / 2))..(L / 2), G (circDist L y) := by
  set f : ℝ → ℝ := fun y => G (circDist L y) with hf
  have hper : Function.Periodic f L := fun y => by
    simp only [hf, circDist_add_period hL]
  have h1 : ∫ y in (-(L / 2))..(L / 2), G (circDist L (y - c)) =
      ∫ x in (-(L / 2) - c)..(L / 2 - c), f x :=
    intervalIntegral.integral_comp_sub_right f c
  have h2 : L / 2 - c = (-(L / 2) - c) + L := by ring
  have h3 : ∫ x in (-(L / 2) - c)..(-(L / 2) - c + L), f x =
      ∫ x in (-(L / 2))..(-(L / 2) + L), f x := hper.intervalIntegral_add_eq _ _
  have h4 : -(L / 2) + L = L / 2 := by ring
  rw [h1, h2, h3, h4]

/-- On the window `[-L/2, L/2]`, the circle distance is the absolute value. -/
lemma circDist_eq_abs_of_mem_Icc {L y : ℝ} (hL : 0 < L) (hy : y ∈ Icc (-(L / 2)) (L / 2)) :
    circDist L y = |y| :=
  circDist_eq_abs hL (abs_le.2 ⟨hy.1, hy.2⟩)

/-- **Window reduction.** For `L > 0`, a centre `c` and a function `G` such that `y ↦ G |y|` is
interval integrable on `[-L/2, L/2]`, the window integral of `G(circDist L (y - c))` over
`(-L/2, L/2]` equals `2 ∫_{(0, L/2]} G`. -/
theorem setIntegral_window_circDist_comp_sub {L : ℝ} (hL : 0 < L) (G : ℝ → ℝ) (c : ℝ)
    (hG : IntervalIntegrable (fun y => G |y|) volume (-(L / 2)) (L / 2)) :
    ∫ y in Ioc (-(L / 2)) (L / 2), G (circDist L (y - c)) = 2 * ∫ u in Ioc 0 (L / 2), G u := by
  have hle : -(L / 2) ≤ L / 2 := by linarith
  have hL0 : 0 ≤ L / 2 := by linarith
  rw [← intervalIntegral.integral_of_le hle, intervalIntegral_circDist_comp_sub hL G c]
  have hcongr : ∫ y in (-(L / 2))..(L / 2), G (circDist L y) =
      ∫ y in (-(L / 2))..(L / 2), G |y| := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hle] at hy
    simp only [circDist_eq_abs_of_mem_Icc hL hy]
  rw [hcongr]
  have hI1 : IntervalIntegrable (fun y => G |y|) volume (-(L / 2)) 0 :=
    hG.mono_set (uIcc_subset_uIcc left_mem_uIcc
      (Set.mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩)))
  have hI2 : IntervalIntegrable (fun y => G |y|) volume 0 (L / 2) :=
    hG.mono_set (uIcc_subset_uIcc (Set.mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩))
      right_mem_uIcc)
  rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
  have hneg : ∫ y in (-(L / 2))..0, G |y| = ∫ y in (0)..(L / 2), G y := by
    have e1 : ∫ y in (-(L / 2))..0, G |y| = ∫ y in (-(L / 2))..0, G (-y) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le (by linarith)] at hy
      simp only [abs_of_nonpos hy.2]
    have h := intervalIntegral.integral_comp_neg (a := -(L / 2)) (b := (0 : ℝ)) (f := G)
    simp only [neg_zero, neg_neg] at h
    rw [e1, h]
  have hpos : ∫ y in (0)..(L / 2), G |y| = ∫ y in (0)..(L / 2), G y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hL0] at hy
    simp only [abs_of_nonneg hy.1]
  rw [hneg, hpos, intervalIntegral.integral_of_le hL0]
  ring

/-- The power integral over `(0, R]` for an exponent above `-1`. -/
theorem setIntegral_Ioc_rpow {e R : ℝ} (he : -1 < e) (hR : 0 < R) :
    ∫ u in Ioc 0 R, u ^ e = R ^ (e + 1) / (e + 1) := by
  rw [← intervalIntegral.integral_of_le hR.le, integral_rpow (Or.inl he)]
  rw [Real.zero_rpow (by linarith : e + 1 ≠ 0), sub_zero]

/-- A power with exponent above `-1` restricted to `(0, a]` and to the ball `(0, R]`: the
indicator of `(-∞, R]` lowers the integral to the power integral over `(0, R]`. -/
theorem setIntegral_Ioc_indicator_Iic_rpow_le {e R a : ℝ} (he : -1 < e) (hR : 0 < R) :
    ∫ u in Ioc 0 a, (Iic R).indicator (fun u => u ^ e) u ≤ R ^ (e + 1) / (e + 1) := by
  rw [setIntegral_indicator measurableSet_Iic, ← setIntegral_Ioc_rpow he hR]
  have hint : IntegrableOn (fun u : ℝ => u ^ e) (Ioc 0 R) :=
    (intervalIntegral.intervalIntegrable_rpow' he).1
  refine setIntegral_mono_set hint ?_ ?_
  · exact (ae_restrict_mem measurableSet_Ioc).mono fun u hu => Real.rpow_nonneg hu.1.le _
  · exact Filter.Eventually.of_forall fun u hu => ⟨hu.1.1, hu.2⟩

/-- A power with exponent below `-1` restricted to `[ρ, ∞)`: the integral over `(0, a]` is at
most the integral over `(ρ, ∞)`. -/
theorem setIntegral_Ioc_indicator_Ici_rpow_le {e ρ a : ℝ} (he : e < -1) (hρ : 0 < ρ) :
    ∫ u in Ioc 0 a, (Ici ρ).indicator (fun u => u ^ e) u ≤ -ρ ^ (e + 1) / (e + 1) := by
  rw [setIntegral_indicator measurableSet_Ici, ← integral_Ioi_rpow_of_lt he hρ,
    ← integral_Ici_eq_integral_Ioi]
  have hint : IntegrableOn (fun u : ℝ => u ^ e) (Ici ρ) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt he hρ
  refine setIntegral_mono_set hint ?_ ?_
  · exact (ae_restrict_mem measurableSet_Ici).mono fun u hu =>
      Real.rpow_nonneg (hρ.le.trans hu) _
  · exact Filter.Eventually.of_forall fun u hu => hu.2

end Riesz1
