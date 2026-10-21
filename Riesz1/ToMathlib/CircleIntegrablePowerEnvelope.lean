/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleIntegrablePowerConvolution
public import Riesz1.ToMathlib.CircleFiniteMarkConvolution

/-!
# Inverse-power convolutions against a finite marked envelope

An `L¹` bound handles displacements larger than one, so the constant stays
uniform as the circle grows. The near contribution uses the convolution
of two integrable singularities. Used in Lemma 5.3.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1.CirclePowerConvolution

/-- Uniform value bound for a power convolution of a density with finitely
many integrable marked singularities and a bounded `L¹` norm. -/
theorem integral_power_envelope_le {s b : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hb : 0 < b) (hb1 : b < 1)
    (hsb : 1 < s+b) (ι : Type*) [Fintype ι] :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ), 0 < L → ∀ (marks : ι → ℝ) (x : ℝ),
      (∀ j, 0 < circDist L (x-marks j)) →
      ∀ (q : ℝ → ℝ) (A : ℝ), 0 ≤ A → Measurable q →
      IntegrableOn q (Ioc (-(L/2)) (L/2)) →
      (∫ y in Ioc (-(L/2)) (L/2), |q y|) ≤ A →
      (∀ᵐ y : ℝ ∂(volume.restrict (Ioc (-(L/2)) (L/2))),
        |q y| ≤ A * (1 + ∑ j, circDist L (y-marks j) ^ (-b))) →
      IntegrableOn (fun y => circDist L (y-x) ^ (-s) * |q y|)
        (Ioc (-(L/2)) (L/2)) ∧
      (∫ y in Ioc (-(L/2)) (L/2), circDist L (y-x) ^ (-s) * |q y|) ≤
        C * A * (1 + ∑ j, circDist L (x-marks j) ^ (1-s-b)) := by
  classical
  obtain ⟨K, hK, hconv⟩ := integral_integrable_power_mul_le hs hs1 hb hb1 hsb
  let C := 1 + 2 / (1-s) + K
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun L hL marks x hx q A hA hqm hqi hnorm henv => ?_⟩
  have : Fact (0 < L) := ⟨hL⟩
  let W := Ioc (-(L/2)) (L/2)
  let U := fun y => (Iic 1).indicator (fun t : ℝ => t ^ (-s)) (circDist L (y-x))
  let V := fun j y => circDist L (y-x) ^ (-s) * circDist L (y-marks j) ^ (-b)
  let M := fun y => |q y| + A * U y + A * ∑ j, V j y
  have hUi : IntegrableOn U W := integrableOn_window_circDist_comp_sub hL _ x
    (intervalIntegrable_abs_rpow_indicator_Iic (by linarith) (by positivity))
  have hVi (j : ι) : IntegrableOn (V j) W := (hconv L hL x (marks j) (hx j)).1
  have hSi : IntegrableOn (fun y => ∑ j, V j y) W := integrable_finsetSum _ fun j _ => hVi j
  have hMi : IntegrableOn M W := (hqi.abs.add (hUi.const_mul A)).add (hSi.const_mul A)
  have hmajor : ∀ᵐ y : ℝ ∂(volume.restrict W), circDist L (y-x) ^ (-s) * |q y| ≤ M y := by
    filter_upwards [henv] with y hy
    have hn : 0 ≤ circDist L (y-x) ^ (-s) := Real.rpow_nonneg (circDist_nonneg _ _) _
    have hVn : 0 ≤ ∑ j, V j y := Finset.sum_nonneg fun j _ =>
      mul_nonneg hn (Real.rpow_nonneg (circDist_nonneg _ _) _)
    by_cases hd : circDist L (y-x) ≤ 1
    · have hUy : U y = circDist L (y-x) ^ (-s) :=
        indicator_of_mem (show circDist L (y-x) ∈ Iic 1 from hd) _
      calc _ ≤ circDist L (y-x) ^ (-s) * (A * (1 + ∑ j, circDist L (y-marks j) ^ (-b))) :=
            mul_le_mul_of_nonneg_left hy hn
        _ = A * U y + A * ∑ j, V j y := by
          rw [hUy]
          simp only [V, ← Finset.mul_sum]
          ring
        _ ≤ M y := by dsimp [M]; linarith [abs_nonneg (q y)]
    · have hp : circDist L (y-x) ^ (-s) ≤ 1 := by
        simpa only [Real.one_rpow] using Real.rpow_le_rpow_of_nonpos
          (by norm_num : (0 : ℝ) < 1) (le_of_not_ge hd) (by linarith : -s ≤ 0)
      have hUy : U y = 0 :=
        indicator_of_notMem (show circDist L (y-x) ∉ Iic 1 from hd) _
      have hh := mul_le_mul_of_nonneg_right hp (abs_nonneg (q y))
      dsimp only [M]
      rw [hUy, mul_zero, add_zero]
      simpa only [one_mul] using hh.trans (le_add_of_nonneg_right (mul_nonneg hA hVn))
  have hdmeas : Measurable (fun y : ℝ => circDist L (y-x)) := by
    simp_rw [← dist_coe_zero_eq_circDist]
    exact (((AddCircle.continuous_mk' L).comp (continuous_id.sub continuous_const)).dist
      continuous_const).measurable
  have hi : IntegrableOn (fun y => circDist L (y-x) ^ (-s) * |q y|) W := by
    refine hMi.mono' (((hdmeas.pow_const (-s)).mul (continuous_abs.measurable.comp hqm)).aestronglyMeasurable) ?_
    filter_upwards [hmajor] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (Real.rpow_nonneg (circDist_nonneg _ _) _) (abs_nonneg _))]
    exact hy
  refine ⟨hi, (integral_mono_ae hi hMi hmajor).trans ?_⟩
  have hUb : (∫ y in W, U y) ≤ 2 / (1-s) := by
    simpa only [U, show -s+1 = 1-s by ring, Real.one_rpow, mul_one] using
      setIntegral_window_circDist_rpow_Iic_le (e := -s) hL (by linarith) (by norm_num : (0 : ℝ) < 1) x
  have hVb : (∫ y in W, ∑ j, V j y) ≤ K * ∑ j, circDist L (x-marks j) ^ (1-s-b) := by
    rw [integral_finsetSum _ fun j _ => hVi j, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => (hconv L hL x (marks j) (hx j)).2
  rw [show M = fun y => |q y| + A * U y + A * ∑ j, V j y from rfl,
    integral_add (f := fun y => |q y| + A * U y)
      (hqi.abs.add (hUi.const_mul A)) (hSi.const_mul A),
    integral_add hqi.abs (hUi.const_mul A), integral_const_mul, integral_const_mul]
  have hsum : 0 ≤ ∑ j, circDist L (x-marks j) ^ (1-s-b) :=
    Finset.sum_nonneg fun j _ => Real.rpow_nonneg (circDist_nonneg _ _) _
  calc _ ≤ A + A * (2 / (1-s)) + A * (K * ∑ j, circDist L (x-marks j) ^ (1-s-b)) :=
      add_le_add (add_le_add hnorm (mul_le_mul_of_nonneg_left hUb hA))
        (mul_le_mul_of_nonneg_left hVb hA)
    _ ≤ _ := by
      dsimp [C]
      nlinarith [mul_nonneg hA hsum, mul_nonneg (by positivity : 0 ≤ 2 / (1-s)) (mul_nonneg hA hsum),
        mul_nonneg hK.le hA]

end Riesz1.CirclePowerConvolution
