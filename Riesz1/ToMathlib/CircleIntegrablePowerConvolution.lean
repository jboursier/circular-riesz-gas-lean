/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CirclePowerConvolution

/-!
# Convolution of two integrable circle singularities

When `0 < s,b < 1 < s+b`, the convolution of the two distance powers
is bounded by a constant times the center distance to the power `1-s-b`.
The constant is independent of the period. This supplies the positive
exponent value estimate in Lemma 5.3.
-/

public section

open MeasureTheory Set

namespace Riesz1.CirclePowerConvolution

/-- Separate the two integrable singularities and dominate the remaining
region by two truncated integrable tails. -/
theorem integrable_mul_le_split {u v D s b : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hD : 0 < D) (htri : D ≤ u + v)
    (hs : 0 < s) (hb : 0 < b) :
    u ^ (-s) * v ^ (-b) ≤
      (D / 2) ^ (-b) * (Iic (D / 2)).indicator (fun t => t ^ (-s)) u +
      (D / 2) ^ (-s) * (Iic (D / 2)).indicator (fun t => t ^ (-b)) v +
      (Ici (D / 2)).indicator (fun t => t ^ (-s-b)) u +
      (Ici (D / 2)).indicator (fun t => t ^ (-s-b)) v := by
  have hn (w e : ℝ) (hw : 0 ≤ w) :
      0 ≤ (Ici (D / 2)).indicator (fun t => t ^ e) w :=
    indicator_nonneg (fun _ _ => Real.rpow_nonneg hw _) _
  have hm (w e : ℝ) (hw : 0 ≤ w) :
      0 ≤ (Iic (D / 2)).indicator (fun t => t ^ e) w :=
    indicator_nonneg (fun _ _ => Real.rpow_nonneg hw _) _
  by_cases huR : u ≤ D / 2
  · rw [indicator_of_mem (show u ∈ Iic (D / 2) from huR)]
    have hp : v ^ (-b) ≤ (D / 2) ^ (-b) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have hh := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hu (-s))
    nlinarith [hn u (-s-b) hu, hn v (-s-b) hv, hm v (-b) hv,
      mul_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ D / 2) (-s)) (hm v (-b) hv)]
  · rw [indicator_of_notMem (show u ∉ Iic (D / 2) from huR), mul_zero,
      zero_add, indicator_of_mem (show u ∈ Ici (D / 2) from (lt_of_not_ge huR).le)]
    by_cases hvR : v ≤ D / 2
    · rw [indicator_of_mem (show v ∈ Iic (D / 2) from hvR)]
      have hp : u ^ (-s) ≤ (D / 2) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      have hh := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hv (-b))
      linarith [Real.rpow_nonneg hu (-s-b), hn v (-s-b) hv]
    · rw [indicator_of_notMem (show v ∉ Iic (D / 2) from hvR), mul_zero,
        zero_add, indicator_of_mem (show v ∈ Ici (D / 2) from (lt_of_not_ge hvR).le)]
      by_cases huv : u ≤ v
      · have hup : 0 < u := by linarith
        have hp := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hup huv (by linarith : -b ≤ 0))
          (Real.rpow_nonneg hu (-s))
        rw [← Real.rpow_add hup] at hp
        exact hp.trans (le_add_of_nonneg_right (Real.rpow_nonneg hv _))
      · have hvp : 0 < v := by linarith
        have hp := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos hvp (le_of_not_ge huv) (by linarith : -s ≤ 0))
          (Real.rpow_nonneg hv (-b))
        rw [← Real.rpow_add hvp] at hp
        exact hp.trans (le_add_of_nonneg_left (Real.rpow_nonneg hu _))

/-- The product convolution is absolutely integrable at distinct centers,
and has a period-independent bound with the sharp exponent. -/
theorem integral_integrable_power_mul_le {s b : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hb : 0 < b) (hb1 : b < 1)
    (hsb : 1 < s + b) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → ∀ x a : ℝ,
      0 < circDist L (x-a) →
      IntegrableOn (fun y => circDist L (y-x) ^ (-s) * circDist L (y-a) ^ (-b))
        (Ioc (-(L/2)) (L/2)) ∧
      (∫ y in Ioc (-(L/2)) (L/2),
        circDist L (y-x) ^ (-s) * circDist L (y-a) ^ (-b)) ≤
          C * circDist L (x-a) ^ (1-s-b) := by
  let K := 2 / (1-s) + 2 / (1-b) + 4 / (s+b-1)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K * (1/2 : ℝ) ^ (1-s-b), by positivity, fun L hL x a hD => ?_⟩
  have : Fact (0 < L) := ⟨hL⟩
  let D := circDist L (x-a)
  let R := D / 2
  have hR : 0 < R := by dsimp [R, D]; positivity
  let U := fun y => (Iic R).indicator (fun t : ℝ => t ^ (-s)) (circDist L (y-x))
  let V := fun y => (Iic R).indicator (fun t : ℝ => t ^ (-b)) (circDist L (y-a))
  let T := fun c y => (Ici R).indicator (fun t : ℝ => t ^ (-s-b)) (circDist L (y-c))
  let W := Ioc (-(L/2)) (L/2)
  have hUi : IntegrableOn U W := integrableOn_window_circDist_comp_sub hL _ x
    (intervalIntegrable_abs_rpow_indicator_Iic (by linarith) (by positivity))
  have hVi : IntegrableOn V W := integrableOn_window_circDist_comp_sub hL _ a
    (intervalIntegrable_abs_rpow_indicator_Iic (by linarith) (by positivity))
  have hTi (c : ℝ) : IntegrableOn (T c) W := integrableOn_window_circDist_comp_sub hL _ c
    (intervalIntegrable_abs_rpow_indicator_Ici (by linarith) hR (by positivity))
  let M := fun y => R ^ (-b) * U y + R ^ (-s) * V y + T x y + T a y
  have hMi : IntegrableOn M W :=
    (((hUi.const_mul _).add (hVi.const_mul _)).add (hTi x)).add (hTi a)
  have hd (y z : ℝ) : circDist L (y-z) = dist (y : AddCircle L) (z : AddCircle L) := by
    simp only [← dist_coe_zero_eq_circDist, AddCircle.coe_sub, dist_eq_norm, sub_zero]
  have hdm (z : ℝ) : Measurable (fun y : ℝ => circDist L (y-z)) := by
    simp_rw [hd]
    exact ((AddCircle.continuous_mk' L).dist continuous_const).measurable
  have hmajor (y : ℝ) : circDist L (y-x) ^ (-s) * circDist L (y-a) ^ (-b) ≤ M y := by
    apply integrable_mul_le_split (circDist_nonneg _ _) (circDist_nonneg _ _) hD ?_ hs hb
    simp_rw [hd]
    simpa only [dist_comm (x : AddCircle L) (y : AddCircle L)] using
      dist_triangle (x : AddCircle L) (y : AddCircle L) (a : AddCircle L)
  have hi : IntegrableOn (fun y => circDist L (y-x) ^ (-s) * circDist L (y-a) ^ (-b)) W := by
    refine hMi.mono' (((hdm x).pow_const (-s)).mul ((hdm a).pow_const (-b))).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (Real.rpow_nonneg (circDist_nonneg _ _) _) (Real.rpow_nonneg (circDist_nonneg _ _) _))]
    exact hmajor y
  refine ⟨hi, (integral_mono_ae hi hMi (ae_of_all _ hmajor)).trans ?_⟩
  have hUb : (∫ y in W, U y) ≤ 2 * R ^ (1-s) / (1-s) := by
    simpa only [U, show -s+1 = 1-s by ring] using
      setIntegral_window_circDist_rpow_Iic_le (e := -s) hL (by linarith) hR x
  have hVb : (∫ y in W, V y) ≤ 2 * R ^ (1-b) / (1-b) := by
    simpa only [V, show -b+1 = 1-b by ring] using
      setIntegral_window_circDist_rpow_Iic_le (e := -b) hL (by linarith) hR a
  have hTb (c : ℝ) : (∫ y in W, T c y) ≤ 2 * (-R ^ (-s-b+1) / (-s-b+1)) :=
    setIntegral_window_circDist_rpow_Ici_le hL (by linarith) hR c
  calc (∫ y in W, M y) = R ^ (-b) * (∫ y in W, U y) +
        R ^ (-s) * (∫ y in W, V y) + (∫ y in W, T x y) + (∫ y in W, T a y) := by
        dsimp only [M]
        rw [integral_add (f := fun y => R ^ (-b) * U y + R ^ (-s) * V y + T x y)
            (((hUi.const_mul _).add (hVi.const_mul _)).add (hTi x)) (hTi a),
          integral_add (f := fun y => R ^ (-b) * U y + R ^ (-s) * V y)
            ((hUi.const_mul _).add (hVi.const_mul _)) (hTi x),
          integral_add (hUi.const_mul _) (hVi.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ R ^ (-b) * (2 * R ^ (1-s) / (1-s)) +
        R ^ (-s) * (2 * R ^ (1-b) / (1-b)) +
          2 * (-R ^ (-s-b+1) / (-s-b+1)) + 2 * (-R ^ (-s-b+1) / (-s-b+1)) := by
      exact add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hUb (Real.rpow_nonneg hR.le _))
        (mul_le_mul_of_nonneg_left hVb (Real.rpow_nonneg hR.le _))) (hTb x)) (hTb a)
    _ = K * R ^ (1-s-b) := by
      have e₁ : R ^ (-b) * R ^ (1-s) = R ^ (1-s-b) := by
        rw [← Real.rpow_add hR]; congr 1; ring
      have e₂ : R ^ (-s) * R ^ (1-b) = R ^ (1-s-b) := by
        rw [← Real.rpow_add hR]; congr 1; ring
      rw [show -s-b+1 = 1-s-b by ring]
      calc _ = 2 / (1-s) * (R ^ (-b) * R ^ (1-s)) +
            2 / (1-b) * (R ^ (-s) * R ^ (1-b)) +
              4 / (s+b-1) * R ^ (1-s-b) := by
            rw [show 1-s-b = -(s+b-1) by ring, div_neg]
            ring
        _ = _ := by rw [e₁, e₂]; dsimp [K]; ring
    _ = _ := by
      dsimp only [R]
      rw [show D / 2 = (1/2 : ℝ) * D by ring, Real.mul_rpow (by norm_num) hD.le]
      ring

end Riesz1.CirclePowerConvolution
