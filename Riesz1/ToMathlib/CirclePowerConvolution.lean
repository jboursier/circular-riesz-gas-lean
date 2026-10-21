/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleWindowPowerIntegrable
public import Riesz1.ToMathlib.FiniteMarkMollify

/-!
# A truncated singular convolution with a circular power

Split the integration variable according to whether it is closer than half the
center-to-mark distance to the mark. On that part the other distance is bounded
below. On the complement the marked power is bounded. The resulting two power
integrals give a uniform estimate without a dyadic annulus sum. These are the
far-integral estimates needed for Lemma 5.3.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1
namespace CirclePowerConvolution

/-- A two-distance split of a singular product. The truncation makes the
nonintegrable power harmless at zero, and the marked power is integrable for
`b < 1` in the integral application below. -/
theorem truncated_mul_le_split {u v D ρ e b : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hD : 0 < D) (_hρ : 0 < ρ)
    (htriangle : D ≤ u + v) (he : e ≤ 0) (hb : 0 < b) :
    (Ici ρ).indicator (fun t => t ^ e) u * v ^ (-b) ≤
      (D / 2) ^ e * (Iic (D / 2)).indicator (fun t => t ^ (-b)) v +
        (D / 2) ^ (-b) * (Ici ρ).indicator (fun t => t ^ e) u := by
  by_cases hur : ρ ≤ u
  · rw [indicator_of_mem (show u ∈ Ici ρ from hur)]
    by_cases hvD : v ≤ D / 2
    · rw [indicator_of_mem (show v ∈ Iic (D / 2) from hvD)]
      have hpow : u ^ e ≤ (D / 2) ^ e :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) he
      exact (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hv _)).trans
        (le_add_of_nonneg_right (by positivity))
    · rw [indicator_of_notMem (show v ∉ Iic (D / 2) from hvD), mul_zero, zero_add]
      have hpow : v ^ (-b) ≤ (D / 2) ^ (-b) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (le_of_not_ge hvD) (by linarith)
      calc u ^ e * v ^ (-b) ≤ u ^ e * (D / 2) ^ (-b) :=
            mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hu _)
        _ = _ := mul_comm _ _
  · rw [indicator_of_notMem (show u ∉ Ici ρ from hur), zero_mul, mul_zero, add_zero]
    by_cases hvD : v ≤ D / 2
    · rw [indicator_of_mem (show v ∈ Iic (D / 2) from hvD)]
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hv _)
    · rw [indicator_of_notMem (show v ∉ Iic (D / 2) from hvD), mul_zero]

/-- The far convolution of a nonintegrable circular power with one integrable
marked power is absolutely integrable. Both numerical power integrals are
uniform in the circle length and in the two centers. -/
theorem integral_truncated_mul_le {L e b ρ : ℝ} (hL : 0 < L)
    (he : e < -1) (hb : 0 < b) (hb1 : b < 1) (hρ : 0 < ρ)
    (x a : ℝ) (hD : 0 < circDist L (x - a)) :
    IntegrableOn (fun y =>
      (Ici ρ).indicator (fun t => t ^ e) (circDist L (y - x)) *
        circDist L (y - a) ^ (-b)) (Ioc (-(L / 2)) (L / 2)) ∧
    (∫ y in Ioc (-(L / 2)) (L / 2),
      (Ici ρ).indicator (fun t => t ^ e) (circDist L (y - x)) *
        circDist L (y - a) ^ (-b)) ≤
      (circDist L (x - a) / 2) ^ e *
        (2 * (circDist L (x - a) / 2) ^ (1 - b) / (1 - b)) +
      (circDist L (x - a) / 2) ^ (-b) * (2 * (-ρ ^ (e + 1) / (e + 1))) := by
  have : Fact (0 < L) := ⟨hL⟩
  let D := circDist L (x - a)
  let U := fun y => (Ici ρ).indicator (fun t : ℝ => t ^ e) (circDist L (y - x))
  let V := fun y => (Iic (D / 2)).indicator (fun t : ℝ => t ^ (-b))
    (circDist L (y - a))
  have hd (y z : ℝ) : circDist L (y - z) = dist (y : AddCircle L) (z : AddCircle L) := by
    simp only [← dist_coe_zero_eq_circDist, AddCircle.coe_sub, dist_eq_norm, sub_zero]
  have hdistm (z : ℝ) : Measurable (fun y : ℝ => circDist L (y - z)) := by
    simp_rw [hd]
    exact ((AddCircle.continuous_mk' L).dist continuous_const).measurable
  have hUi : IntegrableOn U (Ioc (-(L / 2)) (L / 2)) :=
    integrableOn_window_circDist_comp_sub hL _ x
      (intervalIntegrable_abs_rpow_indicator_Ici (by linarith) hρ (by positivity))
  have hVi : IntegrableOn V (Ioc (-(L / 2)) (L / 2)) :=
    integrableOn_window_circDist_comp_sub hL _ a
      (intervalIntegrable_abs_rpow_indicator_Iic (by linarith) (by positivity))
  have hUn (y : ℝ) : 0 ≤ U y := by
    dsimp only [U]
    by_cases hy : ρ ≤ circDist L (y - x)
    · rw [indicator_of_mem (show circDist L (y - x) ∈ Ici ρ from hy)]
      exact Real.rpow_nonneg (by rw [hd]; exact dist_nonneg) _
    · rw [indicator_of_notMem (show circDist L (y - x) ∉ Ici ρ from hy)]
  have hmajor (y : ℝ) : U y * circDist L (y - a) ^ (-b) ≤
      (D / 2) ^ e * V y + (D / 2) ^ (-b) * U y := by
    apply truncated_mul_le_split (by rw [hd]; exact dist_nonneg)
      (by rw [hd]; exact dist_nonneg) hD hρ ?_ (by linarith) hb
    simp_rw [hd]
    simpa only [dist_comm (x : AddCircle L) (y : AddCircle L)] using
      dist_triangle (x : AddCircle L) (y : AddCircle L) (a : AddCircle L)
  have hMi : IntegrableOn (fun y => (D / 2) ^ e * V y + (D / 2) ^ (-b) * U y)
      (Ioc (-(L / 2)) (L / 2)) := by
    exact (hVi.const_mul _).add (hUi.const_mul _)
  have hproduct : IntegrableOn (fun y => U y * circDist L (y - a) ^ (-b))
      (Ioc (-(L / 2)) (L / 2)) := by
    refine hMi.mono'
      ((((measurable_id.pow_const e).indicator measurableSet_Ici).comp (hdistm x)).mul
        ((hdistm a).pow_const (-b))).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hUn y)
      (Real.rpow_nonneg (by rw [hd]; exact dist_nonneg) _))]
    exact hmajor y
  refine ⟨hproduct, ?_⟩
  have hmono := integral_mono_ae hproduct hMi (ae_of_all _ hmajor)
  rw [integral_add (hVi.const_mul _) (hUi.const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  apply hmono.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
    have hh : 0 < D / 2 := by dsimp [D]; linarith
    have hbnd := setIntegral_window_circDist_rpow_Iic_le (e := -b) hL
      (by linarith) hh a
    simpa only [V, show -b + 1 = 1 - b by ring] using hbnd
  · apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
    exact setIntegral_window_circDist_rpow_Ici_le hL he hρ x

/-- Uniform far-power bound at a radius no larger than the center-to-mark
separation. For `e = -1-s`, its order is `r^(-s-b)`, exactly the profile
 derivative exponent in the inverse-transport application. -/
theorem integral_far_power_mul_le {s b : ℝ} (hs : 0 < s)
    (hb : 0 < b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → ∀ x a r : ℝ, 0 < r →
      r ≤ circDist L (x - a) →
      IntegrableOn (fun y =>
        (Ici (r / 4)).indicator (fun t => t ^ (-s - 1)) (circDist L (y - x)) *
          circDist L (y - a) ^ (-b)) (Ioc (-(L / 2)) (L / 2)) ∧
      (∫ y in Ioc (-(L / 2)) (L / 2),
        (Ici (r / 4)).indicator (fun t => t ^ (-s - 1)) (circDist L (y - x)) *
          circDist L (y - a) ^ (-b)) ≤ C * r ^ (-s - b) := by
  let C₀ := 2 * (1 / 2 : ℝ) ^ (-s - b) / (1 - b)
  let C₁ := 2 / s * (1 / 2 : ℝ) ^ (-b) * (1 / 4 : ℝ) ^ (-s)
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  refine ⟨C₀ + C₁, by positivity, fun L hL x a r hr hrD => ?_⟩
  let D := circDist L (x - a)
  have hD : 0 < D := lt_of_lt_of_le hr hrD
  obtain ⟨hi, hbound⟩ := integral_truncated_mul_le hL
    (show -s - 1 < -1 by linarith) hb hb1 (by positivity : 0 < r / 4) x a hD
  refine ⟨hi, hbound.trans ?_⟩
  have he₀ : (D / 2) ^ (-s - 1) * (2 * (D / 2) ^ (1 - b) / (1 - b)) =
      C₀ * D ^ (-s - b) := by
    calc _ = (2 / (1 - b)) * ((D / 2) ^ (-s - 1) * (D / 2) ^ (1 - b)) := by ring
      _ = (2 / (1 - b)) * (D / 2) ^ (-s - b) := by
        rw [← Real.rpow_add (by positivity : 0 < D / 2)]
        congr 2
        ring
      _ = _ := by
        rw [show D / 2 = (1 / 2 : ℝ) * D by ring,
          Real.mul_rpow (by norm_num : 0 ≤ (1 / 2 : ℝ)) hD.le]
        dsimp [C₀]
        ring
  have he₁ : (D / 2) ^ (-b) * (2 * (-(r / 4) ^ (-s - 1 + 1) / (-s - 1 + 1))) =
      C₁ * (D ^ (-b) * r ^ (-s)) := by
    rw [show -s - 1 + 1 = -s by ring,
      show D / 2 = (1 / 2 : ℝ) * D by ring,
      show r / 4 = (1 / 4 : ℝ) * r by ring,
      Real.mul_rpow (by norm_num : 0 ≤ (1 / 2 : ℝ)) hD.le,
      Real.mul_rpow (by norm_num : 0 ≤ (1 / 4 : ℝ)) hr.le]
    dsimp [C₁]
    ring
  change (D / 2) ^ (-s - 1) * (2 * (D / 2) ^ (1 - b) / (1 - b)) +
    (D / 2) ^ (-b) * (2 * (-(r / 4) ^ (-s - 1 + 1) / (-s - 1 + 1))) ≤ _
  rw [he₀, he₁]
  have hpow₀ : D ^ (-s - b) ≤ r ^ (-s - b) :=
    Real.rpow_le_rpow_of_nonpos hr hrD (by linarith)
  have hpow₁ : D ^ (-b) * r ^ (-s) ≤ r ^ (-s - b) := by
    calc _ ≤ r ^ (-b) * r ^ (-s) := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos hr hrD (by linarith)) (Real.rpow_nonneg hr.le _)
      _ = _ := by rw [← Real.rpow_add hr]; congr 1; ring
  calc _ ≤ C₀ * r ^ (-s - b) + C₁ * r ^ (-s - b) := add_le_add
        (mul_le_mul_of_nonneg_left hpow₀ hC₀.le)
        (mul_le_mul_of_nonneg_left hpow₁ hC₁.le)
    _ = _ := by ring

end CirclePowerConvolution
end Riesz1
