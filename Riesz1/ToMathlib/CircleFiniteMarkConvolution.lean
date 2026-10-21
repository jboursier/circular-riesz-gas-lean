/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CirclePowerConvolution
public import Riesz1.ToMathlib.FiniteMarkDistance

/-!
# Uniform far convolutions against a finite marked envelope

The per-mark circular power convolution estimate extends to a transport
density bounded by the capped mark-distance power. The constant is chosen
before the circle, the marks, the density and the evaluation point. This
includes the constant part of the transport envelope, which would otherwise
introduce a spurious circle-length factor in Lemma 5.3.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1.CirclePowerConvolution

/-- Integrating a far circular power against a finite marked envelope costs
`r^(-s-b)`, uniformly over positive circle lengths and all mark positions. -/
theorem integral_far_power_envelope_le {s b : ℝ} (hs : 0 < s)
    (hb : 0 < b) (hb1 : b < 1) (ι : Type*) [Fintype ι] :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → ∀ (marks : ι → ℝ) (x r : ℝ),
      0 < r → r ≤ 1 → (∀ j, r ≤ circDist L (x - marks j)) →
      ∀ (q : ℝ → ℝ) (A : ℝ), 0 ≤ A → Measurable q →
        (∀ᵐ y : ℝ ∂(volume.restrict (Ioc (-(L / 2)) (L / 2))),
          |q y| ≤ A * (1 + ∑ j, circDist L (y - marks j) ^ (-b))) →
        IntegrableOn (fun y =>
          (Ici (r / 4)).indicator (fun t => t ^ (-s - 1)) (circDist L (y - x)) * |q y|)
          (Ioc (-(L / 2)) (L / 2)) ∧
        (∫ y in Ioc (-(L / 2)) (L / 2),
          (Ici (r / 4)).indicator (fun t => t ^ (-s - 1)) (circDist L (y - x)) * |q y|) ≤
          C * A * r ^ (-s - b) := by
  obtain ⟨D, hD, hmark⟩ := integral_far_power_mul_le hs hb hb1
  let D₀ := 2 / s * (1 / 4 : ℝ) ^ (-s)
  have hD₀ : 0 < D₀ := by dsimp [D₀]; positivity
  refine ⟨D₀ + Fintype.card ι * D, by positivity, ?_⟩
  intro L hL marks x r hr hr1 hsep q A hA hqm hq
  let W := Ioc (-(L / 2)) (L / 2)
  let U := fun y => (Ici (r / 4)).indicator (fun t : ℝ => t ^ (-s - 1)) (circDist L (y - x))
  let V := fun j y => U y * circDist L (y - marks j) ^ (-b)
  have hUi : IntegrableOn U W := integrableOn_window_circDist_comp_sub hL _ x
    (intervalIntegrable_abs_rpow_indicator_Ici (by linarith) (by positivity) (by positivity))
  have hVi (j : ι) : IntegrableOn (V j) W :=
    (hmark L hL x (marks j) r hr (hsep j)).1
  have hUn (y : ℝ) : 0 ≤ U y := by
    dsimp [U]
    exact indicator_nonneg (fun t _ => Real.rpow_nonneg (circDist_nonneg L (y - x)) _) _
  have hsumI : IntegrableOn (fun y => U y + ∑ j, V j y) W :=
    hUi.add (integrable_finsetSum _ fun j _ => hVi j)
  have hMi : IntegrableOn (fun y => A * (U y + ∑ j, V j y)) W := hsumI.const_mul A
  have hmajor : ∀ᵐ y : ℝ ∂(volume.restrict W),
      U y * |q y| ≤ A * (U y + ∑ j, V j y) := by
    filter_upwards [hq] with y hy
    calc _ ≤ U y * (A * (1 + ∑ j, circDist L (y - marks j) ^ (-b))) :=
          mul_le_mul_of_nonneg_left hy (hUn y)
      _ = A * (U y * (1 + ∑ j, circDist L (y - marks j) ^ (-b))) := by ring
      _ = _ := by rw [mul_add, mul_one, Finset.mul_sum]
  have hmeas : AEStronglyMeasurable (fun y => U y * |q y|) (volume.restrict W) := by
    have : Fact (0 < L) := ⟨hL⟩
    have hd : Measurable (fun y : ℝ => circDist L (y - x)) := by
      simp_rw [← dist_coe_zero_eq_circDist]
      exact ((AddCircle.continuous_mk' L).comp
        (continuous_id.sub continuous_const)).dist continuous_const |>.measurable
    exact ((((measurable_id.pow_const (-s - 1)).indicator measurableSet_Ici).comp hd).mul
      (continuous_abs.measurable.comp hqm)).aestronglyMeasurable
  have hi : IntegrableOn (fun y => U y * |q y|) W := by
    apply hMi.mono' hmeas
    filter_upwards [hmajor] with y hy
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hUn y) (abs_nonneg _))] using hy
  refine ⟨hi, (integral_mono_ae hi hMi hmajor).trans ?_⟩
  rw [integral_const_mul, integral_add hUi (integrable_finsetSum _ fun j _ => hVi j),
    integral_finsetSum _ fun j _ => hVi j]
  have hUb : (∫ y in W, U y) ≤ D₀ * r ^ (-s - b) := by
    have ht := setIntegral_window_circDist_rpow_Ici_le hL
      (show -s - 1 < -1 by linarith) (by positivity : 0 < r / 4) x
    have he : 2 * (-(r / 4) ^ (-s - 1 + 1) / (-s - 1 + 1)) = D₀ * r ^ (-s) := by
      rw [show -s - 1 + 1 = -s by ring, show r / 4 = (1 / 4 : ℝ) * r by ring,
        Real.mul_rpow (by norm_num : 0 ≤ (1 / 4 : ℝ)) hr.le]
      dsimp [D₀]
      ring
    exact (ht.trans_eq he).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)) hD₀.le)
  have hVb : (∑ j, ∫ y in W, V j y) ≤ (Fintype.card ι : ℝ) * (D * r ^ (-s - b)) := by
    calc _ ≤ ∑ _j : ι, D * r ^ (-s - b) :=
          Finset.sum_le_sum fun j _ => (hmark L hL x (marks j) r hr (hsep j)).2
      _ = _ := by simp
  calc A * _ ≤ A * (D₀ * r ^ (-s - b) + (Fintype.card ι : ℝ) * (D * r ^ (-s - b))) :=
        mul_le_mul_of_nonneg_left (add_le_add hUb hVb) hA
    _ = _ := by ring

/-- The capped-distance transport bound supplies the whole envelope without
adding a hypothesis at the marks. Their real lifts form a countable null set. -/
theorem integral_far_power_capped_le {s b : ℝ} (hs : 0 < s)
    (hb : 0 < b) (hb1 : b < 1) (ι : Type*) [Fintype ι] [Nonempty ι] :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ) [Fact (0 < L)] (marks : ι → ℝ) (x r : ℝ),
      0 < r → r ≤ cappedMarkDistance (fun j => (marks j : AddCircle L)) (x : AddCircle L) →
      ∀ (q : ℝ → ℝ) (A : ℝ), 0 ≤ A → Measurable q →
        (∀ y : ℝ, (∀ j, (y : AddCircle L) ≠ (marks j : AddCircle L)) →
          |q y| ≤ A * cappedMarkDistance (fun j => (marks j : AddCircle L))
            (y : AddCircle L) ^ (-b)) →
        IntegrableOn (fun y =>
          (Ici (r / 4)).indicator (fun t => t ^ (-s - 1)) (circDist L (y - x)) * |q y|)
          (Ioc (-(L / 2)) (L / 2)) ∧
        (∫ y in Ioc (-(L / 2)) (L / 2),
          (Ici (r / 4)).indicator (fun t => t ^ (-s - 1)) (circDist L (y - x)) * |q y|) ≤
          C * A * r ^ (-s - b) := by
  obtain ⟨C, hC, hbound⟩ := integral_far_power_envelope_le hs hb hb1 ι
  refine ⟨C, hC, fun L hL marks x r hr hrc q A hA hqm hq => ?_⟩
  have hd (y a : ℝ) : circDist L (y - a) =
      dist (y : AddCircle L) (a : AddCircle L) := by
    rw [← dist_coe_zero_eq_circDist, AddCircle.coe_sub]
    simp only [dist_eq_norm, sub_zero]
  apply hbound L hL.out marks x r hr
    (hrc.trans (cappedMarkDistance_le_one _ _))
    (fun j => by rw [hd]; exact hrc.trans (cappedMarkDistance_le_dist _ _ j)) q A hA hqm
  have hcount := CircleSingularity.countable_marked_lifts (T := L) marks
  filter_upwards [ae_restrict_of_ae (hcount.ae_notMem volume)] with y hy
  have hym : ∀ j, (y : AddCircle L) ≠ (marks j : AddCircle L) := by
    simpa only [mem_ofPred_eq, not_exists] using hy
  apply (hq y hym).trans
  apply mul_le_mul_of_nonneg_left _ hA
  simpa only [hd] using cappedMarkDistance_rpow_le_one_add_sum
    (fun j => (marks j : AddCircle L)) (y : AddCircle L) (-b)

/-- The scale comparison used after the error-kernel far estimate. It holds
already for `h ≤ r`, with no artificial restriction on the mark exponent. -/
theorem far_error_scale_le {s b h r : ℝ} (hs : 0 < s)
    (hh : 0 < h) (hhr : h ≤ r) :
    h * r ^ (-s - 1 - b) ≤ h ^ (1 - s) * r ^ (-1 - b) := by
  have hr : 0 < r := hh.trans_le hhr
  have hp : h ^ s ≤ r ^ s := Real.rpow_le_rpow hh.le hhr hs.le
  have heh : h = h ^ (1 - s) * h ^ s := by
    rw [← Real.rpow_add hh, sub_add_cancel, Real.rpow_one]
  have her : r ^ (-s - 1 - b) = r ^ (-s) * r ^ (-1 - b) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have hcancel : r ^ s * r ^ (-s) = 1 := by rw [← Real.rpow_add hr]; simp
  calc _ = h ^ (1 - s) * (h ^ s * r ^ (-s)) * r ^ (-1 - b) := by
        conv_lhs => lhs; rw [heh]
        rw [her]
        ring
    _ ≤ h ^ (1 - s) * (r ^ s * r ^ (-s)) * r ^ (-1 - b) := by
      gcongr
    _ = _ := by rw [hcancel, mul_one]

end Riesz1.CirclePowerConvolution
