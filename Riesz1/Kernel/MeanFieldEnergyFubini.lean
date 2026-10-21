/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fubini for a periodic kernel against a periodic profile

For one-periodic functions `Ψ` and `G` on `ℝ`, with `Ψ` square integrable on `(0, 1]`, the
double integral `∬ G(x - y) (Ψ x - Ψ y)² dx dy` over `(0, 1]²` is absolutely convergent as soon
as `r ↦ |G r| ∫ (Ψ x - Ψ (x - r))² dx` is integrable on `(0, 1]`, and it equals
`∫ G(r) (∫ (Ψ x - Ψ (x - r))² dx) dr`. This is the Fubini step for the mean-field energy.
-/

public section

open MeasureTheory Set Filter Topology

open scoped ENNReal

namespace Riesz1

/-- Translation invariance of the lower integral of a one-periodic function over one period. -/
lemma lintegral_Ioc_sub_periodic {F : ℝ → ℝ≥0∞} (hF : Function.Periodic F 1) (x : ℝ) :
    ∫⁻ y in Ioc (0 : ℝ) 1, F (x - y) = ∫⁻ r in Ioc (0 : ℝ) 1, F r := by
  let Fc : UnitAddCircle → ℝ≥0∞ := hF.lift
  have hFc : ∀ y : ℝ, Fc (y : UnitAddCircle) = F y := fun y => hF.lift_coe y
  have h1 : ∀ y : ℝ, F (x - y) = Fc ((x : UnitAddCircle) - (y : UnitAddCircle)) := by
    intro y
    rw [← hFc (x - y)]
    congr 1
  calc ∫⁻ y in Ioc (0 : ℝ) 1, F (x - y)
      = ∫⁻ y in Ioc (0 : ℝ) 1, Fc ((x : UnitAddCircle) - (y : UnitAddCircle)) :=
        lintegral_congr fun y => h1 y
    _ = ∫⁻ z : UnitAddCircle, Fc ((x : UnitAddCircle) - z) := by
        have := AddCircle.lintegral_preimage 1 0 (fun z : UnitAddCircle => Fc ((x : UnitAddCircle) - z))
        simpa using this
    _ = ∫⁻ z : UnitAddCircle, Fc z := lintegral_sub_left_eq_self Fc (x : UnitAddCircle)
    _ = ∫⁻ r in Ioc (0 : ℝ) 1, F r := by
        have := AddCircle.lintegral_preimage 1 0 Fc
        simp only [zero_add] at this
        rw [← this]
        exact lintegral_congr fun r => hFc r

/-- Translation invariance of the Bochner integral of a one-periodic function over one period. -/
lemma integral_Ioc_sub_periodic {F : ℝ → ℝ} (hF : Function.Periodic F 1) (x : ℝ) :
    ∫ y in Ioc (0 : ℝ) 1, F (x - y) = ∫ r in Ioc (0 : ℝ) 1, F r := by
  rw [← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_left F x, sub_zero]
  have hper := hF.intervalIntegral_add_eq (x - 1) 0
  rwa [show x - 1 + 1 = x by ring, zero_add] at hper

/-- Translation of a one-periodic lower integral by a constant. -/
lemma lintegral_Ioc_add_periodic {F : ℝ → ℝ≥0∞} (hF : Function.Periodic F 1) (c : ℝ) :
    ∫⁻ y in Ioc (0 : ℝ) 1, F (y + c) = ∫⁻ r in Ioc (0 : ℝ) 1, F r := by
  let Fc : UnitAddCircle → ℝ≥0∞ := hF.lift
  have hFc : ∀ y : ℝ, Fc (y : UnitAddCircle) = F y := fun y => hF.lift_coe y
  calc ∫⁻ y in Ioc (0 : ℝ) 1, F (y + c)
      = ∫⁻ y in Ioc (0 : ℝ) 1, Fc ((y : UnitAddCircle) + (c : UnitAddCircle)) := by
        refine lintegral_congr fun y => ?_
        rw [← hFc (y + c)]
        congr 1
    _ = ∫⁻ z : UnitAddCircle, Fc (z + (c : UnitAddCircle)) := by
        have := AddCircle.lintegral_preimage 1 0 (fun z : UnitAddCircle => Fc (z + (c : UnitAddCircle)))
        simpa using this
    _ = ∫⁻ z : UnitAddCircle, Fc z := lintegral_add_right_eq_self Fc (c : UnitAddCircle)
    _ = ∫⁻ r in Ioc (0 : ℝ) 1, F r := by
        have := AddCircle.lintegral_preimage 1 0 Fc
        simp only [zero_add] at this
        rw [← this]
        exact lintegral_congr fun r => hFc r

/-- The square of a difference of a periodic `L²` profile is integrable on `(0, 1]`. -/
lemma integrable_sq_sub_translate {Ψ : ℝ → ℝ} (hΨm : Measurable Ψ) (hΨp : Function.Periodic Ψ 1)
    (hΨ2 : ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (Ψ x ^ 2) ≠ ⊤) (r : ℝ) :
    Integrable (fun x => (Ψ x - Ψ (x - r)) ^ 2) (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hFp : Function.Periodic (fun z => ENNReal.ofReal (Ψ z ^ 2)) 1 :=
    fun z => by simp [hΨp z]
  have hbd : ∀ x : ℝ, ENNReal.ofReal ((Ψ x - Ψ (x - r)) ^ 2) ≤
      ENNReal.ofReal 2 * ENNReal.ofReal (Ψ x ^ 2) +
        ENNReal.ofReal 2 * ENNReal.ofReal (Ψ (x - r) ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg (Ψ x + Ψ (x - r))]
  have hmeasK : Measurable (fun x => ENNReal.ofReal 2 * ENNReal.ofReal (Ψ x ^ 2)) :=
    measurable_const.mul ((hΨm.pow_const 2).ennreal_ofReal)
  have hshift : ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (Ψ (x - r) ^ 2) =
      ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (Ψ x ^ 2) := by
    have h := lintegral_Ioc_add_periodic hFp (-r)
    simp only [← sub_eq_add_neg] at h
    exact h
  have hsplit : ∫⁻ x in Ioc (0 : ℝ) 1,
      (ENNReal.ofReal 2 * ENNReal.ofReal (Ψ x ^ 2) +
        ENNReal.ofReal 2 * ENNReal.ofReal (Ψ (x - r) ^ 2)) =
      ENNReal.ofReal 2 * (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (Ψ x ^ 2)) +
        ENNReal.ofReal 2 * (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (Ψ (x - r) ^ 2)) := by
    rw [lintegral_add_left hmeasK, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hfin : ∫⁻ x in Ioc (0 : ℝ) 1,
      (ENNReal.ofReal 2 * ENNReal.ofReal (Ψ x ^ 2) +
        ENNReal.ofReal 2 * ENNReal.ofReal (Ψ (x - r) ^ 2)) ≠ ⊤ := by
    rw [hsplit, hshift]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΨ2,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΨ2⟩
  have hlt : ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal ((Ψ x - Ψ (x - r)) ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (lintegral_mono hbd)
  have hmeas : Measurable (fun x => (Ψ x - Ψ (x - r)) ^ 2) :=
    (hΨm.sub (hΨm.comp (measurable_id.sub_const r))).pow_const 2
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg _)]
  exact lt_top_iff_ne_top.mpr hlt

/-- The absolute kernel integral over the product, in the variables `(x, r)`, is finite. -/
lemma lintegral_kernel_ne_top {Ψ G : ℝ → ℝ} (hΨm : Measurable Ψ) (hΨp : Function.Periodic Ψ 1)
    (hΨ2 : ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (Ψ x ^ 2) ≠ ⊤)
    (hGm : Measurable G)
    (hint : IntegrableOn (fun r => |G r| * ∫ x in Ioc (0 : ℝ) 1, (Ψ x - Ψ (x - r)) ^ 2)
      (Ioc (0 : ℝ) 1)) :
    ∫⁻ p : ℝ × ℝ, ‖G p.2 * (Ψ p.1 - Ψ (p.1 - p.2)) ^ 2‖ₑ
      ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) ≠ ⊤ := by
  have hKm : Measurable (fun p : ℝ × ℝ => G p.2 * (Ψ p.1 - Ψ (p.1 - p.2)) ^ 2) :=
    (hGm.comp measurable_snd).mul
      (((hΨm.comp measurable_fst).sub (hΨm.comp (measurable_fst.sub measurable_snd))).pow_const 2)
  have hnn : ∀ r : ℝ, 0 ≤ ∫ x in Ioc (0 : ℝ) 1, (Ψ x - Ψ (x - r)) ^ 2 := fun r =>
    setIntegral_nonneg measurableSet_Ioc fun x _ => sq_nonneg _
  have hinner : ∀ r : ℝ, ∫⁻ x in Ioc (0 : ℝ) 1, ‖G r * (Ψ x - Ψ (x - r)) ^ 2‖ₑ =
      ‖G r‖ₑ * ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal ((Ψ x - Ψ (x - r)) ^ 2) := by
    intro r
    rw [← lintegral_const_mul]
    · refine lintegral_congr fun x => ?_
      rw [enorm_mul, Real.enorm_eq_ofReal (sq_nonneg _)]
    · exact ((hΨm.sub (hΨm.comp (measurable_id.sub_const r))).pow_const 2).ennreal_ofReal
  have hfinite : ∀ r : ℝ, ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal ((Ψ x - Ψ (x - r)) ^ 2) =
      ENNReal.ofReal (∫ x in Ioc (0 : ℝ) 1, (Ψ x - Ψ (x - r)) ^ 2) := by
    intro r
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_sq_sub_translate hΨm hΨp hΨ2 r)
      (Eventually.of_forall fun x => sq_nonneg _)).symm
  rw [lintegral_prod _ hKm.enorm.aemeasurable, lintegral_lintegral_swap hKm.enorm.aemeasurable]
  have key : ∫⁻ r in Ioc (0 : ℝ) 1, ∫⁻ x in Ioc (0 : ℝ) 1, ‖G r * (Ψ x - Ψ (x - r)) ^ 2‖ₑ =
      ∫⁻ r in Ioc (0 : ℝ) 1, ‖|G r| * ∫ x in Ioc (0 : ℝ) 1, (Ψ x - Ψ (x - r)) ^ 2‖ₑ := by
    refine lintegral_congr fun r => ?_
    rw [hinner r, hfinite r, Real.enorm_eq_ofReal (mul_nonneg (abs_nonneg _) (hnn r)),
      Real.enorm_eq_ofReal_abs, ENNReal.ofReal_mul (abs_nonneg _)]
  rw [key]
  exact hint.2.ne

/-- Fubini for the periodic kernel against a periodic profile: the double integral over `(0, 1]²`
is absolutely convergent, and it equals `∫ G(r) (∫ (Ψ x - Ψ (x - r))² dx) dr`. -/
theorem integrable_and_integral_translate {Ψ G : ℝ → ℝ}
    (hΨm : Measurable Ψ) (hΨp : Function.Periodic Ψ 1)
    (hΨ2 : ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (Ψ x ^ 2) ≠ ⊤)
    (hGm : Measurable G) (hGp : Function.Periodic G 1)
    (hint : IntegrableOn (fun r => |G r| * ∫ x in Ioc (0 : ℝ) 1, (Ψ x - Ψ (x - r)) ^ 2)
      (Ioc (0 : ℝ) 1)) :
    Integrable (fun p : ℝ × ℝ => G (p.1 - p.2) * (Ψ p.1 - Ψ p.2) ^ 2)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) ∧
    ∫ p : ℝ × ℝ, G (p.1 - p.2) * (Ψ p.1 - Ψ p.2) ^ 2
      ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) =
      ∫ r in Ioc (0 : ℝ) 1, G r * ∫ x in Ioc (0 : ℝ) 1, (Ψ x - Ψ (x - r)) ^ 2 := by
  have hKm : Measurable (fun p : ℝ × ℝ => G p.2 * (Ψ p.1 - Ψ (p.1 - p.2)) ^ 2) :=
    (hGm.comp measurable_snd).mul
      (((hΨm.comp measurable_fst).sub (hΨm.comp (measurable_fst.sub measurable_snd))).pow_const 2)
  have hΦm : Measurable (fun p : ℝ × ℝ => G (p.1 - p.2) * (Ψ p.1 - Ψ p.2) ^ 2) :=
    (hGm.comp (measurable_fst.sub measurable_snd)).mul
      (((hΨm.comp measurable_fst).sub (hΨm.comp measurable_snd)).pow_const 2)
  have hKint : Integrable (fun p : ℝ × ℝ => G p.2 * (Ψ p.1 - Ψ (p.1 - p.2)) ^ 2)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
    ⟨hKm.aestronglyMeasurable,
      lt_top_iff_ne_top.mpr (lintegral_kernel_ne_top hΨm hΨp hΨ2 hGm hint)⟩
  have hshift : ∀ x : ℝ, Function.Periodic (fun z => G z * (Ψ x - Ψ (x - z)) ^ 2) 1 := by
    intro x z
    simp only
    rw [hGp z, show x - (z + 1) = x - z - 1 by ring, hΨp.sub_eq]
  have hΦfin : ∫⁻ p : ℝ × ℝ, ‖G (p.1 - p.2) * (Ψ p.1 - Ψ p.2) ^ 2‖ₑ
      ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) ≠ ⊤ := by
    rw [lintegral_prod _ hΦm.enorm.aemeasurable]
    have h : ∀ x : ℝ, ∫⁻ y in Ioc (0 : ℝ) 1, ‖G (x - y) * (Ψ x - Ψ y) ^ 2‖ₑ =
        ∫⁻ r in Ioc (0 : ℝ) 1, ‖G r * (Ψ x - Ψ (x - r)) ^ 2‖ₑ := by
      intro x
      have hF : Function.Periodic (fun z => ‖G z * (Ψ x - Ψ (x - z)) ^ 2‖ₑ) 1 :=
        fun z => by simp only [hshift x z]
      have := lintegral_Ioc_sub_periodic hF x
      simpa only [sub_sub_cancel] using this
    rw [lintegral_congr h]
    have hK := lintegral_kernel_ne_top hΨm hΨp hΨ2 hGm hint
    rwa [lintegral_prod _ hKm.enorm.aemeasurable] at hK
  have hΦint : Integrable (fun p : ℝ × ℝ => G (p.1 - p.2) * (Ψ p.1 - Ψ p.2) ^ 2)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
    ⟨hΦm.aestronglyMeasurable, lt_top_iff_ne_top.mpr hΦfin⟩
  refine ⟨hΦint, ?_⟩
  rw [integral_prod _ hΦint]
  have h2 : ∀ x : ℝ, ∫ y in Ioc (0 : ℝ) 1, G (x - y) * (Ψ x - Ψ y) ^ 2 =
      ∫ r in Ioc (0 : ℝ) 1, G r * (Ψ x - Ψ (x - r)) ^ 2 := by
    intro x
    have := integral_Ioc_sub_periodic (hshift x) x
    simpa only [sub_sub_cancel] using this
  simp only [h2]
  rw [integral_integral_swap (f := fun x r => G r * (Ψ x - Ψ (x - r)) ^ 2) hKint]
  refine setIntegral_congr_fun measurableSet_Ioc fun r _ => ?_
  rw [integral_const_mul]

end Riesz1
