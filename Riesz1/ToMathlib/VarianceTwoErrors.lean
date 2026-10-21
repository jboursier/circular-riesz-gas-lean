/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.SizeBiasedVariance

/-!
# Variance controlled by two uncentered errors

A comparison variable and a deterministic background reduce a variance
estimate to two uncentered second moments. This avoids charging the
deterministic background in the localization of the loop.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Riesz1

/-- A real second moment is the square of the extended `L²` norm. -/
theorem lintegral_sq_eq_eLpNorm_two_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F : Ω → ℝ} (hF : AEStronglyMeasurable F μ) :
    (∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂μ) = eLpNorm F 2 μ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hF
  norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] at h
  rw [h]
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- Variance is preserved by a measurable change of probability space. -/
theorem variance_map_eq {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → Ξ} (hf : AEMeasurable f μ)
    {F : Ξ → ℝ} (hF : MemLp F 2 (μ.map f)) :
    variance (μ.map f) F (hF.integrable one_le_two) =
      variance μ (F ∘ f) ((hF.comp_of_map hf).integrable one_le_two) := by
  unfold variance
  rw [integral_map hf hF.aestronglyMeasurable]
  exact lintegral_map' ((hF.aemeasurable.sub_const _).pow_const 2).ennreal_ofReal hf

/-- Variance under a specified push-forward law. Integrability certificates
are supplied on the original measures, so the statement avoids transporting
dependent proof arguments through an equality of measures. -/
theorem variance_eq_of_map {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : Ω → Ξ} (hf : AEMeasurable f μ) (he : μ.map f = ν)
    {F : Ξ → ℝ} (hF : MemLp F 2 ν) (hFm : MemLp (F ∘ f) 2 μ) :
    variance ν F (hF.integrable one_le_two) =
      variance μ (F ∘ f) (hFm.integrable one_le_two) := by
  have hm : AEStronglyMeasurable F (μ.map f) := he.symm ▸ hF.aestronglyMeasurable
  have hmean : (∫ x, F x ∂ν) = ∫ x, F (f x) ∂μ := by
    calc
      _ = ∫ x, F x ∂μ.map f := congrArg (fun ρ => ∫ x, F x ∂ρ) he.symm
      _ = _ := integral_map hf hm
  unfold variance
  rw [hmean]
  calc
    _ = ∫⁻ x, ENNReal.ofReal ((F x - ∫ y, F (f y) ∂μ) ^ 2) ∂μ.map f :=
      congrArg (fun ρ => ∫⁻ x, ENNReal.ofReal ((F x - ∫ y, F (f y) ∂μ) ^ 2) ∂ρ) he.symm
    _ = _ := lintegral_map' ((hm.aemeasurable.sub_const _).pow_const 2).ennreal_ofReal hf

/-- Two uncentered errors suffice to compare variances. An arbitrary
deterministic background is free. -/
theorem variance_le_two_errors {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F G H : Ω → ℝ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) (hH : MemLp H 2 μ) (c : ℝ) :
    variance μ F (hF.integrable one_le_two) ≤
      3 * (eLpNorm (fun x => F x - G x - c) 2 μ ^ 2 +
        eLpNorm (fun x => G x - H x) 2 μ ^ 2 +
        variance μ H (hH.integrable one_le_two)) := by
  let m := ∫ x, H x ∂μ
  have hU := (hF.sub hG).sub (memLp_const c)
  have hV := hG.sub hH
  apply (variance_le_lintegral_sq_sub μ hF (c + m)).trans
  calc
    _ ≤ ∫⁻ x, 3 * (ENNReal.ofReal ((F x - G x - c) ^ 2) +
        ENNReal.ofReal ((G x - H x) ^ 2) + ENNReal.ofReal ((H x - m) ^ 2)) ∂μ := by
      apply lintegral_mono
      intro x
      have he : (F x - (c + m)) ^ 2 ≤
          3 * ((F x - G x - c) ^ 2 + (G x - H x) ^ 2 + (H x - m) ^ 2) := by
        nlinarith [sq_nonneg ((F x - G x - c) - (G x - H x)),
          sq_nonneg ((F x - G x - c) - (H x - m)),
          sq_nonneg ((G x - H x) - (H x - m))]
      have hadd : ENNReal.ofReal ((F x - G x - c) ^ 2 + (G x - H x) ^ 2 +
          (H x - m) ^ 2) = ENNReal.ofReal ((F x - G x - c) ^ 2) +
            ENNReal.ofReal ((G x - H x) ^ 2) + ENNReal.ofReal ((H x - m) ^ 2) := by
        rw [ENNReal.ofReal_add (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _),
          ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        ENNReal.ofReal_ofNat, hadd] using ENNReal.ofReal_le_ofReal he
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by norm_num),
        lintegral_add_left' (show AEMeasurable (fun x =>
          ENNReal.ofReal ((F x - G x - c) ^ 2) + ENNReal.ofReal ((G x - H x) ^ 2)) μ from
            (hU.aemeasurable.pow_const 2).ennreal_ofReal.add
              (hV.aemeasurable.pow_const 2).ennreal_ofReal),
        lintegral_add_left' (show AEMeasurable (fun x =>
          ENNReal.ofReal ((F x - G x - c) ^ 2)) μ from
            (hU.aemeasurable.pow_const 2).ennreal_ofReal),
        lintegral_sq_eq_eLpNorm_two_sq (F := fun x => F x - G x - c) hU.aestronglyMeasurable,
        lintegral_sq_eq_eLpNorm_two_sq (F := fun x => G x - H x) hV.aestronglyMeasurable]
      rfl

end Riesz1

end
