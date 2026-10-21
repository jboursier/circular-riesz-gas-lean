/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelErrorEnvelope

/-!
# Quantitative cutoffs of the regularization-error kernel

The near mass retains `h^(1-s)`, and the far derivative is bounded by
`C h^(1-s) 1_{d≥a/2} d^(-2)`. Both estimates hold even when the cutoff
transition intersects the smoothing window. This is the quantitative kernel
split needed for equation (5.8) in Lemma 5.3.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The actual error kernel is C¹ off the singular lattice. -/
theorem inverseKernel_regularization_contDiffAt (P : Parameters) {ρ : ℝ → ℝ}
    (hρ : IsMollifier ρ) {L h t : ℝ} (hL : 0 < L) (hh : 0 < h)
    (ht : t ≠ 0) (htL : |t| < L) :
    ContDiffAt ℝ 1 (fun u => inverseKernel P L u - mollifyLine ρ h (inverseKernel P L) u) t :=
  ((inverseKernel_contDiffAt_of_abs_lt P hL ht htL).of_le (by simp)).sub
    ((contDiff_mollifyLine_of_locallyIntegrable hρ hh
      (inverseKernel_locallyIntegrable P hL)).of_le (by simp)).contDiffAt

/-- One cutoff for every circle and smoothing radius, with quantitative mass
and derivative bounds uniform over the whole smoothing/cutoff transition. -/
theorem inverseKernel_regularization_quantitative_cutoff (P : Parameters)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → ∃ χ : ℝ → ℝ,
      ContDiff ℝ ∞ χ ∧ (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) ∧
      (∀ t, |t| ≤ a / 2 → χ t = 0) ∧
      ∀ L h : ℝ, 0 < L → 0 < h → h ≤ L / 4 → a < L / 2 →
        let E := fun t => inverseKernel P L t - mollifyLine ρ h (inverseKernel P L) t
        Function.support (fun t => E t * (1 - χ t)) ⊆ Ioc (-a) a ∧
        IntegrableOn (fun t => E t * (1 - χ t)) (Icc (-a) a) ∧
        (∫ t in Icc (-a) a, |E t * (1 - χ t)|) ≤ C * h ^ (1 - P.val.2) ∧
        ContDiffOn ℝ 1 (fun t => E t * χ t) (Ioo (-L) L) ∧
        ∀ t : ℝ, |t| < L / 2 →
          |deriv (fun u => E u * χ u) t| ≤
            C * h ^ (1 - P.val.2) *
              (Ici (a / 2)).indicator (fun d : ℝ => d ^ (-2 : ℝ)) |t| := by
  obtain ⟨D, hD, henv⟩ := inverseKernel_regularization_power_envelopes P ρ hρ
  obtain ⟨K, hK, hmass⟩ := inverseKernel_regularization_L1 P ρ hρ
  obtain ⟨B, hB, hcut⟩ := exists_even_scaled_cutoff
  let C := K + D * (1 + B) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hKC : K ≤ C := by
    have hn : 0 ≤ D * (1 + B) := by positivity
    dsimp [C]
    linarith
  have hDC : D * (1 + B) ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, fun a ha => ?_⟩
  obtain ⟨χ, hχ, hχb, _heven, hzero, hone, hdχ, hout⟩ := hcut a ha
  refine ⟨χ, hχ, hχb, hzero, fun L h hL hh hhL haL => ?_⟩
  let E := fun t => inverseKernel P L t - mollifyLine ρ h (inverseKernel P L) t
  obtain ⟨hEi, hEmass⟩ := hmass L h hL hh hhL
  have hsmall : Icc (-a) a ⊆ Icc (-(L / 2)) (L / 2) :=
    Icc_subset_Icc (by linarith) haL.le
  have hNi : IntegrableOn (fun t => E t * (1 - χ t)) (Icc (-a) a) :=
    (hEi.mono_set hsmall).mul_continuousOn
      ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).sub hχ.continuous).continuousOn
      isCompact_Icc
  have hKs (t : ℝ) (ht : t ≠ 0) (htL : |t| < L) : ContDiffAt ℝ 1 E t :=
    inverseKernel_regularization_contDiffAt P hρ hL hh ht htL
  refine ⟨?_, hNi, ?_, ?_, fun t ht => ?_⟩
  · intro t ht
    have ht' : |t| < a := by
      by_contra hn
      exact ht (by dsimp only; rw [hone t (le_of_not_gt hn), sub_self, mul_zero])
    exact ⟨(abs_lt.mp ht').1, (abs_lt.mp ht').2.le⟩
  · calc (∫ t in Icc (-a) a, |E t * (1 - χ t)|) ≤ ∫ t in Icc (-a) a, |E t| := by
          apply integral_mono_ae hNi.abs (hEi.mono_set hsmall).abs
          exact ae_of_all _ fun t => by
            dsimp only
            rw [abs_mul, abs_of_nonneg (by linarith [(hχb t).2] : 0 ≤ 1 - χ t)]
            exact mul_le_of_le_one_right (abs_nonneg _) (by linarith [(hχb t).1])
        _ ≤ ∫ t in Icc (-(L / 2)) (L / 2), |E t| :=
          setIntegral_mono_set hEi.abs (ae_of_all _ fun t => abs_nonneg _) (Eventually.of_forall hsmall)
        _ ≤ K * h ^ (1 - P.val.2) := hEmass
        _ ≤ C * h ^ (1 - P.val.2) := mul_le_mul_of_nonneg_right hKC (by positivity)
  · intro t ht
    exact (PowerKernelCutoff.contDiffAt_far ha hχ hzero hKs
      (abs_lt.mpr ht)).contDiffWithinAt
  · have hb := PowerKernelCutoff.abs_deriv_far_le (e := -1) ha
      (show 0 ≤ D * h ^ (1 - P.val.2) by positivity) hB.le hχ hχb hzero hdχ
      (fun u hu => hout u (Or.inr hu))
      (fun u hu huL => hKs u hu (huL.trans (by linarith)))
      (fun u hu huL => (henv L h u hL hh hhL huL hu).1)
      (fun u hu huL => by simpa only [show (-1 : ℝ) - 1 = -2 by norm_num] using
        (henv L h u hL hh hhL huL hu).2) ht
    have hn : 0 ≤ (Ici (a / 2)).indicator (fun d : ℝ => d ^ (-2 : ℝ)) |t| :=
      indicator_nonneg (fun d _ => Real.rpow_nonneg (abs_nonneg t) _) _
    apply hb.trans
    calc D * h ^ (1 - P.val.2) * (1 + B) *
          (Ici (a / 2)).indicator (fun d : ℝ => d ^ ((-1 : ℝ) - 1)) |t| =
          (D * (1 + B)) * h ^ (1 - P.val.2) *
          (Ici (a / 2)).indicator (fun d : ℝ => d ^ (-2 : ℝ)) |t| := by
            rw [show (-1 : ℝ) - 1 = -2 by norm_num]
            ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hDC (by positivity)) hn

end Riesz1
