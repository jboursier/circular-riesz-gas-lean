/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriUnanchoredScaling
public import Riesz1.Variance.APrioriTranslateRadius
public import Riesz1.Bridges.InputConsolidation

/-!
# Both a priori variances at the original centre

Lemma 5.2: both variances, all particle numbers, the
factor `M²`, and every positive fixed radius. The translated anchored
envelope is a separate assertion and is not claimed here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- Both original-radius bounds of Lemma 5.2, with
the paper's order and dependence of constants and the full factor `M²`. -/
theorem a_priori_original (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (lam ε : ℝ) (hlam : 0 ≤ lam) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      ∀ M : ℝ, 0 ≤ M → ∀ f : ℝ → ℝ,
      ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) →
      (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
        |deriv f u| ≤ M * cutoffMajorant P.val.2 lam ((N : ℝ) * ℓ) |u|) →
      (∃ hA : Integrable (fun X : Configuration N =>
          ∑ i, f ((X.val i - X.val ⟨0, N.pos⟩) / ℓ)) (gibbsMeasure P N),
        variance (gibbsMeasure P N) (fun X =>
          ∑ i, f ((X.val i - X.val ⟨0, N.pos⟩) / ℓ)) hA ≤
          ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ) ^ (ε + max (2 * lam) P.val.2))) ∧
      (∃ hB : Integrable (fun X : Configuration N => ∑ i, f (X.val i / ℓ)) (gibbsMeasure P N),
        variance (gibbsMeasure P N) (fun X => ∑ i, f (X.val i / ℓ)) hB ≤
          ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ) ^ (ε + max (2 * lam) P.val.2))) := by
  obtain ⟨Ca, hCa, ha⟩ := Internal.a_priori_anchored hBE hPL P lam ε hlam hε
  obtain ⟨Cb, hCb, hb⟩ := Internal.a_priori_unanchored hBE hPL P lam ε hlam hε
  refine ⟨Ca + Cb, add_pos hCa hCb, ?_⟩
  intro N ℓ hℓ hℓ1 hK M hM f hf hper hder
  have hm : 0 ≤ M ^ 2 * ((N : ℝ) * ℓ) ^ (ε + max (2 * lam) P.val.2) := by positivity
  constructor
  · obtain ⟨hA, hv⟩ := ha N ℓ hℓ hℓ1 hK M hM f hf hper hder
    refine ⟨hA, hv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have h := mul_le_mul_of_nonneg_right (show Ca ≤ Ca + Cb by linarith) hm
    simpa only [mul_assoc] using h
  · obtain ⟨hB, hv⟩ := hb N ℓ hℓ hℓ1 hK M hM f hf hper hder
    refine ⟨hB, hv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have h := mul_le_mul_of_nonneg_right (show Cb ≤ Ca + Cb by linarith) hm
    simpa only [mul_assoc] using h

/-- Both bounds of Lemma 5.2 for every positive fixed radius,
at centre zero. The constant is chosen before `N, ℓ, M, f`. -/
theorem a_priori_at_origin (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (lam ε R : ℝ) (hlam : 0 ≤ lam) (hε : 0 < ε) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      ∀ M : ℝ, 0 ≤ M → ∀ f : ℝ → ℝ,
      ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) →
      (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
        |deriv f u| ≤ M * Internal.aPrioriEnvelope P.val.2 lam ((N : ℝ) * ℓ) R |u|) →
      (∃ hA : Integrable (fun X : Configuration N =>
          ∑ i, f ((X.val i - X.val ⟨0, N.pos⟩) / ℓ)) (gibbsMeasure P N),
        variance (gibbsMeasure P N) (fun X =>
          ∑ i, f ((X.val i - X.val ⟨0, N.pos⟩) / ℓ)) hA ≤
          ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ) ^ (ε + max (2 * lam) P.val.2))) ∧
      (∃ hB : Integrable (fun X : Configuration N => ∑ i, f (X.val i / ℓ)) (gibbsMeasure P N),
        variance (gibbsMeasure P N) (fun X => ∑ i, f (X.val i / ℓ)) hB ≤
          ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ) ^ (ε + max (2 * lam) P.val.2))) := by
  obtain ⟨C, hC, hb⟩ := a_priori_original hBE hPL P lam ε hlam hε
  obtain ⟨B, hB, hrad⟩ := Internal.aPrioriEnvelope_radius_le
    (by linarith [P.2.2.2] : P.val.2 < 3) hlam hR
  refine ⟨C * B ^ 2, by positivity, ?_⟩
  intro N ℓ hℓ hℓ1 hK M hM f hf hper hder
  have hd : ∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
      |deriv f u| ≤ (M * B) * cutoffMajorant P.val.2 lam ((N : ℝ) * ℓ) |u| := by
    intro u hu
    apply (hder u hu).trans
    rw [Internal.cutoffMajorant_eq_aPrioriEnvelope, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hrad ((N : ℝ) * ℓ) hK |u| (abs_nonneg u)) hM
  obtain ⟨⟨hAi, hAv⟩, ⟨hBi, hBv⟩⟩ :=
    hb N ℓ hℓ hℓ1 hK (M * B) (by positivity) f hf hper hd
  have he : C * (M * B) ^ 2 = C * B ^ 2 * M ^ 2 := by ring
  exact ⟨⟨hAi, by simpa only [he] using hAv⟩, ⟨hBi, by simpa only [he] using hBv⟩⟩

end Riesz1

end
