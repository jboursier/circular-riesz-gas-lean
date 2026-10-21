/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopEstimatesInput
public import Riesz1.Auxiliary.LoopEstimatesPowers
public import Riesz1.Auxiliary.LoopLocalizationFinal
public import Riesz1.Auxiliary.LoopAnchoringVariance

/-!
# Localization of the microscopic loop variance

The estimates part of Lemma 5.8, conditional only on the first
anchoring bound and the Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler
inequality `External.PrekopaLeindler`. All constants precede
the particle number and scale. The small-parameter threshold and exponent
precede even the temperature and spatial cutoff.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz1.Internal

/-- The localization estimate on the microscopic loop. The return
values certify both finite second moments before stating the inequality. -/
theorem auxiliary_Loop_estimates_microscopic_of_anchoring
    (hanch : LoopAnchoringL2Input)
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (s α γ : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hα : s - 1 ≤ α) (hα2 : α < s / 2)
    (hγ : loopLocalizationExponent s ≤ γ) :
    ∃ ε₀ κ : ℝ, 0 < ε₀ ∧ 0 < κ ∧
      ∀ (β : ℝ) (hβ : 0 < β) (χ : ℝ → ℝ),
        ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4) →
        (∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
        ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ℓ C₀ : ℝ) (ψ : ℝ → ℝ),
          0 < ℓ → ℓ ≤ 1 → 1 ≤ ((n + 1).succPNat : ℝ) * ℓ → 0 ≤ C₀ →
          ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
          (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α)
            (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
          (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s (1 - s + α)
            (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
          let N := (n + 1).succPNat
          let K := (N : ℝ) * ℓ
          let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
          letI := (modelWellDefined P N).2.2
          letI := isProbabilityMeasure_anchoredLaw P (n + 1)
          let F := fun X : Configuration N => loopArcL s N (loopScaleField K ψ) X
          let H := fun y => loopCutoffF χ s γ ε N ℓ ψ (anchorVector y)
          ∃ hF : MemLp F 2 (gibbsMeasure P N),
          ∃ hH : MemLp H 2 (anchoredLaw P (n + 1)),
            variance (gibbsMeasure P N) F (hF.integrable one_le_two) ≤
              ENNReal.ofReal (C * K ^ (κ * ε)) *
                variance (anchoredLaw P (n + 1)) H (hH.integrable one_le_two) +
              ENNReal.ofReal (C * C₀ ^ 2 * K ^ (κ * ε) * (K + K ^ (2 * (1 - s + α)))) := by
  obtain ⟨εa, k, hεa, hk, ha⟩ := hanch s α γ hs hs1 hα hα2 hγ
  have hεs : 0 < min (1 / 8 : ℝ) ((1 - s / 2) / 8) := by
    apply lt_min <;> linarith
  refine ⟨min εa (min (1 / 8) ((1 - s / 2) / 8)), 2 * k + 1,
    lt_min hεa hεs, by positivity, ?_⟩
  intro β hβ χ hχ hχc hχs hχ1 hχ01 ε hε hε0
  have hεa' : ε < εa := hε0.trans_le (min_le_left _ _)
  have hεs' : ε < min (1 / 8) ((1 - s / 2) / 8) := hε0.trans_le (min_le_right _ _)
  have hγ1 : 1 < γ := by linarith [loopLocalizationExponent_ge_four s]
  obtain ⟨A, hA, hloc⟩ := auxiliary_Loop_localization hBE hPL β s hβ hs hs1 hα hα2
    hχ hχc hχs hχ1 hχ01 γ hγ
  obtain ⟨B, hB, hanc⟩ := ha β hβ hs hs1 χ hχ hχc hχs hχ1 hχ01 ε hε hεa'
  obtain ⟨D, hD, hsize⟩ := loopAnchoring_sizeWeighted_variance β s α γ ε hβ hs hs1
    hα hα2 hγ1 hε hεs' hBE hPL hχ hχc hχs hχ1 hχ01
  obtain ⟨L, _hL, hlocal⟩ := auxiliary_Loop_local_moments β s hβ hs hs1 hα hα2
    (p := 2) (by norm_num) hχ hχc hχs hχ1 hχ01
  obtain ⟨Cr, _hCr, hcrude⟩ := auxiliary_Loop_crude hBE hPL hβ hs hs1 (p := 2) (by norm_num)
  refine ⟨3 * (A ^ 2 + B ^ 2 + D + 1), by positivity, ?_⟩
  intro n ℓ C₀ ψ hℓ hℓ1 hK hC₀ hψ hper hd hdd
  let N := (n + 1).succPNat
  let K := (N : ℝ) * ℓ
  let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
  let μ := loopPrecedingMeasure P N
  let F := fun X : Configuration N => loopArcL s N (loopScaleField K ψ) X
  let G := loopLocalLoop s N ℓ γ (loopLocalTransport χ N ℓ γ ψ)
  let H := fun y => loopCutoffF χ s γ ε N ℓ ψ (anchorVector y)
  let c := loopLocalBackground s N ℓ γ (loopLocalTransport χ N ℓ γ ψ)
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have := isProbabilityMeasure_anchoredLaw P (n + 1)
  have hb : ContDiff ℝ 1 (loopScaleField K ψ) := (loopScaleField_contDiff hψ).of_le (by simp)
  have hbp : Function.Periodic (loopScaleField K ψ) (N : ℝ) :=
    loopLocalization_scaleField_periodic hper
  have hFnorm := hcrude N (loopScaleField K ψ) hb hbp
  norm_num only [ENNReal.ofReal_ofNat] at hFnorm
  have hF : MemLp F 2 (gibbsMeasure P N) := hFnorm.trans_lt ENNReal.ofReal_lt_top
  have hFmap : MemLp F 2 (μ.map Subtype.val) := by rw [map_loopPrecedingMeasure]; exact hF
  have hFm : MemLp (F ∘ Subtype.val) 2 μ := hFmap.comp_of_map measurable_subtype_coe.aemeasurable
  have hG : MemLp G 2 μ := by
    have hh := (hlocal hPL N ℓ γ ψ C₀ (by simp [N]) hℓ hK hγ1 hC₀ hψ hper hd hdd).1
    norm_num only [ENNReal.ofReal_ofNat] at hh
    exact hh
  obtain ⟨hH, hHw, hvar⟩ := hsize n ℓ C₀ ψ hℓ hℓ1 hK hC₀ hψ hper hd hdd
  have hmapOff : μ.map (fun X : LoopPrecedingConfiguration N => loopPrecedingOffsets X) =
      loopSizeBiasedLaw P n := map_loopPrecedingOffsets P n
  have hHmap : MemLp H 2 (μ.map loopPrecedingOffsets) := hmapOff.symm ▸ hHw
  have hHm : MemLp (H ∘ loopPrecedingOffsets) 2 μ :=
    hHmap.comp_of_map (measurable_loopPrecedingOffsets N).aemeasurable
  have hFvar := variance_eq_of_map μ (gibbsMeasure P N)
    measurable_subtype_coe.aemeasurable (map_loopPrecedingMeasure P N) hF hFm
  have hHvar := variance_eq_of_map μ (loopSizeBiasedLaw P n)
    (measurable_loopPrecedingOffsets N).aemeasurable hmapOff hHw hHm
  have hlocnorm := (hloc N ℓ ψ C₀ (by simp [N]) hℓ hℓ1 hK hC₀ hψ hper hd hdd).2.1
  have hancnorm := hanc C₀ hC₀ n ℓ ψ hℓ hℓ1 hK hψ hper hd hdd
  refine ⟨hF, hH, ?_⟩
  calc
    _ = variance μ (F ∘ Subtype.val) (hFm.integrable one_le_two) := hFvar
    _ ≤ 3 * (eLpNorm (fun X => F X.val - G X - c) 2 μ ^ 2 +
        eLpNorm (fun X => G X - H (loopPrecedingOffsets X)) 2 μ ^ 2 +
        variance μ (H ∘ loopPrecedingOffsets) (hHm.integrable one_le_two)) :=
      variance_le_two_errors μ hFm hG hHm c
    _ ≤ 3 * (ENNReal.ofReal (A * C₀ * K ^ (1 / 2 : ℝ)) ^ 2 +
        ENNReal.ofReal (B * C₀ * K ^ ((1 - s + α) + k * ε)) ^ 2 +
        (ENNReal.ofReal (K ^ ε) * variance (anchoredLaw P (n + 1)) H
          (hH.integrable one_le_two) + ENNReal.ofReal (D * C₀ ^ 2 * K ^ (-10 : ℝ)))) := by
      apply mul_le_mul' le_rfl
      apply add_le_add
      · exact add_le_add (pow_le_pow_left' hlocnorm 2) (pow_le_pow_left' hancnorm 2)
      · rw [← hHvar]
        exact hvar
    _ ≤ _ := loopEstimates_absorb hK (by linarith) hk hε hA.le hB.le hD.le hC₀ _

end Riesz1.Internal

end
