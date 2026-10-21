/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalizationCells
public import Riesz1.Auxiliary.LoopArcsUnconditional

/-!
# Polynomial moments of the global loop of the cutoff transport

The global-loop moment step of the localization part of Lemma 5.8.
The crude arc bound is combined with the support cell count. Both window
regimes, including every bounded scale `K ≥ 1`, are covered.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz1

/-- The global loop evaluated at the localized transport has moments bounded
by `C C₀ K^(a+γ)`. The constant is chosen before the window exponent. -/
theorem loopLocalization_global_moments
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    {β s : ℝ} (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    {α p : ℝ} (hα : s - 1 ≤ α) (hα2 : α < s / 2) (hp : 1 ≤ p)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ : ℝ) (ψ : ℝ → ℝ) (C0 : ℝ),
      0 < ℓ → 1 ≤ (N : ℝ) * ℓ → 1 < γ → 0 ≤ C0 → ContDiff ℝ ∞ ψ →
      Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤
        C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      let F := fun X : LoopPrecedingConfiguration N =>
        loopArcL s N (loopLocalTransport χ N ℓ γ ψ) X.val
      let μ := loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ N
      MemLp F (ENNReal.ofReal p) μ ∧
      eLpNorm F (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (C * C0 * ((N : ℝ) * ℓ) ^ ((1 - s + α) + γ)) := by
  obtain ⟨A, hA, hcells⟩ := loopLocalTransport_cell_sum hs hs1 hα hα2
    hχ hχc hχs hχ1 hχ01
  obtain ⟨B, hB, hcrude⟩ := auxiliary_Loop_crude hBE hPL hβ hs hs1 hp
  refine ⟨B * A, mul_pos hB hA, ?_⟩
  intro N ℓ γ ψ C0 hℓ hK hγ hC0 hψ hpψ hd hdd
  let b0 := loopLocalTransport χ N ℓ γ ψ
  let μ := loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ N
  have hb : ContDiff ℝ 1 b0 := (contDiff_loopLocalTransport hχ hψ hχs N hℓ γ).of_le
    (by simp)
  have hbp : Function.Periodic b0 (N : ℝ) := loopLocalTransport_periodic hℓ χ hpψ
  have hf := stronglyMeasurable_loopArcL hs hs1 N hb hbp
  have hmap := eLpNorm_map_measure (μ := μ) hf.aestronglyMeasurable
    measurable_subtype_coe.aemeasurable (p := ENNReal.ofReal p)
  rw [map_loopPrecedingMeasure] at hmap
  have hnorm : eLpNorm (fun X : LoopPrecedingConfiguration N => loopArcL s N b0 X.val)
      (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (B * A * C0 * ((N : ℝ) * ℓ) ^ ((1 - s + α) + γ)) := by
    calc
      _ = eLpNorm (fun X : Configuration N => loopArcL s N b0 X)
          (ENNReal.ofReal p) (gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N) := hmap.symm
      _ ≤ _ := hcrude N b0 hb hbp
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have h := mul_le_mul_of_nonneg_left
          (hcells N ℓ γ ψ C0 hℓ hK hγ hC0 hψ hpψ hd hdd) hB.le
        simpa only [cellSup, mul_assoc] using h
  exact ⟨hnorm.trans_lt ENNReal.ofReal_lt_top, hnorm⟩

end Riesz1

end
