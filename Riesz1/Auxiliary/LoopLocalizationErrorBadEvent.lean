/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalizationBoundedScale
public import Riesz1.Auxiliary.LoopLocalizationBadEvent

/-!
# The complete localization error on the bad event

The localization part of Lemma 5.8. The global uncut loop, the
local loop and the deterministic background are all included, for every `K ≥ 1`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz1

/-- The entire localization error has restricted second moment of order
`K⁻¹⁰` on the exterior bad event, with no asymptotic scale restriction. -/
theorem loopLocalization_bad_eLpNorm
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    {α γ : ℝ} (hα : s - 1 ≤ α) (hα2 : α < s / 2) (hγ : 2 ≤ γ)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ) (ψ : ℝ → ℝ) (C0 : ℝ),
      2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → GradPartial N ℓ γ →
      0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤
        C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      let μ := loopPrecedingMeasure (⟨(β, s), hβ, hs, hs1⟩ : Parameters) N
      let b0 := loopLocalTransport χ N ℓ γ ψ
      let F := fun X : LoopPrecedingConfiguration N =>
        loopArcL s N (loopScaleField ((N : ℝ) * ℓ) ψ) X.val -
          loopLocalLoop s N ℓ γ b0 X - loopLocalBackground s N ℓ γ b0
      MemLp F 2 (μ.restrict (loopExteriorGood N ℓ γ)ᶜ) ∧
      eLpNorm F 2 (μ.restrict (loopExteriorGood N ℓ γ)ᶜ) ≤
        ENNReal.ofReal (C * C0 * ((N : ℝ) * ℓ) ^ (-10 : ℝ)) := by
  let d := (1 - s + α) + 2 * γ
  have hd : 0 < d := by dsimp [d]; linarith
  let B := 4 * (d + 10)
  have hB : 0 < B := by dsimp [B]; linarith
  obtain ⟨Q, hQ, hprob⟩ := loopLocalization_bad_probability hBE hPL β s hβ hs hs1 γ B (by linarith) hB
  obtain ⟨A, hA, hmom⟩ := loopLocalization_polynomial_error hBE hPL β s hβ hs hs1
    hα hα2 hγ (p := 4) (by norm_num) hχ hχc hχs hχ1 hχ01
  refine ⟨A * Q ^ (1 / 4 : ℝ), by positivity, ?_⟩
  intro N ℓ ψ C0 hN hℓ hℓ1 hK hP hC0 hψ hpψ hdψ hddψ
  let μ := loopPrecedingMeasure (⟨(β, s), hβ, hs, hs1⟩ : Parameters) N
  let b0 := loopLocalTransport χ N ℓ γ ψ
  let F := fun X : LoopPrecedingConfiguration N =>
        loopArcL s N (loopScaleField ((N : ℝ) * ℓ) ψ) X.val -
          loopLocalLoop s N ℓ γ b0 X - loopLocalBackground s N ℓ γ b0
  let S := (loopExteriorGood N ℓ γ)ᶜ
  let K := (N : ℝ) * ℓ
  have hKpos : 0 < K := by dsimp [K]; linarith
  have hb : ContDiff ℝ 1 (loopScaleField K ψ) := (loopScaleField_contDiff hψ).of_le (by simp)
  have hbp := loopLocalization_scaleField_periodic (N := N) hpψ
  have hbl := (contDiff_loopLocalTransport hχ hψ hχs N hℓ γ).continuous
  have hF : Measurable F :=
    (((stronglyMeasurable_loopArcL hs hs1 N hb hbp).measurable.comp measurable_subtype_coe).sub
      (measurable_loopLocalLoop hbl s N hℓ.le γ)).sub_const _
  have hnorm4 : eLpNorm F 4 μ ≤ ENNReal.ofReal (A * C0 * K ^ d) := by
    have hm := (hmom N ℓ ψ C0 hN hℓ hK hC0 hψ hpψ hdψ hddψ).2
    norm_num only [ENNReal.ofReal_ofNat] at hm
    exact hm
  have hnorm : eLpNorm F 2 (μ.restrict S) ≤
      ENNReal.ofReal (A * Q ^ (1 / 4 : ℝ) * C0 * K ^ (-10 : ℝ)) := by
    calc
      _ ≤ eLpNorm F 4 μ * μ S ^ (1 / 4 : ℝ) :=
        eLpNorm_two_restrict_le_four hF.aestronglyMeasurable S
      _ ≤ ENNReal.ofReal (A * C0 * K ^ d) *
          ENNReal.ofReal (Q * K ^ (-B)) ^ (1 / 4 : ℝ) := by
        apply mul_le_mul' hnorm4
        exact ENNReal.rpow_le_rpow (hprob N ℓ hN hℓ hℓ1 hK hP) (by norm_num)
      _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ← ENNReal.ofReal_mul (by positivity),
          Real.mul_rpow hQ.le (Real.rpow_nonneg hKpos.le _),
          ← Real.rpow_mul hKpos.le]
        have he : d + -B * (1 / 4) = (-10 : ℝ) := by dsimp [B]; ring
        have hp : K ^ d * K ^ (-B * (1 / 4)) = K ^ (-10 : ℝ) := by
          rw [← Real.rpow_add hKpos, he]
        congr 1
        calc
          _ = A * Q ^ (1 / 4 : ℝ) * C0 * (K ^ d * K ^ (-B * (1 / 4))) := by ring
          _ = _ := by rw [hp]
  exact ⟨hnorm.trans_lt ENNReal.ofReal_lt_top, hnorm⟩


end Riesz1

end
