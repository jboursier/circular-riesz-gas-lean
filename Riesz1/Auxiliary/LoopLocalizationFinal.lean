/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalizationGoodEvent
public import Riesz1.Auxiliary.LoopLocalizationErrorBadEvent
public import Riesz1.Auxiliary.LoopLocalizationExponent

/-!
# Spatial localization of the loop

The complete localization part of Lemma 5.8, including the
bounded scale range and the identically zero error in a full window.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz1

private theorem norm_partition {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) (hS : MeasurableSet S) (F : Ω → ℝ) :
    eLpNorm F 2 μ ≤ eLpNorm F 2 (μ.restrict S) + eLpNorm F 2 (μ.restrict Sᶜ) := by
  classical
  have he : F = S.indicator F + Sᶜ.indicator F := by
    funext X
    by_cases hX : X ∈ S <;> simp [hX]
  calc
    _ = eLpNorm (S.indicator F + Sᶜ.indicator F) 2 μ := congrArg (fun f => eLpNorm f 2 μ) he
    _ ≤ eLpNorm (S.indicator F) 2 μ + eLpNorm (Sᶜ.indicator F) 2 μ := eLpNorm_add_le (by norm_num)
    _ = _ := by rw [eLpNorm_indicator_eq_eLpNorm_restrict hS.nullMeasurableSet,
      eLpNorm_indicator_eq_eLpNorm_restrict hS.compl.nullMeasurableSet]

/-- Spatial localization of the loop. The positive constant is chosen before
the number of particles, scale, transport, and envelope constant. All scales
`K ≥ 1` are included, and the full-window error is identically zero. -/
theorem auxiliary_Loop_localization
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    {α : ℝ} (hα : s - 1 ≤ α) (hα2 : α < s / 2)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (γ : ℝ) (hγ : loopLocalizationExponent s ≤ γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ) (ψ : ℝ → ℝ) (C0 : ℝ),
      2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤
        C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      let μ := loopPrecedingMeasure (⟨(β, s), hβ, hs, hs1⟩ : Parameters) N
      let b0 := loopLocalTransport χ N ℓ γ ψ
      let F := fun X : LoopPrecedingConfiguration N =>
        loopArcL s N (loopScaleField ((N : ℝ) * ℓ) ψ) X.val -
          loopLocalLoop s N ℓ γ b0 X - loopLocalBackground s N ℓ γ b0
      MemLp F 2 μ ∧ eLpNorm F 2 μ ≤
        ENNReal.ofReal (C * C0 * ((N : ℝ) * ℓ) ^ (1 / 2 : ℝ)) ∧
      (¬GradPartial N ℓ γ → ∀ X, F X = 0) := by
  have hγ4 : 4 ≤ γ := (loopLocalizationExponent_ge_four s).trans hγ
  have hγ2 : 2 ≤ γ := by linarith
  obtain ⟨δ, Cg, K0, _hδ, hδs, hCg, hK0, hgood⟩ :=
    loopLocalization_good_eLpNorm hBE hPL β s hβ hs hs1 hα2 hχ hχs hχ01
  obtain ⟨Ct, hCt, htail⟩ := loopLocalization_tail_eLpNorm hBE hPL hβ hs hs1
    hα hα2 (p := 2) (by norm_num) hχ hχc hχs hχ1 hχ01
  obtain ⟨Cb, hCb, hbad⟩ := loopLocalization_bad_eLpNorm hBE hPL β s hβ hs hs1
    hα hα2 hγ2 hχ hχc hχs hχ1 hχ01
  obtain ⟨Ck, hCk, hbounded⟩ := loopLocalization_bounded_scale hBE hPL β s hβ hs hs1
    hα hα2 hγ2 hχ hχc hχs hχ1 hχ01 K0 hK0
  let C := Ck + Ct + Cg + Cb
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N ℓ ψ C0 hN hℓ hℓ1 hK hC0 hψ hpψ hd hdd
  let K := (N : ℝ) * ℓ
  let μ := loopPrecedingMeasure (⟨(β, s), hβ, hs, hs1⟩ : Parameters) N
  let G := loopExteriorGood N ℓ γ
  let b0 := loopLocalTransport χ N ℓ γ ψ
  let F := fun X : LoopPrecedingConfiguration N =>
    loopArcL s N (loopScaleField K ψ) X.val -
      loopLocalLoop s N ℓ γ b0 X - loopLocalBackground s N ℓ γ b0
  have hfull (hF : ¬GradPartial N ℓ γ) (X : LoopPrecedingConfiguration N) : F X = 0 :=
    loopLocalization_full_error_zero hF hℓ χ hpψ X
  have hnorm : eLpNorm F 2 μ ≤ ENNReal.ofReal (C * C0 * K ^ (1 / 2 : ℝ)) := by
    by_cases hP : GradPartial N ℓ γ
    · by_cases hlarge : K0 ≤ K
      · let T := fun X : LoopPrecedingConfiguration N =>
          loopArcL s N (loopScaleField K ψ) X.val - loopArcL s N b0 X.val
        let V := fun X : LoopPrecedingConfiguration N =>
          loopArcL s N b0 X.val - loopLocalLoop s N ℓ γ b0 X - loopLocalBackground s N ℓ γ b0
        have he : F = T + V := by
          funext X
          dsimp only [F, T, V, Pi.add_apply]
          ring
        have ht := (htail N ℓ γ ψ C0 hℓ hK hγ2 hP hC0 hψ hpψ hd hdd).2
        norm_num only [ENNReal.ofReal_ofNat] at ht
        have hg := (hgood N ℓ γ ψ C0 hN hℓ hℓ1 hlarge (by linarith) hP hC0 hψ hpψ hd).2
        have hb := (hbad N ℓ ψ C0 hN hℓ hℓ1 hK hP hC0 hψ hpψ hd hdd).2
        have htPow : K ^ (2 - s - γ * (1 - s)) ≤ K ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hK (loopLocalization_tail_exponent hs1 hγ)
        have hgPow : K ^ (1 - γ * (s / 2 - δ)) ≤ K ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hK (loopLocalization_force_exponent hs hγ hδs)
        have hbPow : K ^ (-10 : ℝ) ≤ K ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hK (by norm_num)
        have ht' : eLpNorm T 2 μ ≤ ENNReal.ofReal (Ct * C0 * K ^ (1 / 2 : ℝ)) :=
          ht.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left htPow (by positivity)))
        have hg' : eLpNorm V 2 (μ.restrict G) ≤ ENNReal.ofReal (Cg * C0 * K ^ (1 / 2 : ℝ)) :=
          hg.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hgPow (by positivity)))
        have hb' : eLpNorm F 2 (μ.restrict Gᶜ) ≤ ENNReal.ofReal (Cb * C0 * K ^ (1 / 2 : ℝ)) :=
          hb.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hbPow (by positivity)))
        calc
          _ ≤ eLpNorm F 2 (μ.restrict G) + eLpNorm F 2 (μ.restrict Gᶜ) :=
            norm_partition μ G (measurableSet_loopExteriorGood N ℓ γ) F
          _ ≤ (eLpNorm T 2 (μ.restrict G) + eLpNorm V 2 (μ.restrict G)) +
              eLpNorm F 2 (μ.restrict Gᶜ) := by
            apply add_le_add _ le_rfl
            rw [he]
            exact eLpNorm_add_le (by norm_num)
          _ ≤ (ENNReal.ofReal (Ct * C0 * K ^ (1 / 2 : ℝ)) +
              ENNReal.ofReal (Cg * C0 * K ^ (1 / 2 : ℝ))) +
              ENNReal.ofReal (Cb * C0 * K ^ (1 / 2 : ℝ)) :=
            add_le_add (add_le_add ((eLpNorm_restrict_le T 2 μ G).trans ht') hg') hb'
          _ ≤ _ := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            apply ENNReal.ofReal_le_ofReal
            calc
              _ = (Ct + Cg + Cb) * C0 * K ^ (1 / 2 : ℝ) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hC0)
                (Real.rpow_nonneg (by linarith : 0 ≤ K) (1 / 2 : ℝ))
      · have hb := (hbounded N ℓ ψ C0 hN hℓ hK (le_of_not_ge hlarge) hC0 hψ hpψ hd hdd).2
        apply hb.trans
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith : 0 ≤ K) _)
        apply mul_le_mul_of_nonneg_right _ hC0
        dsimp [C]
        linarith
    · have hz : F = 0 := funext (hfull hP)
      rw [hz, eLpNorm_zero]
      exact bot_le
  exact ⟨hnorm.trans_lt ENNReal.ofReal_lt_top, hnorm, hfull⟩

end Riesz1

end
