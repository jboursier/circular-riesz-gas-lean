/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalizationExpansion
public import Riesz1.Auxiliary.LoopExteriorFinal
public import Riesz1.Auxiliary.LoopCrude

/-!
# Localization on the exterior good event

The remaining probabilistic estimate of the localization part of
Lemma 5.8, with only the Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler
inequality `External.PrekopaLeindler` as external hypotheses.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz1

/-- The good-event error of the cutoff loop, with constants and threshold
chosen before all scales and window exponents. -/
theorem loopLocalization_good_eLpNorm
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    {α : ℝ} (hα2 : α < s / 2) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4)) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ δ C K0 : ℝ, 0 < δ ∧ δ ≤ s / 4 ∧ 0 < C ∧ 1 ≤ K0 ∧
      ∀ (N : ℕ+) (ℓ γ : ℝ) (ψ : ℝ → ℝ) (C0 : ℝ),
        2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → K0 ≤ (N : ℝ) * ℓ → 1 < γ →
        GradPartial N ℓ γ → 0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
        (∀ t, |deriv ψ t| ≤
          C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
        let μ := loopPrecedingMeasure (⟨(β, s), hβ, hs, hs1⟩ : Parameters) N
        let b0 := loopLocalTransport χ N ℓ γ ψ
        let F := fun X : LoopPrecedingConfiguration N =>
          loopArcL s N b0 X.val - loopLocalLoop s N ℓ γ b0 X -
            loopLocalBackground s N ℓ γ b0
        MemLp F 2 (μ.restrict (loopExteriorGood N ℓ γ)) ∧
        eLpNorm F 2 (μ.restrict (loopExteriorGood N ℓ γ)) ≤
          ENNReal.ofReal (C * C0 * ((N : ℝ) * ℓ) ^ (1 - γ * (s / 2 - δ))) := by
  obtain ⟨eps0, heps, hext⟩ := auxiliary_Loop_exterior hBE hPL β s hβ hs hs1
  let δ := min (s / 4) eps0 / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδs : δ ≤ s / 4 := by
    have := min_le_left (s / 4) eps0
    dsimp [δ]
    linarith
  have hδ0 : δ < min (s / 2) eps0 := by
    have hm := min_le_right (s / 4) eps0
    apply lt_min
    · linarith
    · dsimp [δ]
      linarith
  obtain ⟨Cf, c, lam, K0, hCf, _hc, _hlam, hK0, _heq, hforce⟩ :=
    hext 2 δ (by norm_num) hδ hδ0
  let A := 20 * ((1 + 1 / (1 - (1 - s + α))) + 1 / (1 - s))
  have hA : 0 < A := by
    have ha : 0 < 1 - (1 - s + α) := by linarith
    have ht : 0 < 1 - s := by linarith
    dsimp [A]
    positivity
  refine ⟨δ, A * Cf, K0, hδ, hδs, mul_pos hA hCf, hK0, ?_⟩
  intro N ℓ γ ψ C0 hN hℓ hℓ1 hK hγ hP hC0 hψ hpψ hd
  let K := (N : ℝ) * ℓ
  let M := gradM N ℓ γ
  let μ := loopPrecedingMeasure (⟨(β, s), hβ, hs, hs1⟩ : Parameters) N
  let G := loopExteriorGood N ℓ γ
  let ν := μ.comap (Subtype.val : G → LoopPrecedingConfiguration N)
  let b0 := loopLocalTransport χ N ℓ γ ψ
  let F := fun X : LoopPrecedingConfiguration N =>
    loopArcL s N b0 X.val - loopLocalLoop s N ℓ γ b0 X - loopLocalBackground s N ℓ γ b0
  let H := fun X : G => ⨆ z, |loopExteriorForce s N ℓ γ X z|
  let D := A * C0 * K * M
  have hK1 : 1 ≤ K := hK0.trans hK
  have hKpos : 0 < K := by linarith
  have hM : 0 < M := Real.rpow_pos_of_pos hKpos γ
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb : ContDiff ℝ 1 b0 := (contDiff_loopLocalTransport hχ hψ hχs N hℓ γ).of_le (by simp)
  have hp : Function.Periodic b0 (N : ℝ) := loopLocalTransport_periodic hℓ χ hpψ
  have hFm : Measurable F :=
    (((stronglyMeasurable_loopArcL hs hs1 N hb hp).measurable.comp measurable_subtype_coe).sub
      (measurable_loopLocalLoop hb.continuous s N hℓ.le γ)).sub_const _
  have hpoint (X : G) : |F X.val| ≤ D * H X := by
    rw [show F X.val = _ from loopLocalization_partial_expansion hs hs1 hℓ hK1
      (by linarith) hP hχ hχs hψ hpψ X]
    exact loopLocalization_cross_pairing_bound hs hs1 hα2 hℓ hK1 (by linarith) hP hC0
      hχs hχ01 hψ hpψ hd X
  obtain ⟨_hbad, _hHm, _hHmLp, hHnorm⟩ := hforce N ℓ γ hN hℓ hℓ1 hK hγ hP
  norm_num only [ENNReal.ofReal_ofNat] at hHnorm
  have hnorm : eLpNorm (fun X : G => F X.val) 2 ν ≤
      ENNReal.ofReal (A * Cf * C0 * K ^ (1 - γ * (s / 2 - δ))) := by
    calc
      _ ≤ eLpNorm (fun X : G => D * H X) 2 ν := by
        apply eLpNorm_mono_real (hFm.comp measurable_subtype_coe).aestronglyMeasurable
        intro X
        rw [Real.norm_eq_abs]
        exact hpoint X
      _ = ENNReal.ofReal D * eLpNorm H 2 ν := by
        rw [show (fun X : G => D * H X) = D • H from rfl,
          eLpNorm_const_smul, Real.enorm_eq_ofReal hD]
      _ ≤ ENNReal.ofReal D * ENNReal.ofReal (Cf * M ^ (-1 - s / 2 + δ)) :=
        mul_le_mul' le_rfl hHnorm
      _ = _ := by
        rw [← ENNReal.ofReal_mul hD]
        have he : M * M ^ (-1 - s / 2 + δ) = M ^ (-s / 2 + δ) := by
          conv_lhs => lhs; rw [← Real.rpow_one M]
          rw [← Real.rpow_add hM]
          congr 1
          ring
        have hpow : K * M ^ (-s / 2 + δ) = K ^ (1 - γ * (s / 2 - δ)) := by
          dsimp only [M, gradM]
          rw [← Real.rpow_mul hKpos.le]
          conv_lhs => lhs; rw [← Real.rpow_one K]
          rw [← Real.rpow_add hKpos]
          congr 1
          ring
        congr 1
        calc
          _ = A * Cf * C0 * (K * (M * M ^ (-1 - s / 2 + δ))) := by dsimp [D]; ring
          _ = _ := by rw [he, hpow]
  rw [eLpNorm_subtype_eq_restrict μ (measurableSet_loopExteriorGood N ℓ γ) hFm 2] at hnorm
  exact ⟨hnorm.trans_lt ENNReal.ofReal_lt_top, hnorm⟩

end Riesz1

end
