/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopExteriorMoments
public import Riesz1.Auxiliary.LoopLocalMomentsIntegral
public import Riesz1.ToMathlib.Moments.Decay
public import Riesz1.ToMathlib.RestrictedL2L4

/-!
# Negligibility of the localized loop on the exterior bad event

The bad-event step in the localization part of Lemma 5.8.
The polynomial probability estimate includes every `K ≥ 1`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz1

/-- The exterior bad event has arbitrary inverse-power probability, uniformly
in the particle number, including bounded scales. -/
theorem loopLocalization_bad_probability
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    (γ B : ℝ) (hγ : 1 < γ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ),
      2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      GradPartial N ℓ γ →
      loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ N (loopExteriorGood N ℓ γ)ᶜ ≤
        ENNReal.ofReal (C * ((N : ℝ) * ℓ) ^ (-B)) := by
  obtain ⟨eps0, heps0, ht⟩ := loopExteriorGood_probability hBE hPL β s hβ hs hs1
  let δ := min (s / 2) eps0 / 2
  have hmin : 0 < min (s / 2) eps0 := lt_min (by linarith) heps0
  have hδ : 0 < δ := half_pos hmin
  have hδ0 : δ < min (s / 2) eps0 := by dsimp [δ]; linarith
  obtain ⟨c, A, K0, hc, hA, hK0, hprob⟩ := ht δ hδ hδ0
  let lam := δ / (4 * (s + 2))
  have hlam : 0 < lam := div_pos hδ (by linarith)
  obtain ⟨D, hD, hdec⟩ := rpow_mul_exp_neg_bounded (β := B)
    (mul_pos (by linarith : 0 < γ) hlam) hc
  refine ⟨A * D + K0 ^ B + 1, by positivity, ?_⟩
  intro N ℓ hN hℓ hℓ1 hK hP
  let K := (N : ℝ) * ℓ
  have hKpos : 0 < K := by dsimp [K]; linarith
  by_cases hlarge : K0 ≤ K
  · have he : gradM N ℓ γ ^ lam = K ^ (γ * lam) := by
      exact (Real.rpow_mul hKpos.le γ lam).symm
    have ht := hprob N ℓ γ hN hℓ hℓ1 hlarge hγ hP
    change _ ≤ ENNReal.ofReal (A * Real.exp (-c * gradM N ℓ γ ^ lam)) at ht
    rw [he] at ht
    apply ht.trans
    apply ENNReal.ofReal_le_ofReal
    have hdecK := hdec K hK
    have hcancel : K ^ B * K ^ (-B) = 1 := by rw [← Real.rpow_add hKpos]; simp
    have hE : Real.exp (-c * K ^ (γ * lam)) ≤ D * K ^ (-B) := by
      have h := mul_le_mul_of_nonneg_right hdecK (Real.rpow_nonneg hKpos.le (-B))
      calc
        _ = (K ^ B * K ^ (-B)) * Real.exp (-c * K ^ (γ * lam)) := by rw [hcancel, one_mul]
        _ = K ^ B * Real.exp (-c * K ^ (γ * lam)) * K ^ (-B) := by ring
        _ ≤ _ := h
    have hC : A * D ≤ A * D + K0 ^ B + 1 := by
      linarith [Real.rpow_nonneg (zero_le_one.trans hK0) B]
    exact (mul_le_mul_of_nonneg_left hE hA.le).trans
      (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_right hC
        (Real.rpow_nonneg hKpos.le (-B))))
  · have hsmall : K ≤ K0 := (not_le.mp hlarge).le
    have hpow : K ^ B ≤ K0 ^ B := Real.rpow_le_rpow hKpos.le hsmall hB.le
    have hone : 1 ≤ K0 ^ B * K ^ (-B) := by
      calc
        1 = K ^ B * K ^ (-B) := by rw [← Real.rpow_add hKpos]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hKpos.le _)
    apply (prob_le_one (μ := loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ N)).trans
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    apply hone.trans
    exact mul_le_mul_of_nonneg_right
      (by nlinarith [mul_nonneg hA.le hD] : K0 ^ B ≤ A * D + K0 ^ B + 1)
      (Real.rpow_nonneg hKpos.le _)

/-- The localized loop together with its deterministic background has negligible
second moment on the exterior bad event. The estimate holds at every scale
`K ≥ 1`. Its constant is chosen before `N`, the scale and the test. -/
theorem loopLocalization_local_bad_eLpNorm
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    {α γ : ℝ} (hα : s - 1 ≤ α) (hα2 : α < s / 2) (hγ : 1 < γ)
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
      let F := fun X => loopLocalLoop s N ℓ γ b0 X + loopLocalBackground s N ℓ γ b0
      MemLp F 2 (μ.restrict (loopExteriorGood N ℓ γ)ᶜ) ∧
      eLpNorm F 2 (μ.restrict (loopExteriorGood N ℓ γ)ᶜ) ≤
        ENNReal.ofReal (C * C0 * ((N : ℝ) * ℓ) ^ (-10 : ℝ)) := by
  let d := (1 - s + α) + 2 * γ
  have hd : 0 < d := by dsimp [d]; linarith
  let B := 4 * (d + 10)
  have hB : 0 < B := by dsimp [B]; linarith
  obtain ⟨Q, hQ, hprob⟩ := loopLocalization_bad_probability hBE hPL β s hβ hs hs1 γ B hγ hB
  obtain ⟨A, hA, hmom⟩ := auxiliary_Loop_local_moments β s hβ hs hs1
    hα hα2 (p := 4) (by norm_num) hχ hχc hχs hχ1 hχ01
  refine ⟨A * Q ^ (1 / 4 : ℝ), by positivity, ?_⟩
  intro N ℓ ψ C0 hN hℓ hℓ1 hK hP hC0 hψ hpψ hdψ hddψ
  let μ := loopPrecedingMeasure (⟨(β, s), hβ, hs, hs1⟩ : Parameters) N
  let b0 := loopLocalTransport χ N ℓ γ ψ
  let F := fun X => loopLocalLoop s N ℓ γ b0 X + loopLocalBackground s N ℓ γ b0
  let S := (loopExteriorGood N ℓ γ)ᶜ
  let K := (N : ℝ) * ℓ
  have hKpos : 0 < K := by dsimp [K]; linarith
  have hF : Measurable F := (measurable_loopLocalLoop
    (contDiff_loopLocalTransport hχ hψ hχs N hℓ γ).continuous s N hℓ.le γ).add_const _
  have hnorm4 : eLpNorm F 4 μ ≤ ENNReal.ofReal (A * C0 * K ^ d) := by
    have hm := (hmom hPL N ℓ γ ψ C0 hN hℓ hK hγ hC0 hψ hpψ hdψ hddψ).2.2
    norm_num only [ENNReal.ofReal_ofNat] at hm
    have hc : eLpNorm (fun _ : LoopPrecedingConfiguration N => loopLocalBackground s N ℓ γ b0)
        4 μ = ENNReal.ofReal |loopLocalBackground s N ℓ γ b0| := by
      rw [eLpNorm_const' _ (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
        measure_univ, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs]
    exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 4)).trans (by rw [hc]; exact hm)
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
