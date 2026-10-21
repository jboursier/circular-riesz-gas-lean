/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalizationTail
public import Riesz1.Auxiliary.LoopLocalizationGlobalMoments
public import Riesz1.Auxiliary.LoopLocalizationFull

/-!
# The bounded scale range of spatial loop localization

The localization part of Lemma 5.8: all scales below any fixed
threshold are covered uniformly in the particle number, in both window regimes.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz1

private theorem norm_sub_le_three {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (U V W : Ω → ℝ) :
    eLpNorm (U - W) p μ ≤ eLpNorm (U - V) p μ + (eLpNorm V p μ + eLpNorm W p μ) := by
  have he : U - W = (U - V) + (V - W) := by
    funext X
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [he]
  exact (eLpNorm_add_le hp).trans (add_le_add le_rfl (eLpNorm_sub_le hp))

/-- A polynomial bound for the entire localization error, on the original
preceding-particle law. No lower-scale asymptotic assumption is used. -/
theorem loopLocalization_polynomial_error
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    {α γ : ℝ} (hα : s - 1 ≤ α) (hα2 : α < s / 2) (hγ : 2 ≤ γ)
    {p : ℝ} (hp : 1 ≤ p)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ) (ψ : ℝ → ℝ) (C0 : ℝ),
      2 ≤ (N : ℕ) → 0 < ℓ → 1 ≤ (N : ℝ) * ℓ →
      0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤
        C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      let b0 := loopLocalTransport χ N ℓ γ ψ
      let F := fun X : LoopPrecedingConfiguration N =>
        loopArcL s N (loopScaleField ((N : ℝ) * ℓ) ψ) X.val -
        loopLocalLoop s N ℓ γ b0 X - loopLocalBackground s N ℓ γ b0
      let μ := loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ N
      MemLp F (ENNReal.ofReal p) μ ∧ eLpNorm F (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (C * C0 * ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ)) := by
  obtain ⟨A, hA, htail⟩ := loopLocalization_tail_eLpNorm hBE hPL hβ hs hs1
    hα hα2 (p := p) hp hχ hχc hχs hχ1 hχ01
  obtain ⟨B, hB, hglobal⟩ := loopLocalization_global_moments hBE hPL hβ hs hs1
    hα hα2 (p := p) hp hχ hχc hχs hχ1 hχ01
  obtain ⟨D, hD, hlocal⟩ := auxiliary_Loop_local_moments β s hβ hs hs1
    hα hα2 (p := p) hp hχ hχc hχs hχ1 hχ01
  refine ⟨A + B + D, by positivity, ?_⟩
  intro N ℓ ψ C0 hN hℓ hK hC0 hψ hpψ hd hdd
  let K := (N : ℝ) * ℓ
  let d := (1 - s + α) + 2 * γ
  let μ := loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ N
  let b0 := loopLocalTransport χ N ℓ γ ψ
  let U := fun X : LoopPrecedingConfiguration N => loopArcL s N (loopScaleField K ψ) X.val
  let V := fun X : LoopPrecedingConfiguration N => loopArcL s N b0 X.val
  let W := fun X : LoopPrecedingConfiguration N =>
    loopLocalLoop s N ℓ γ b0 X + loopLocalBackground s N ℓ γ b0
  have he : (fun X : LoopPrecedingConfiguration N =>
      loopArcL s N (loopScaleField K ψ) X.val - loopLocalLoop s N ℓ γ b0 X -
      loopLocalBackground s N ℓ γ b0) = U - W := by funext X; dsimp [U, W]; ring
  have hn : eLpNorm (U - W) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ((A + B + D) * C0 * K ^ d) := by
    by_cases hP : GradPartial N ℓ γ
    · have ht := (htail N ℓ γ ψ C0 hℓ hK hγ hP hC0 hψ hpψ hd hdd).2
      have hg := (hglobal N ℓ γ ψ C0 hℓ hK (by linarith) hC0 hψ hpψ hd hdd).2
      have hl := (hlocal hPL N ℓ γ ψ C0 hN hℓ hK (by linarith) hC0 hψ hpψ hd hdd).2.2
      have hc : eLpNorm (fun _ : LoopPrecedingConfiguration N =>
          loopLocalBackground s N ℓ γ b0) (ENNReal.ofReal p) μ = ENNReal.ofReal |loopLocalBackground s N ℓ γ b0| := by
        rw [eLpNorm_const' _ (ENNReal.ofReal_pos.mpr (by linarith : 0 < p)).ne' ENNReal.ofReal_ne_top,
          measure_univ, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs]
      have hw : eLpNorm W (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (D * C0 * K ^ d) := by
        apply (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hp)).trans
        rw [hc]
        exact hl
      have hpow1 : K ^ (2 - s - γ * (1 - s)) ≤ K ^ d := by
        apply Real.rpow_le_rpow_of_exponent_le hK
        dsimp [d]
        nlinarith
      have hpow2 : K ^ ((1 - s + α) + γ) ≤ K ^ d := by
        apply Real.rpow_le_rpow_of_exponent_le hK
        dsimp [d]
        linarith
      have ht' : eLpNorm (U - V) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (A * C0 * K ^ d) :=
        ht.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow1 (by positivity)))
      have hg' : eLpNorm V (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (B * C0 * K ^ d) :=
        hg.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow2 (by positivity)))
      calc
        _ ≤ eLpNorm (U - V) (ENNReal.ofReal p) μ + (eLpNorm V (ENNReal.ofReal p) μ + eLpNorm W (ENNReal.ofReal p) μ) := norm_sub_le_three μ (ENNReal.ofReal p) (ENNReal.one_le_ofReal.mpr hp) U V W
        _ ≤ ENNReal.ofReal (A * C0 * K ^ d) +
            (ENNReal.ofReal (B * C0 * K ^ d) + ENNReal.ofReal (D * C0 * K ^ d)) :=
          add_le_add ht' (add_le_add hg' hw)
        _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
    · have hz : U - W = 0 := by
        ext X
        have h := loopLocalization_full_error_zero (s := s) hP hℓ χ hpψ X
        change U X - W X = 0
        dsimp [U, W]
        dsimp [K, b0]
        linarith
      rw [hz, eLpNorm_zero]
      exact bot_le
  dsimp only
  rw [he]
  exact ⟨hn.trans_lt ENNReal.ofReal_lt_top, hn⟩

/-- Every bounded scale range satisfies the square-root bound for
the complete localization error, uniformly in `N`, with the threshold fixed
before the particle number and test. -/
theorem loopLocalization_bounded_scale
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    {α γ : ℝ} (hα : s - 1 ≤ α) (hα2 : α < s / 2) (hγ : 2 ≤ γ)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (K0 : ℝ) (hK0 : 1 ≤ K0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ) (ψ : ℝ → ℝ) (C0 : ℝ),
      2 ≤ (N : ℕ) → 0 < ℓ → 1 ≤ (N : ℝ) * ℓ → (N : ℝ) * ℓ ≤ K0 →
      0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤
        C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      let b0 := loopLocalTransport χ N ℓ γ ψ
      let F := fun X : LoopPrecedingConfiguration N =>
        loopArcL s N (loopScaleField ((N : ℝ) * ℓ) ψ) X.val -
        loopLocalLoop s N ℓ γ b0 X - loopLocalBackground s N ℓ γ b0
      let μ := loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ N
      MemLp F 2 μ ∧ eLpNorm F 2 μ ≤
        ENNReal.ofReal (C * C0 * ((N : ℝ) * ℓ) ^ (1 / 2 : ℝ)) := by
  obtain ⟨A, hA, herr⟩ := loopLocalization_polynomial_error hBE hPL β s hβ hs hs1
    hα hα2 hγ (p := 2) (by norm_num) hχ hχc hχs hχ1 hχ01
  let d := (1 - s + α) + 2 * γ
  refine ⟨A * K0 ^ d, by positivity, ?_⟩
  intro N ℓ ψ C0 hN hℓ hK hKK0 hC0 hψ hp hd hdd
  obtain ⟨hm, hn⟩ := herr N ℓ ψ C0 hN hℓ hK hC0 hψ hp hd hdd
  norm_num only [ENNReal.ofReal_ofNat] at hm hn
  refine ⟨hm, hn.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hpow : ((N : ℝ) * ℓ) ^ d ≤ K0 ^ d :=
    Real.rpow_le_rpow (by linarith) hKK0 (by dsimp [d]; linarith)
  have hsqrt : 1 ≤ ((N : ℝ) * ℓ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hK (by norm_num)
  calc
    _ ≤ A * C0 * K0 ^ d := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (A * K0 ^ d * C0) * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt (by positivity)

end Riesz1

end
