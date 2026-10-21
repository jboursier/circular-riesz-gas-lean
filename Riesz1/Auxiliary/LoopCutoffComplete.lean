/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopCutoffRegularity
public import Riesz1.Auxiliary.LoopCutoffRotation
public import Riesz1.Auxiliary.LoopCutoffSmooth
public import Riesz1.Auxiliary.LoopCutoffExplicitBound
public import Riesz1.Auxiliary.LoopCutoffProbability

/-!
# The complete anchored cutoff statements

The cutoff data part and the cutoff part of Lemma 5.8.
The probability assertion remains conditional on rigidity.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal ContDiff

namespace Riesz1

/-- The regularity, rotation, and value-range assertions of the cutoff definition.
The formulae themselves are `loopCutoff`, `loopTransport`, and `loopCutoffF`. -/
theorem auxiliary_Loop_cutoff_data (s γ ε : ℝ) (N : ℕ+) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {χ ψ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4)) (hp : Function.Periodic ψ ℓ⁻¹) :
    ContDiff ℝ ∞ (loopTransport χ N ℓ γ ψ) ∧
    Function.Periodic (loopTransport χ N ℓ γ ψ) ℓ⁻¹ ∧
    LocallyLipschitzOn (orderedDomain N) (loopCutoff s γ ε N ℓ) ∧
    (∀ S : Set (Fin (N : ℕ) → ℝ), IsCompact S → S ⊆ orderedDomain N →
      ∃ C : ℝ≥0, LipschitzOnWith C (loopCutoff s γ ε N ℓ) S) ∧
    (∀ X : Fin (N : ℕ) → ℝ, 0 ≤ loopCutoff s γ ε N ℓ X ∧ loopCutoff s γ ε N ℓ X ≤ 1) ∧
    (∀ (t : ℝ) (X : Configuration N),
      loopCutoff s γ ε N ℓ (loopRotate N t X).val = loopCutoff s γ ε N ℓ X.val) := by
  exact ⟨contDiff_loopTransport hχ hψ hχs N hℓ γ, loopTransport_periodic hℓ χ hp,
    loopCutoff_locallyLipschitzOn s γ ε N hℓ,
    fun _ hS hSD => loopCutoff_lipschitzOn_compact s γ ε N hℓ hS hSD,
    fun X => loopCutoff_mem_Icc s γ ε ℓ X, fun t X => loopCutoff_rotate s γ ε N ℓ t X⟩

namespace Internal

/-- The cutoff part of Lemma 5.8, every assertion. The envelope constant is chosen
before `γ`, `ε`, and `B₀`, so it depends only on `s`, `α`, and `χ`. The other constants are
chosen before the particle number, scale, profile, and anchored configuration. -/
theorem auxiliary_Loop_cutoff_of_rigidity (β s α : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    (hα : s - 1 ≤ α) (hα2 : α < s / 2) (hRig : RigidityConclusion β s hβ hs hs1)
    (hPL : External.PrekopaLeindler) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ Cenv : ℝ, 0 ≤ Cenv ∧ ∀ γ ε B₀ : ℝ, 1 < γ → 0 < ε →
      ε < min (1 / 8) ((1 - s / 2) / 8) → 0 < B₀ →
      ∃ C B₁ : ℝ, B₁ = (1 - s + α) + 2 * γ + ε * (s + 1) ∧ 0 < C ∧ 0 < B₁ ∧
        ∀ (N : ℕ+) (ℓ : ℝ), 2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
          gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N
            {X | loopCutoff s γ ε N ℓ X.val ≠ 1} ≤
              ENNReal.ofReal (C * ((N : ℝ) * ℓ) ^ (-B₀)) ∧
          (∀ X : Configuration N, 0 < loopCutoff s γ ε N ℓ X.val →
            gradEvent s (2 * γ) ε N ℓ X.val) ∧
          ∀ (C0 : ℝ) (ψ : ℝ → ℝ), 0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
            (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
            (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
            (∀ y : Fin (N : ℕ) → ℝ, y ∈ orderedDomain N → y ⟨0, N.pos⟩ = 0 →
              |loopCutoffF χ s γ ε N ℓ ψ y| ≤ C * C0 * ((N : ℝ) * ℓ) ^ B₁) ∧
            (∀ t, |deriv (loopTransport χ N ℓ γ ψ) t| ≤
                Cenv * C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t ∧
              |deriv (deriv (loopTransport χ N ℓ γ ψ)) t| ≤
                Cenv * C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) := by
  obtain ⟨Cenv, hCenv, henv⟩ := loopTransport_envelope hs hs1 hα hα2 hχ hχc hχs hχ1 hχ01
  refine ⟨Cenv, hCenv, fun γ ε B₀ hγ hε hε1 hB₀ => ?_⟩
  have hεs : ε ≤ 1 - s / 2 := by
    have h := lt_of_lt_of_le hε1 (min_le_right _ _)
    linarith
  obtain ⟨Cp, hCp, hprob⟩ := loopCutoff_probability_of_rigidity β s hβ hs hs1 hPL hRig
    γ ε hγ hε hε1 B₀ hB₀
  obtain ⟨Cf, hCf, hbound⟩ := loopCutoffF_explicit_bound hs hs1 hα hα2 hγ hε hεs
    hχ hχc hχs hχ1 hχ01
  have hB : 0 < (1 - s + α) + 2 * γ + ε * (s + 1) := by
    have ha : 0 ≤ 1 - s + α := by linarith
    have he : 0 < ε * (s + 1) := mul_pos hε (by linarith)
    linarith
  refine ⟨Cp + Cf, (1 - s + α) + 2 * γ + ε * (s + 1), rfl, by linarith, hB, ?_⟩
  intro N ℓ hN hℓ hℓ1 hK
  refine ⟨(hprob N hN ℓ hℓ hℓ1 hK).trans (ENNReal.ofReal_le_ofReal ?_),
    fun X hX => gradEvent_of_loopCutoff_pos hℓ X hX, ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _)
  · intro C0 ψ hC0 hψ hp hd1 hd2
    refine ⟨fun y hy hy0 => ?_, henv N ℓ γ ψ C0 hℓ hK hγ hC0 hψ hp hd1 hd2⟩
    apply (hbound C0 N ℓ ψ y hC0 hN hℓ hK hψ hp hd1 hd2 hy hy0).trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (by linarith) hC0
    · exact le_refl _
    · exact Real.rpow_nonneg (by linarith) _
    · exact mul_nonneg (by linarith) hC0

end Internal

end Riesz1

end
