/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlAssemblyEnvelope
public import Riesz1.Variance.VarAlLoopEnvelope

/-!
# Uniform loop variance under the two single-singularity envelopes

Proposition 5.9, single-envelope case: every particle number,
every scale `K ≥ 1`, and the endpoint exponent are included.
The coefficient precedes the transport and the observation scale.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz1

/-- The uniform single-envelope loop variance bound, including `N = 1`
and `α = s - 1`. Finite-piece reduction for a general admissible profile
is a separate step. -/
theorem varAl_loop_variance_envelope
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) {α γ C₀ ε : ℝ} (hα : P.val.2 - 1 ≤ α) (hα2 : α < P.val.2 / 2)
    (hγ : max 4 (2 / P.val.2) ≤ γ) (hγloc : loopLocalizationExponent P.val.2 ≤ γ)
    (hC₀ : 0 < C₀) (hε : 0 < ε) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ) (ψ : ℝ → ℝ),
      0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne P.val.2 (1 - P.val.2 + α)
        ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo P.val.2 (1 - P.val.2 + α)
        ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      let K := (N : ℝ) * ℓ
      let F := fun X : Configuration N => loopFunctional P.val.2 (N : ℕ) (loopScaleField ℓ ψ) X.val
      letI := (modelWellDefined P N).2.2
      ∃ hF : MemLp F 2 (gibbsMeasure P N),
        variance (gibbsMeasure P N) F (hF.integrable one_le_two) ≤
          ENNReal.ofReal (C * K ^ (ε + max 1 (2 * (1 - P.val.2 + α)))) := by
  obtain ⟨α', hα'0, hα'1, hαα', heq⟩ : ∃ α' : ℝ,
      P.val.2 - 1 < α' ∧ α' < P.val.2 / 2 ∧ α ≤ α' ∧
        max 1 (2 * (1 - P.val.2 + α')) = max 1 (2 * (1 - P.val.2 + α)) := by
    rcases eq_or_lt_of_le hα with he | he
    · obtain ⟨α', h0, h1, hpow⟩ := Internal.varAlLoop_endpoint_exponent P.2.2.2
      exact ⟨α', h0, h1, by linarith, by simpa only [he] using hpow⟩
    · exact ⟨α, he, hα2, le_rfl, rfl⟩
  obtain ⟨Ce, hCe, he⟩ := varAl_loop_variance_single_envelope hBE hPL P hα'0 hα'1
    hγ hγloc hC₀ hε hχ hχc hχs hχ1 hχ01
  obtain ⟨Co, hCo, ho⟩ := varAlLoop_one_envelope_variance P
  refine ⟨max Ce (Co * C₀ ^ 2), lt_of_lt_of_le hCe (le_max_left _ _), ?_⟩
  intro N ℓ ψ hℓ hℓ1 hK hψ hp h1 h2
  by_cases hN : N = 1
  · subst N
    have := (modelWellDefined P 1).2.2
    have heℓ : ℓ = 1 := by norm_num at hK; linarith
    subst ℓ
    have hp1 : Function.Periodic ψ 1 := by simpa only [inv_one] using hp
    have hder : ∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne P.val.2 (1 - P.val.2 + α) 1 1 t := by
      simpa only [PNat.val_ofNat, Nat.cast_one, one_mul, inv_one] using h1
    obtain ⟨hF, hv⟩ := ho C₀ (1 - P.val.2 + α) hC₀.le (by linarith) ψ hψ hp1 hder
    have hb := hv.trans (ENNReal.ofReal_le_ofReal (le_max_right Ce (Co * C₀ ^ 2)))
    have hscale : loopScaleField 1 ψ = ψ := by
      funext x
      exact one_mul (ψ (x / 1)) |>.trans (congrArg ψ (div_one x))
    rw [hscale]
    simpa only [one_mul, PNat.val_ofNat, Nat.cast_one, Real.one_rpow,
      mul_one] using (show ∃ hF : MemLp
        (fun X : Configuration 1 => loopFunctional P.val.2 1 ψ X.val) 2 (gibbsMeasure P 1),
      variance (gibbsMeasure P 1) _ (hF.integrable one_le_two) ≤
        ENNReal.ofReal (max Ce (Co * C₀ ^ 2)) from ⟨hF, hb⟩)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = (n + 1).succPNat := by
      refine ⟨(N : ℕ) - 2, ?_⟩
      apply PNat.coe_injective
      have hN1 : (N : ℕ) ≠ 1 := fun h => hN (PNat.coe_injective h)
      have := N.pos
      simp only [Nat.succPNat_coe]
      omega
    have hd1 : ∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne P.val.2 (1 - P.val.2 + α')
        (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t := fun t =>
      (h1 t).trans (mul_le_mul_of_nonneg_left (varAlLoop_weightOne_mono hK (by linarith)) hC₀.le)
    have hd2 : ∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo P.val.2 (1 - P.val.2 + α')
        (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t := fun t =>
      (h2 t).trans (mul_le_mul_of_nonneg_left (varAlLoop_weightTwo_mono hK (by linarith)) hC₀.le)
    obtain ⟨hF, hv⟩ := he n ℓ ψ hℓ hℓ1 hK hψ hp hd1 hd2
    refine ⟨hF, hv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    rw [heq]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)

end Riesz1

end
