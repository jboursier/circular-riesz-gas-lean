/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlLoopOne
public import Riesz1.Auxiliary.GradientSplittingZWeights
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Endpoint envelopes and the one-particle case

The envelope monotonicity used to move the endpoint of Proposition 5.9
into the interior, and the variance bound for `N = 1`
in precisely the envelope notation.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Riesz1

/-- Increasing the singularity exponent enlarges the first envelope. -/
theorem varAlLoop_weightOne_mono {s a a' K L u : ℝ} (hK : 1 ≤ K) (ha : a ≤ a') :
    gradWeightOne s a K L u ≤ gradWeightOne s a' K L u := by
  unfold gradWeightOne
  split_ifs with hu
  · apply Real.rpow_le_rpow_of_exponent_ge
      (lt_max_of_lt_right (inv_pos.mpr (by linarith : 0 < K)))
      (max_le hu.le (inv_le_one_of_one_le₀ hK))
    linarith
  · exact le_rfl

/-- Increasing the singularity exponent enlarges the second envelope. -/
theorem varAlLoop_weightTwo_mono {s a a' K L u : ℝ} (hK : 1 ≤ K) (ha : a ≤ a') :
    gradWeightTwo s a K L u ≤ gradWeightTwo s a' K L u := by
  unfold gradWeightTwo
  split_ifs with hu
  · apply Real.rpow_le_rpow_of_exponent_ge
      (lt_max_of_lt_right (inv_pos.mpr (by linarith : 0 < K)))
      (max_le hu.le (inv_le_one_of_one_le₀ hK))
    linarith
  · exact le_rfl

/-- Proposition 5.9, `N = 1`, for every envelope-bounded smooth
transport, with the coefficient before the envelope amplitude and profile.
This includes the endpoint `b = 0`. -/
theorem varAlLoop_one_envelope_variance (P : Parameters) :
    letI := (modelWellDefined P 1).2.2
    ∃ C : ℝ, 0 < C ∧ ∀ (C₀ b : ℝ), 0 ≤ C₀ → 0 ≤ b →
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → Function.Periodic ψ 1 →
        (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne P.val.2 b 1 1 t) →
        ∃ hF : MemLp (fun X : Configuration 1 => loopFunctional P.val.2 1 ψ X.val)
            2 (gibbsMeasure P 1),
          variance (gibbsMeasure P 1) _ (hF.integrable one_le_two) ≤ ENNReal.ofReal (C * C₀ ^ 2) := by
  have := (modelWellDefined P 1).2.2
  obtain ⟨C, hC, hc⟩ := varAlLoop_one_variance P
  refine ⟨C, hC, ?_⟩
  intro C₀ b hC₀ hb ψ hψ hp hd
  have hlip : LipschitzWith ⟨C₀, hC₀⟩ ψ := by
    apply lipschitzWith_of_nnnorm_deriv_le (hψ.differentiable (by simp))
    intro t
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm, Real.norm_eq_abs]
    calc
      |deriv ψ t| ≤ C₀ * gradWeightOne P.val.2 b 1 1 t := hd t
      _ ≤ C₀ * (1 : ℝ) ^ b := mul_le_mul_of_nonneg_left
        (gradWeightOne_le_K_pow P.2.2.2 hb le_rfl) hC₀
      _ = C₀ := by rw [Real.one_rpow, mul_one]
  exact hc ⟨C₀, hC₀⟩ ψ hlip hp

end Riesz1

end
