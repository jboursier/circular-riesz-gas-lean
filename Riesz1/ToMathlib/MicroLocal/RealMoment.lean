/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite nonnegative moment bounds and real expectations

Conversion from a lower-integral bound proves integrability before
introducing the real-valued expectation.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- Internal conversion lemma: a finite nonnegative lower-integral bound
gives integrability and the corresponding real integral inequality. -/
theorem integral_le_of_lintegral_bound_internal {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    (F : α → ℝ) (G : β → ℝ) (hF : AEStronglyMeasurable F μ)
    (hF0 : 0 ≤ᵐ[μ] F) (hG : Integrable G ν) (hG0 : 0 ≤ᵐ[ν] G)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≤
      ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (G y) ∂ν) :
    Integrable F μ ∧ (∫ x, F x ∂μ) ≤ C * ∫ y, G y ∂ν := by
  have hr : ENNReal.ofReal (C * ∫ y, G y ∂ν) =
      ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (G y) ∂ν := by
    rw [ENNReal.ofReal_mul hC, ofReal_integral_eq_lintegral_ofReal hG hG0]
  have hb : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≤ ENNReal.ofReal (C * ∫ y, G y ∂ν) := by
    rw [hr]
    exact hbound
  have hi : Integrable F μ := ⟨hF, (hasFiniteIntegral_iff_ofReal hF0).mpr
    (hb.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hC (integral_nonneg_of_ae hG0))).mp ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hi hF0]
  exact hb

end Riesz1
