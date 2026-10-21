/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.CoercivityKernel

/-!
# Constant direction, normalized coercivity and kernel

The full quotient statement of the coercivity assertions of Proposition 3.2.
Together with `anchored_vector_coercivity` this covers every coercivity assertion of that
proposition. The coordinate-sum normalization is equivalent to vanishing
mean component along `e`, since every coordinate of `e` is `1 / √N`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Riesz1

/-- Proposition 3.2 (coercivity), all quotient assertions. -/
theorem hs_vector_coercivity {N : ℕ+} {c C_N : ℝ} (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c) (hadm : HsAdmissible χ C_N) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    (∀ h : HsSobolev μ,
      (∀ i : Fin (N : ℕ), hsJetValue μ i (hsRotationField χ hc hadm h).val =
        hsUnitVector N i • hsSobolevValue μ h) ∧
      hsVectorSobolevForm χ hadm.choose hc μ
        (hsRotationField χ hc hadm h) (hsRotationField χ hc hadm h) =
          ‖hsSobolevGradient μ h‖ ^ 2) ∧
    (∀ u : HsVectorSobolev χ hadm.choose hc μ,
      (∑ i : Fin (N : ℕ), ∫ x, hsJetValue μ i u.val x ∂μ) = 0 →
        (∫ x, ∑ i : Fin (N : ℕ), (hsJetValue μ i u.val x) ^ 2 ∂μ) ≤
          hsPoincareConstant N c * hsVectorSobolevForm χ hadm.choose hc μ u u) ∧
    (∀ u : HsVectorSobolev χ hadm.choose hc μ,
      hsVectorSobolevForm χ hadm.choose hc μ u u = 0 ↔
        ∃ a : ℝ, u = hsRotationField χ hc hadm (a • hsPoissonUnit μ)) := by
  refine ⟨?_, ?_, hsVector_form_eq_zero_iff hPL χ hc hadm⟩
  · intro h
    refine ⟨hsRotationField_value χ hc hadm h, ?_⟩
    rw [hsRotationField_form]
    exact real_inner_self_eq_norm_sq (hsSobolevGradient _ h)
  · intro u hu
    rw [← hsVectorValueNormSq_eq_integral]
    apply hsVector_normalized_coercivity hPL χ hadm.choose hc u
    simpa only [poissonMean_eq_integral] using hu

/-- The normalized bound with the literal mean `e`-component condition. -/
theorem hs_vector_coercivity_rotation_normalization {N : ℕ+} {c : ℝ}
    (hPL : External.PrekopaLeindler) (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (u : HsVectorSobolev χ hN hc (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (hu : (∫ x, ∑ i : Fin (N : ℕ), hsJetValue _ i u.val x * hsUnitVector N i
      ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) = 0) :
    (∫ x, ∑ i : Fin (N : ℕ), (hsJetValue _ i u.val x) ^ 2
      ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) ≤
        hsPoincareConstant N c * hsVectorSobolevForm χ hN hc _ u u := by
  rw [hsVector_rotation_mean] at hu
  have hm : hsVectorMean _ u.val = 0 := (mul_eq_zero.mp hu).resolve_left
    (inv_ne_zero (Real.sqrt_pos.mpr (Nat.cast_pos.mpr N.pos)).ne')
  rw [← hsVectorValueNormSq_eq_integral]
  exact hsVector_normalized_coercivity hPL χ hN hc u ((hsVectorMean_eq_sum _ _).symm.trans hm)

end Riesz1
