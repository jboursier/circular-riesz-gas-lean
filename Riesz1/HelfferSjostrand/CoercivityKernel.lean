/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.CoercivityBounds

/-! # The kernel of the full vector form

The remaining kernel assertion of Proposition 3.2.
Subtracting the mean rotation component reduces it to normalized coercivity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

theorem hsUnitVector_sum (N : ℕ+) :
    ∑ i : Fin (N : ℕ), hsUnitVector N i = Real.sqrt (N : ℕ) := by
  have hpos : (0 : ℝ) < (N : ℕ) := Nat.cast_pos.mpr N.pos
  have hn := Real.sq_sqrt hpos.le
  simp only [hsUnitVector, hsRotationVector, PiLp.smul_apply, smul_eq_mul, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    (N : ℝ) * (Real.sqrt (N : ℕ))⁻¹ =
        (Real.sqrt (N : ℕ)) ^ 2 * (Real.sqrt (N : ℕ))⁻¹ := congrArg (· * _) hn.symm
    _ = Real.sqrt (N : ℕ) := by
      field_simp

/-- Expected coordinate sum, a continuous functional on vector jets. -/
def hsVectorMean (μ : Measure (HsConfiguration N)) [IsProbabilityMeasure μ] :
    HsVectorJet μ →L[ℝ] ℝ := ∑ i : Fin (N : ℕ), (poissonMean μ).comp (hsJetValue μ i)

theorem hsVectorMean_eq_sum (μ : Measure (HsConfiguration N)) [IsProbabilityMeasure μ]
    (u : HsVectorJet μ) : hsVectorMean μ u = ∑ i, poissonMean μ (hsJetValue μ i u) := by
  simp only [hsVectorMean, sum_apply, ContinuousLinearMap.comp_apply]

/-- The paper's mean `e`-component is the expected coordinate sum divided by `√N`. -/
theorem hsVector_rotation_mean (μ : Measure (HsConfiguration N)) [IsProbabilityMeasure μ]
    (u : HsVectorJet μ) :
    (∫ x, ∑ i : Fin (N : ℕ), hsJetValue μ i u x * hsUnitVector N i ∂μ) =
      (Real.sqrt (N : ℕ))⁻¹ * hsVectorMean μ u := by
  rw [integral_finsetSum _ (fun i _ => ((Lp.memLp (hsJetValue μ i u)).integrable one_le_two).mul_const _),
    hsVectorMean_eq_sum]
  simp_rw [integral_mul_const, poissonMean_eq_integral]
  simp only [hsUnitVector, hsRotationVector, PiLp.smul_apply, smul_eq_mul, mul_one]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem hsVectorMean_rotationUnit (χ : HsPairPotentials N c) (hc : 0 < c) {C_N : ℝ}
    (hadm : HsAdmissible χ C_N) (a : ℝ) :
    hsVectorMean _ (hsRotationField χ hc hadm (a • hsPoissonUnit _)).val =
      a * Real.sqrt (N : ℕ) := by
  rw [hsVectorMean_eq_sum]
  simp_rw [hsRotationField_value, map_smul, hsPoissonUnit_value, poissonMean_one,
    smul_eq_mul, mul_one]
  rw [← Finset.sum_mul, hsUnitVector_sum, mul_comm]

theorem hsVectorMean_sub_rotationUnit (χ : HsPairPotentials N c) (hc : 0 < c) {C_N : ℝ}
    (hadm : HsAdmissible χ C_N)
    (u : HsVectorSobolev χ hadm.choose hc (hsQuotientGibbsProbability χ hc : Measure _))
    (a : ℝ) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    hsVectorMean μ (u - hsRotationField χ hc hadm (a • hsPoissonUnit μ)).val =
      hsVectorMean μ u.val - a * Real.sqrt (N : ℕ) := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  let r := hsRotationField χ hc hadm (a • hsPoissonUnit μ)
  change hsVectorMean μ (u.val - r.val) = _
  calc
    hsVectorMean μ (u.val - r.val) = hsVectorMean μ u.val - hsVectorMean μ r.val :=
      map_sub (hsVectorMean μ) _ _
    _ = hsVectorMean μ u.val - a * Real.sqrt (N : ℕ) :=
      congrArg (hsVectorMean μ u.val - ·) (hsVectorMean_rotationUnit χ hc hadm a)

/-- The value norm is the integral of the sum of squared components. -/
theorem hsVectorValueNormSq_eq_integral (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]
    (u : HsVectorJet μ) :
    hsVectorValueNormSq μ u = ∫ x, ∑ i : Fin (N : ℕ), (hsJetValue μ i u x) ^ 2 ∂μ := by
  unfold hsVectorValueNormSq
  simp_rw [poisson_norm_sq μ]
  exact (integral_finsetSum _ (fun i _ => (Lp.memLp _).integrable_sq)).symm

/-- Vanishing of the value norm forces the vector completion element to vanish. -/
theorem hsVector_eq_zero_of_valueNormSq (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ))
    (hc : 0 < c)
    (u : HsVectorSobolev χ hN hc (hsQuotientGibbsProbability χ hc : Measure _))
    (hu : hsVectorValueNormSq _ u.val ≤ 0) : u = 0 := by
  apply hsVectorSobolev_eq_zero_of_values χ hN hc u
  intro i
  apply norm_eq_zero.mp
  have hi : ‖hsJetValue _ i u.val‖ ^ 2 ≤ hsVectorValueNormSq _ u.val :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖hsJetValue _ j u.val‖) (Finset.mem_univ i)
  nlinarith only [hi, hu, norm_nonneg (hsJetValue _ i u.val)]

/-- Adding a constant rotation field leaves every vector gradient and pair energy unchanged. -/
theorem hsVector_form_sub_rotationUnit (χ : HsPairPotentials N c) (hc : 0 < c) {C_N : ℝ}
    (hadm : HsAdmissible χ C_N)
    (u : HsVectorSobolev χ hadm.choose hc (hsQuotientGibbsProbability χ hc : Measure _))
    (a : ℝ) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    let v := u - hsRotationField χ hc hadm (a • hsPoissonUnit μ)
    hsVectorSobolevForm χ hadm.choose hc μ v v =
      hsVectorSobolevForm χ hadm.choose hc μ u u := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  change (∑ i : Fin (N : ℕ), inner ℝ
      (hsSobolevGradient μ (u.val.ofLp.1 i - hsUnitVector N i • (a • hsPoissonUnit μ)))
      (hsSobolevGradient μ (u.val.ofLp.1 i - hsUnitVector N i • (a • hsPoissonUnit μ)))) +
      inner ℝ (u.val.ofLp.2 - 0) (u.val.ofLp.2 - 0) = _
  simp only [map_sub, map_smul, hsPoissonUnit_gradient, smul_zero, sub_zero]
  rfl

/-- The kernel is exactly the constant multiples of the unit rotation field. -/
theorem hsVector_form_eq_zero_iff (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c) {C_N : ℝ} (hadm : HsAdmissible χ C_N)
    (u : HsVectorSobolev χ hadm.choose hc (hsQuotientGibbsProbability χ hc : Measure _)) :
    hsVectorSobolevForm χ hadm.choose hc _ u u = 0 ↔
      ∃ a : ℝ, u = hsRotationField χ hc hadm (a • hsPoissonUnit _) := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  constructor
  · intro hq
    let a : ℝ := hsVectorMean μ u.val / Real.sqrt (N : ℕ)
    let v := u - hsRotationField χ hc hadm (a • hsPoissonUnit μ)
    have hm : ∑ i, poissonMean μ (hsJetValue μ i v.val) = 0 := by
      rw [← hsVectorMean_eq_sum, hsVectorMean_sub_rotationUnit χ hc hadm u a]
      dsimp only [a]
      rw [div_mul_cancel₀ _ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr N.pos)).ne', sub_self]
    have hb := hsVector_normalized_coercivity hPL χ hadm.choose hc v hm
    have hqv : hsVectorSobolevForm χ hadm.choose hc μ v v = 0 :=
      (hsVector_form_sub_rotationUnit χ hc hadm u a).trans hq
    rw [hqv, mul_zero] at hb
    have hz := hsVector_eq_zero_of_valueNormSq χ hadm.choose hc v hb
    exact ⟨a, sub_eq_zero.mp hz⟩
  · rintro ⟨a, rfl⟩
    rw [hsRotationField_form]
    change inner ℝ (hsSobolevGradient μ (a • hsPoissonUnit μ))
      (hsSobolevGradient μ (a • hsPoissonUnit μ)) = 0
    rw [map_smul, hsPoissonUnit_gradient, smul_zero, inner_zero_left]

end Riesz1
