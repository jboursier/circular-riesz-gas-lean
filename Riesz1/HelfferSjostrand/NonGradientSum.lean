/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.NonGradientInverse

/-! # Preservation of the pointwise zero coordinate sum

The last assertion of Proposition 3.2. The argument
works for every compatible field with zero coordinate sum, without requiring
that its components be functions of the gaps.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace

namespace Riesz1

variable {N : ℕ+} {c C_N : ℝ} (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ))
  (hc : 0 < c) (hadm : HsAdmissible χ C_N)

local notation "μ" => (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))

/-- The rotation test pairs with the scalar coordinate sum of the vector field. -/
theorem hsNonGradient_form_rotationField (u : HsVectorSobolev χ hN hc μ) (f : HsSobolev μ) :
    hsVectorSobolevForm χ hN hc μ u (hsRotationField χ hc hadm f) =
      (Real.sqrt (N : ℕ))⁻¹ * inner ℝ
        (hsSobolevGradient μ (∑ i : Fin (N : ℕ), u.val.ofLp.1 i)) (hsSobolevGradient μ f) := by
  change (∑ i : Fin (N : ℕ), inner ℝ (hsSobolevGradient μ (u.val.ofLp.1 i))
    (hsSobolevGradient μ (hsUnitVector N i • f))) + inner ℝ _ 0 = _
  simp only [map_smul, real_inner_smul_right, inner_zero_right, add_zero]
  simp only [hsUnitVector, hsRotationVector, PiLp.smul_apply, smul_eq_mul, mul_one]
  rw [← Finset.mul_sum, map_sum, sum_inner]

/-- A pointwise zero-sum forcing annihilates every rotation test. -/
theorem hsNonGradient_pairing_rotationField_zero
    (v : Lp (HsEuclidean N) 2 μ) (hv : ∀ᵐ x ∂μ, ∑ i : Fin (N : ℕ), v x i = 0)
    (f : HsSobolev μ) :
    hsNonGradientPairing μ v (hsRotationField χ hc hadm f).val = 0 := by
  rw [hsNonGradientPairing_eq_integral]
  apply integral_eq_zero_of_ae
  have he (i : Fin (N : ℕ)) :
      (hsJetValue μ i (hsRotationField χ hc hadm f).val : HsConfiguration N → ℝ) =ᵐ[μ]
        fun x => hsUnitVector N i * hsSobolevValue μ f x := by
    rw [hsRotationField_value]
    exact Lp.coeFn_smul _ _
  filter_upwards [hv, ae_all_iff.mpr he] with x hx he
  simp_rw [he]
  simp only [hsUnitVector, hsRotationVector, PiLp.smul_apply, smul_eq_mul, mul_one]
  rw [← Finset.sum_mul, hx, zero_mul]
  rfl

namespace Internal

theorem hsNonGradient_zero_sum_of_solves (hadm : HsAdmissible χ C_N)
    (hPL : External.PrekopaLeindler) (v : Lp (HsEuclidean N) 2 μ)
    (hv : ∀ᵐ x ∂μ, ∑ i : Fin (N : ℕ), v x i = 0)
    (u : HsVectorSobolev χ hN hc μ) (hu : hsNonGradientMean χ hN hc μ u = 0)
    (hsol : HsNonGradientSolves χ hN hc v u) :
    ∀ᵐ x ∂μ, ∑ i : Fin (N : ℕ), hsJetValue μ i u.val x = 0 := by
  let f : HsSobolev μ := ∑ i : Fin (N : ℕ), u.val.ofLp.1 i
  have hmean : poissonMean μ (hsSobolevValue μ f) = 0 := by
    change poissonMean μ (hsSobolevValue μ (∑ i : Fin (N : ℕ), u.val.ofLp.1 i)) = 0
    rw [map_sum, map_sum]
    exact (hsVectorMean_eq_sum μ u.val).symm.trans hu
  have hq := (hsNonGradient_form_rotationField χ hN hc hadm u f).symm.trans
    ((hsol (hsRotationField χ hc hadm f)).trans
      (hsNonGradient_pairing_rotationField_zero χ hc hadm v hv f))
  have hg : ‖hsSobolevGradient μ f‖ ^ 2 = 0 := by
    change (Real.sqrt (N : ℕ))⁻¹ * inner ℝ (hsSobolevGradient μ f) (hsSobolevGradient μ f) = 0 at hq
    rw [real_inner_self_eq_norm_sq] at hq
    exact (mul_eq_zero.mp hq).resolve_left
      (inv_ne_zero (Real.sqrt_pos.mpr (Nat.cast_pos.mpr N.pos)).ne')
  have hp := hsScalar_poincare_norm hPL χ hN hc f
  rw [hmean, hg, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, mul_zero] at hp
  have hf : hsSobolevValue μ f = 0 := norm_eq_zero.mp (by
    nlinarith only [hp, norm_nonneg (hsSobolevValue μ f)])
  have hs : (∑ i : Fin (N : ℕ), hsJetValue μ i u.val) = 0 := by
    change (∑ i : Fin (N : ℕ), hsSobolevValue μ (u.val.ofLp.1 i)) = 0
    rw [← map_sum]
    exact hf
  have ha := Lp.coeFn_finsetSum (Finset.univ : Finset (Fin (N : ℕ)))
    (fun i => hsJetValue μ i u.val)
  rw [hs] at ha
  filter_upwards [ha, Lp.coeFn_zero ℝ 2 μ] with x hx hz
  simpa only [Finset.sum_apply, Pi.zero_apply] using hx.symm.trans hz

end Internal

/-- Pointwise zero sum is preserved by the normalized inverse. -/
theorem hsInverse_sum_zero (hPL : External.PrekopaLeindler) (hadm : HsAdmissible χ C_N)
    (v : hsMeanZeroL2 μ) (hv : ∀ᵐ x ∂μ, ∑ i : Fin (N : ℕ), v.val x i = 0) :
    ∀ᵐ x ∂μ, ∑ i : Fin (N : ℕ), hsJetValue μ i (hsInverse hPL χ hN hc v).val.val x = 0 :=
  Internal.hsNonGradient_zero_sum_of_solves χ hN hc hadm hPL v.val hv
    (hsInverse hPL χ hN hc v).val (hsInverse hPL χ hN hc v).property
    (hsInverse_solves hPL χ hN hc hadm v)

end Riesz1
