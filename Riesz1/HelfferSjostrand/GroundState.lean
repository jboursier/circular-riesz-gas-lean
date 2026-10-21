/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SettingGibbs
public import Riesz1.ToMathlib.SquareDensityL2

/-!
# The normalized ground-state transform

The unitary map on the full Gibbs `L²` space.
Both real and complex scalar structures are provided.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter

namespace Riesz1

variable {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)

/-- The positive square root of the normalized Gibbs density, `Z⁻¹ᐟ² exp(-H/2)`. -/
def hsGroundStateMultiplier (x : HsConfiguration N) : ℝ :=
  (Real.sqrt (hsPartitionFunction χ).toReal)⁻¹ * Real.exp (-hsHamiltonian χ x / 2)

include hc in
theorem hsGroundStateMultiplier_pos (x : HsConfiguration N) :
    0 < hsGroundStateMultiplier χ x := by
  have hZ := ENNReal.toReal_pos (hsPartitionFunction_pos χ).ne'
    (hsPartitionFunction_lt_top χ hc).ne
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hZ)) (Real.exp_pos _)

theorem measurable_hsGroundStateMultiplier : Measurable (hsGroundStateMultiplier χ) := by
  unfold hsGroundStateMultiplier
  exact ((Real.measurable_exp.comp ((measurable_hsHamiltonian χ).neg.div_const 2)).const_mul _)

theorem hsGroundStateMultiplier_sq (x : HsConfiguration N) :
    hsGroundStateMultiplier χ x ^ 2 =
      (hsPartitionFunction χ).toReal⁻¹ * Real.exp (-hsHamiltonian χ x) := by
  unfold hsGroundStateMultiplier
  rw [mul_pow, inv_pow, Real.sq_sqrt ENNReal.toReal_nonneg, ← Real.exp_nat_mul]
  congr 2
  ring

/-- The actual Gibbs law is the square of the ground-state multiplier times volume. -/
theorem hsQuotientGibbsProbability_eq_groundStateDensity :
    (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) =
      (hsConfigurationVolume N).withDensity
        (fun x => ENNReal.ofReal (hsGroundStateMultiplier χ x ^ 2)) := by
  have hZ0 := (hsPartitionFunction_pos χ).ne'
  have hZt := (hsPartitionFunction_lt_top χ hc).ne
  have hd : Measurable (fun x => ENNReal.ofReal (Real.exp (-hsHamiltonian χ x))) := by
    exact (Real.measurable_exp.comp (measurable_hsHamiltonian χ).neg).ennreal_ofReal
  change (hsPartitionFunction χ)⁻¹ • hsGibbsWeight χ = _
  rw [hsGibbsWeight, ← withDensity_smul _ hd]
  apply withDensity_congr_ae
  apply Eventually.of_forall
  intro x
  change (hsPartitionFunction χ)⁻¹ * ENNReal.ofReal (Real.exp (-hsHamiltonian χ x)) =
    ENNReal.ofReal (hsGroundStateMultiplier χ x ^ 2)
  rw [hsGroundStateMultiplier_sq χ x,
    ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg),
    ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hZ0 hZt), ENNReal.ofReal_toReal hZt]

/-- The ground-state transform on the whole weighted space. -/
def hsGroundStateEquiv {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    Lp F 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) ≃ₗᵢ[ℝ]
      Lp F 2 (hsConfigurationVolume N) :=
  squareDensityL2Equiv (measurable_hsGroundStateMultiplier χ)
    (hsGroundStateMultiplier_pos χ hc) (hsQuotientGibbsProbability_eq_groundStateDensity χ hc)

/-- The map is multiplication by `Z⁻¹ᐟ² exp(-H/2)` on arbitrary representatives. -/
theorem hsGroundStateEquiv_coeFn {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : Lp F 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    (hsGroundStateEquiv χ hc f : HsConfiguration N → F) =ᵐ[hsConfigurationVolume N]
      fun x => hsGroundStateMultiplier χ x • f x :=
  squareDensityL2Equiv_coeFn (measurable_hsGroundStateMultiplier χ)
    (hsGroundStateMultiplier_pos χ hc) (hsQuotientGibbsProbability_eq_groundStateDensity χ hc) f

/-- Its inverse is multiplication by the reciprocal density square root. -/
theorem hsGroundStateEquiv_symm_coeFn {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : Lp F 2 (hsConfigurationVolume N)) :
    ((hsGroundStateEquiv χ hc).symm g : HsConfiguration N → F) =ᵐ[hsConfigurationVolume N]
      fun x => (hsGroundStateMultiplier χ x)⁻¹ • g x := by
  have he := hsGroundStateEquiv_coeFn χ hc ((hsGroundStateEquiv χ hc).symm g)
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  filter_upwards [he] with x hx
  rw [hx, inv_smul_smul₀ (hsGroundStateMultiplier_pos χ hc x).ne']

/-- The complex-linear unitary ground-state transform. -/
def hsGroundStateUnitary :
    Lp ℂ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (hsConfigurationVolume N) :=
  squareDensityL2ScalarEquiv ℂ (measurable_hsGroundStateMultiplier χ)
    (hsGroundStateMultiplier_pos χ hc) (hsQuotientGibbsProbability_eq_groundStateDensity χ hc)

/-- The complex-linear map has exactly the same positive real multiplier. -/
theorem hsGroundStateUnitary_coeFn
    (f : Lp ℂ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    (hsGroundStateUnitary χ hc f : HsConfiguration N → ℂ) =ᵐ[hsConfigurationVolume N]
      fun x => hsGroundStateMultiplier χ x • f x :=
  hsGroundStateEquiv_coeFn χ hc f

end Riesz1
