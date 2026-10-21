/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.NonGradientSpace
public import Riesz1.ToMathlib.Variational.NormalizedInverse

/-!
# The inverse on compatible vector fields

This file proves the existence and uniqueness assertions of
Proposition 3.2. The inverse uses the coercive restriction of the
vector form. Its equation is proved for every vector test, including
tests outside the normalized subspace.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

local instance (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    InnerProductSpace ℝ (HsSobolev μ) := inferInstance
local instance (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    NormedSpace ℝ (HsSobolev μ) := inferInstance
local instance (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    InnerProductSpace ℝ (PiLp 2 (fun _ : Fin (N : ℕ) => HsSobolev μ)) := inferInstance
local instance (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    InnerProductSpace ℝ (HsVectorJet μ) := inferInstance
local instance (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    NormedSpace ℝ (HsVectorJet μ) := inferInstance

local instance (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    InnerProductSpace ℝ (HsVectorSobolev χ hN hc μ) := inferInstance
local instance (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    NormedSpace ℝ (HsVectorSobolev χ hN hc μ) := inferInstance

/-- The ordinary vector `L²` pairing, written in scalar components. -/
def hsNonGradientPairing (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]
    (v : Lp (HsEuclidean N) 2 μ) (u : HsVectorJet μ) : ℝ :=
  inner ℝ (hsL2Coordinates μ v) (hsNonGradientValues μ u)

theorem hsNonGradientPairing_eq_integral (μ : Measure (HsConfiguration N))
    [IsFiniteMeasure μ] (v : Lp (HsEuclidean N) 2 μ) (u : HsVectorJet μ) :
    hsNonGradientPairing μ v u =
      ∫ x, ∑ i : Fin (N : ℕ), v x i * hsJetValue μ i u x ∂μ := by
  rw [hsNonGradientPairing, PiLp.inner_apply]
  change (∑ i : Fin (N : ℕ), inner ℝ
    ((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ v) (hsJetValue μ i u)) = _
  simp_rw [L2.inner_def]
  rw [← integral_finsetSum _ (fun i _ => L2.integrable_inner _ _)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun i : Fin (N : ℕ) =>
    ContinuousLinearMap.coeFn_compLpL (EuclideanSpace.proj (𝕜 := ℝ) i) v)] with x hx
  exact Finset.sum_congr rfl fun i _ => by
    rw [hx i]
    exact mul_comm _ _

theorem hsL2Mean_eq_integral (μ : Measure (HsConfiguration N)) [IsProbabilityMeasure μ]
    (v : Lp (HsEuclidean N) 2 μ) :
    hsL2Mean μ v = ∫ x, ∑ i : Fin (N : ℕ), v x i ∂μ := by
  simp only [hsL2Mean, sum_apply, ContinuousLinearMap.comp_apply]
  simp_rw [poissonMean_eq_integral]
  rw [← integral_finsetSum _ (fun i _ => (Lp.memLp _).integrable one_le_two)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun i : Fin (N : ℕ) =>
    ContinuousLinearMap.coeFn_compLpL (EuclideanSpace.proj (𝕜 := ℝ) i) v)] with x hx
  exact Finset.sum_congr rfl fun i _ => hx i

/-- The expected rotation component equals the expected sum divided by `√N`. -/
theorem hsL2_rotation_mean (μ : Measure (HsConfiguration N)) [IsProbabilityMeasure μ]
    (v : Lp (HsEuclidean N) 2 μ) :
    (∫ x, ∑ i : Fin (N : ℕ), v x i * hsUnitVector N i ∂μ) =
      (Real.sqrt (N : ℕ))⁻¹ * hsL2Mean μ v := by
  rw [hsL2Mean_eq_integral, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [hsUnitVector, hsRotationVector, PiLp.smul_apply, smul_eq_mul, mul_one]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The carrier is exactly `L²₀` with the rotation normalization. -/
theorem hsMeanZeroL2_iff_rotation_mean_zero (μ : Measure (HsConfiguration N)) [IsProbabilityMeasure μ]
    (v : Lp (HsEuclidean N) 2 μ) :
    v ∈ hsMeanZeroL2 μ ↔ (∫ x, ∑ i : Fin (N : ℕ), v x i * hsUnitVector N i ∂μ) = 0 := by
  rw [hsL2_rotation_mean]
  change hsL2Mean μ v = 0 ↔ (Real.sqrt (N : ℕ))⁻¹ * hsL2Mean μ v = 0
  constructor
  · intro h
    exact (congrArg ((Real.sqrt (N : ℕ))⁻¹ * ·) h).trans (mul_zero _)
  · intro h
    exact (mul_eq_zero.mp h).resolve_left
      (inv_ne_zero (Real.sqrt_pos.mpr (Nat.cast_pos.mpr N.pos)).ne')

variable (hPL : External.PrekopaLeindler) (χ : HsPairPotentials N c)
  (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)

local notation "ν" => (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))

local instance : NormedAddCommGroup (HsSobolev ν) := inferInstance
local instance : InnerProductSpace ℝ (HsSobolev ν) := inferInstance
local instance : NormedSpace ℝ (HsSobolev ν) := inferInstance
local instance : NormedAddCommGroup (HsVectorJet ν) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorJet ν) := inferInstance
local instance : NormedSpace ℝ (HsVectorJet ν) := inferInstance
local instance : NormedAddCommGroup (HsVectorSobolev χ hN hc ν) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorSobolev χ hN hc ν) := inferInstance
local instance : NormedSpace ℝ (HsVectorSobolev χ hN hc ν) := inferInstance

/-- The forcing functional, on every test in the existing vector completion. -/
def hsNonGradientForcing (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    Lp (HsEuclidean N) 2 μ →L[ℝ] StrongDual ℝ (HsVectorSobolev χ hN hc μ) := by
  let P := (hsNonGradientValues μ).comp (hsVectorSobolevSubmodule χ hN hc μ).subtypeL
  exact ((ContinuousLinearMap.compL ℝ (HsVectorSobolev χ hN hc μ)
    (PiLp 2 (fun _ : Fin (N : ℕ) => Lp ℝ 2 μ)) ℝ).flip P).comp
      ((innerSL ℝ (E := PiLp 2 (fun _ : Fin (N : ℕ) => Lp ℝ 2 μ))).comp (hsL2Coordinates μ))

theorem hsNonGradientForcing_apply (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]
    (v : Lp (HsEuclidean N) 2 μ) (w : HsVectorSobolev χ hN hc μ) :
    hsNonGradientForcing χ hN hc μ v w = hsNonGradientPairing μ v w.val := rfl

/-- The norm estimate for the bundled form. -/
theorem hsNonGradient_bilinear_bound (hPL : External.PrekopaLeindler)
    (u : HsVectorSobolev χ hN hc ν) (hu : hsNonGradientMean χ hN hc ν u = 0) :
    ‖u‖ ^ 2 ≤ (1 + hsPoincareConstant N c) * hsNonGradientFullBilinear χ hN hc ν u u :=
  (hsNonGradient_norm_bound χ hN hc hPL u hu).trans_eq
    (congrArg ((1 + hsPoincareConstant N c) * ·) (hsNonGradientFullBilinear_eq χ hN hc ν u u).symm)

/-- Riesz inversion before supplying the forcing functional. -/
def hsNonGradientInverseCore : StrongDual ℝ (HsVectorSobolev χ hN hc ν) →ₗ[ℝ]
    hsMeanZeroVector χ hN hc ν :=
  Internal.normalizedVariationalInverse (hsNonGradientMean χ hN hc ν)
    (hsNonGradientFullBilinear χ hN hc ν) (1 + hsPoincareConstant N c)
    (by linarith [hsPoincareConstant_pos N c]) (hsNonGradient_bilinear_bound χ hN hc hPL)

theorem hsNonGradientInverseCore_solves (f : StrongDual ℝ (HsVectorSobolev χ hN hc ν))
    (w : hsMeanZeroVector χ hN hc ν) :
    hsNonGradientFullBilinear χ hN hc ν (hsNonGradientInverseCore hPL χ hN hc f).val w.val = f w.val :=
  Internal.normalizedVariationalInverse_solves (hsNonGradientMean χ hN hc ν)
    (hsNonGradientFullBilinear χ hN hc ν) (1 + hsPoincareConstant N c)
    (by linarith [hsPoincareConstant_pos N c]) (hsNonGradient_bilinear_bound χ hN hc hPL) f w

/-- The inverse `T`, on its whole compatible carrier. -/
def hsInverse : hsMeanZeroL2 ν →ₗ[ℝ] hsMeanZeroVector χ hN hc ν :=
  (hsNonGradientInverseCore hPL χ hN hc).comp
    ((hsNonGradientForcing χ hN hc ν).toLinearMap.comp (hsMeanZeroL2 ν).subtype)

theorem hsInverse_normalized_solves (v : hsMeanZeroL2 ν) (w : hsMeanZeroVector χ hN hc ν) :
    hsVectorSobolevForm χ hN hc ν (hsInverse hPL χ hN hc v).val w.val =
      hsNonGradientPairing ν v.val w.val.val := by
  calc
    _ = hsNonGradientFullBilinear χ hN hc ν
        (hsNonGradientInverseCore hPL χ hN hc (hsNonGradientForcing χ hN hc ν v.val)).val w.val :=
      (hsNonGradientFullBilinear_eq χ hN hc ν _ _).symm
    _ = hsNonGradientForcing χ hN hc ν v.val w.val :=
      hsNonGradientInverseCore_solves hPL χ hN hc _ w
    _ = _ := hsNonGradientForcing_apply χ hN hc ν v.val w.val

/-- Uniqueness follows already from normalized tests. -/
theorem hsInverse_unique
    (v : hsMeanZeroL2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (u : hsMeanZeroVector χ hN hc (hsQuotientGibbsProbability χ hc : Measure _))
    (hu : ∀ w : hsMeanZeroVector χ hN hc (hsQuotientGibbsProbability χ hc : Measure _),
      hsVectorSobolevForm χ hN hc _ u.val w.val = hsNonGradientPairing ν v.val w.val.val) :
    u = hsInverse hPL χ hN hc v := by
  apply Internal.normalizedVariationalInverse_unique
    (hsNonGradientMean χ hN hc ν) (hsNonGradientFullBilinear χ hN hc ν)
    (1 + hsPoincareConstant N c) (by linarith [hsPoincareConstant_pos N c])
    (fun u hu => (hsNonGradient_norm_bound χ hN hc hPL u hu).trans_eq
      (congrArg ((1 + hsPoincareConstant N c) * ·)
        (hsNonGradientFullBilinear_eq χ hN hc ν u u).symm)) (hsNonGradientForcing χ hN hc ν v.val) u
  intro w
  exact (hsNonGradientFullBilinear_eq χ hN hc ν _ _).trans (hu w)

variable {C_N : ℝ} (hadm : HsAdmissible χ C_N)

/-- Subtracting the mean rotation component normalizes every vector test. -/
def hsNonGradientNormalize
    (w : HsVectorSobolev χ hN hc (hsQuotientGibbsProbability χ hc : Measure _)) :
    hsMeanZeroVector χ hN hc (hsQuotientGibbsProbability χ hc : Measure _) :=
  ⟨w - hsRotationField χ hc hadm
    ((hsVectorMean _ w.val / Real.sqrt (N : ℕ)) • hsPoissonUnit _), by
    change hsVectorMean _ (w - hsRotationField χ hc hadm
      ((hsVectorMean _ w.val / Real.sqrt (N : ℕ)) • hsPoissonUnit _)).val = 0
    rw [hsVectorMean_sub_rotationUnit χ hc hadm]
    rw [div_mul_cancel₀ _ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr N.pos)).ne', sub_self]⟩

/-- Constant rotation fields are annihilated in either slot of the form. -/
theorem hsNonGradient_form_rotationUnit
    (w : HsVectorSobolev χ hN hc (hsQuotientGibbsProbability χ hc : Measure _)) (a : ℝ) :
    hsVectorSobolevForm χ hN hc _ w (hsRotationField χ hc hadm (a • hsPoissonUnit _)) = 0 := by
  change (∑ i : Fin (N : ℕ), inner ℝ (hsSobolevGradient _ (w.val.ofLp.1 i))
    (hsSobolevGradient _ (hsUnitVector N i • (a • hsPoissonUnit _)))) + inner ℝ _ 0 = 0
  simp only [map_smul, hsPoissonUnit_gradient, smul_zero, inner_zero_right,
    Finset.sum_const_zero, add_zero]

/-- The compatibility condition is exactly orthogonality to the constant rotation field. -/
theorem hsNonGradient_pairing_rotationUnit
    (v : Lp (HsEuclidean N) 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (a : ℝ) :
    hsNonGradientPairing _ v (hsRotationField χ hc hadm (a • hsPoissonUnit _)).val =
      (a / Real.sqrt (N : ℕ)) * hsL2Mean _ v := by
  rw [hsNonGradientPairing, PiLp.inner_apply]
  change (∑ i : Fin (N : ℕ), inner ℝ
    ((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 _ v)
    (hsJetValue _ i (hsRotationField χ hc hadm (a • hsPoissonUnit _)).val)) = _
  simp_rw [hsRotationField_value, map_smul, hsPoissonUnit_value,
    real_inner_smul_right, ← real_inner_comm _ (Lp.const 2 _ (1 : ℝ))]
  change (∑ i : Fin (N : ℕ), hsUnitVector N i * (a * poissonMean _
    ((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 _ v))) = _
  simp only [hsUnitVector, hsRotationVector, PiLp.smul_apply, smul_eq_mul, mul_one]
  simp_rw [← mul_assoc]
  rw [← Finset.mul_sum]
  simp only [hsL2Mean, sum_apply, ContinuousLinearMap.comp_apply]
  ring

/-- The actual full weak equation. -/
def HsNonGradientSolves
    (v : Lp (HsEuclidean N) 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (u : HsVectorSobolev χ hN hc (hsQuotientGibbsProbability χ hc : Measure _)) : Prop :=
  ∀ w : HsVectorSobolev χ hN hc (hsQuotientGibbsProbability χ hc : Measure _),
    hsVectorSobolevForm χ hN hc _ u w = hsNonGradientPairing _ v w.val

theorem hsNonGradient_form_normalize
    (u w : HsVectorSobolev χ hN hc ν) :
    hsVectorSobolevForm χ hN hc ν u (hsNonGradientNormalize χ hN hc hadm w).val =
      hsVectorSobolevForm χ hN hc ν u w := by
  let r := hsRotationField χ hc hadm
    ((hsVectorMean ν w.val / Real.sqrt (N : ℕ)) • hsPoissonUnit ν)
  calc
    _ = hsNonGradientFullBilinear χ hN hc ν u (w - r) :=
      (hsNonGradientFullBilinear_eq χ hN hc ν u (w - r)).symm
    _ = hsNonGradientFullBilinear χ hN hc ν u w - hsNonGradientFullBilinear χ hN hc ν u r :=
      (hsNonGradientFullBilinear χ hN hc ν u).map_sub w r
    _ = hsVectorSobolevForm χ hN hc ν u w :=
      (congrArg₂ (· - ·) (hsNonGradientFullBilinear_eq χ hN hc ν u w)
        (hsNonGradientFullBilinear_eq χ hN hc ν u r)).trans
          (sub_eq_self.mpr (hsNonGradient_form_rotationUnit χ hN hc hadm u _))

theorem hsNonGradient_pairing_normalize (v : hsMeanZeroL2 ν)
    (w : HsVectorSobolev χ hN hc ν) :
    hsNonGradientPairing ν v.val (hsNonGradientNormalize χ hN hc hadm w).val.val =
      hsNonGradientPairing ν v.val w.val := by
  change inner ℝ (hsL2Coordinates ν v.val) (hsNonGradientValues ν (w.val - _)) = _
  rw [map_sub, inner_sub_right]
  change hsNonGradientPairing ν v.val w.val - hsNonGradientPairing ν v.val
    (hsRotationField χ hc hadm
      ((hsVectorMean ν w.val / Real.sqrt (N : ℕ)) • hsPoissonUnit ν)).val = _
  apply sub_eq_self.mpr
  exact (hsNonGradient_pairing_rotationUnit χ hc hadm v.val
    (hsVectorMean ν w.val / Real.sqrt (N : ℕ))).trans
      ((congrArg ((hsVectorMean ν w.val / Real.sqrt (N : ℕ) / Real.sqrt (N : ℕ)) * ·)
        (show hsL2Mean ν v.val = 0 from v.property)).trans (mul_zero _))

/-- The normalized inverse solves the equation against every vector test. -/
theorem hsInverse_solves (hadm : HsAdmissible χ C_N) (v : hsMeanZeroL2 ν) :
    HsNonGradientSolves χ hN hc v.val (hsInverse hPL χ hN hc v).val := by
  intro w
  exact (hsNonGradient_form_normalize χ hN hc hadm _ w).symm.trans
    ((hsInverse_normalized_solves hPL χ hN hc v (hsNonGradientNormalize χ hN hc hadm w)).trans
      (hsNonGradient_pairing_normalize χ hN hc hadm v w))

/-- Existence and uniqueness for the full equation on `𝒱_{μ,0}`. -/
theorem hs_non_gradient_existsUnique (hPL : External.PrekopaLeindler) (hadm : HsAdmissible χ C_N)
    (v : hsMeanZeroL2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    ∃! u : hsMeanZeroVector χ hN hc (hsQuotientGibbsProbability χ hc : Measure _),
      HsNonGradientSolves χ hN hc v.val u.val := by
  refine ⟨hsInverse hPL χ hN hc v, hsInverse_solves hPL χ hN hc hadm v, ?_⟩
  intro u hu
  exact hsInverse_unique hPL χ hN hc v u (fun w => hu w.val)

end Riesz1
