/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GroundState
public import Riesz1.HelfferSjostrand.GroundStateDifferential

/-!
# The conjugated scalar operator on test functions

`S₀ = U L₀ U⁻¹` on its entire transported
domain. The domain is a preimage under the unitary. The
definition has no extension or default value outside that domain.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Laplacian

namespace Riesz1

variable {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)

local instance : IsFiniteMeasure (hsConfigurationVolume N) :=
  ⟨by rw [hsConfigurationVolume_univ]; finiteness⟩

/-- The operator on test functions conjugated by the actual ground-state isometry. -/
def hsGroundStateOperator :
    Lp ℝ 2 (hsConfigurationVolume N) →ₗ.[ℝ] Lp ℝ 2 (hsConfigurationVolume N) :=
  let U := hsGroundStateEquiv χ hc (F := ℝ)
  let T := hsTestL2Operator χ hc
  let D := T.domain.comap U.symm.toLinearMap
  { domain := D
    toFun := U.toLinearMap.comp (T.toFun.comp
      ((U.symm.toLinearMap.comp D.subtype).codRestrict T.domain (fun x => x.property))) }

/-- The conjugated domain is exactly the pullback of the original domain. -/
theorem mem_hsGroundStateOperator_domain (f : Lp ℝ 2 (hsConfigurationVolume N)) :
    f ∈ (hsGroundStateOperator χ hc).domain ↔
      (hsGroundStateEquiv χ hc (F := ℝ)).symm f ∈ (hsTestL2Operator χ hc).domain := Iff.rfl

/-- The definition applies the actual three maps `U`, `L₀`, `U⁻¹`. -/
theorem hsGroundStateOperator_apply (f : (hsGroundStateOperator χ hc).domain) :
    hsGroundStateOperator χ hc f = hsGroundStateEquiv χ hc
      (hsTestL2Operator χ hc
        ⟨(hsGroundStateEquiv χ hc (F := ℝ)).symm f.val, f.property⟩) := rfl

/-- Graph membership is exactly conjugation, with no restriction on the
ambient `L²` inputs and outputs. -/
theorem mem_hsGroundStateOperator_graph (f a : Lp ℝ 2 (hsConfigurationVolume N)) :
    (f, a) ∈ (hsGroundStateOperator χ hc).graph ↔
      ((hsGroundStateEquiv χ hc (F := ℝ)).symm f,
        (hsGroundStateEquiv χ hc (F := ℝ)).symm a) ∈ (hsTestL2Operator χ hc).graph := by
  simp only [LinearPMap.mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left]
  constructor
  · rintro ⟨hf, ha⟩
    refine ⟨hf, ?_⟩
    apply (hsGroundStateEquiv χ hc (F := ℝ)).injective
    exact ha.trans ((hsGroundStateEquiv χ hc (F := ℝ)).apply_symm_apply a).symm
  · rintro ⟨hf, ha⟩
    refine ⟨hf, ?_⟩
    change hsGroundStateEquiv χ hc
      (hsTestL2Operator χ hc ⟨(hsGroundStateEquiv χ hc (F := ℝ)).symm f, hf⟩) = a
    rw [ha, LinearIsometryEquiv.apply_symm_apply]

/-- Multiplication by the normalized ground state on an actual test function. -/
def hsGroundStateTest (hN : 2 ≤ (N : ℕ)) (f : HsTestFunction N) : HsTestFunction N :=
  (hsExponentialTest hN χ (-1 / 2) f).smul (Real.sqrt (hsPartitionFunction χ).toReal)⁻¹

/-- The normalized pointwise formula holds throughout the lifted chamber. -/
theorem hsGroundStateTest_apply (hN : 2 ≤ (N : ℕ)) (f : HsTestFunction N)
    (x : HsEuclidean N) :
    hsGroundStateTest χ hN f x = (Real.sqrt (hsPartitionFunction χ).toReal)⁻¹ *
      Real.exp (-hsPairExpression χ x / 2) * f x := by
  change (Real.sqrt (hsPartitionFunction χ).toReal)⁻¹ *
    (f x * Real.exp ((-1 / 2) * hsPairExpression χ x)) = _
  have he : (-1 / 2) * hsPairExpression χ x = -hsPairExpression χ x / 2 := by ring
  rw [he]
  ring

/-- The unitary's action on test functions agrees with the actual smooth
normalized ground-state test, as a class in unweighted `L²`. -/
theorem hsGroundStateEquiv_on_test (hN : 2 ≤ (N : ℕ)) (f : HsTestFunction N) :
    hsGroundStateEquiv χ hc
      (hsSobolevValue _ (hsSobolevOfSmooth _ ⟨f.toFun, f.smoothOnClosure⟩)) =
      hsSobolevValue (hsConfigurationVolume N)
        (hsSobolevOfSmooth (hsConfigurationVolume N)
          ⟨(hsGroundStateTest χ hN f).toFun, (hsGroundStateTest χ hN f).smoothOnClosure⟩) := by
  let ν := (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
  let v := hsSobolevValue ν (hsSobolevOfSmooth ν ⟨f.toFun, f.smoothOnClosure⟩)
  have hac : hsConfigurationVolume N ≪ ν :=
    Internal.squareDensity_ac (measurable_hsGroundStateMultiplier χ)
      (hsGroundStateMultiplier_pos χ hc) (hsQuotientGibbsProbability_eq_groundStateDensity χ hc)
  apply Lp.ext
  filter_upwards [hsGroundStateEquiv_coeFn χ hc v,
    hac.ae_le (f.smoothOnClosure.memLp_value ν).coeFn_toLp,
    ((hsGroundStateTest χ hN f).smoothOnClosure.memLp_value
      (hsConfigurationVolume N)).coeFn_toLp] with x hU hv hg
  change (v : HsConfiguration N → ℝ) x = hsSmoothValue f.toFun x at hv
  change (hsSobolevValue (hsConfigurationVolume N)
    (hsSobolevOfSmooth (hsConfigurationVolume N)
      ⟨(hsGroundStateTest χ hN f).toFun, (hsGroundStateTest χ hN f).smoothOnClosure⟩) :
        HsConfiguration N → ℝ) x = hsSmoothValue (hsGroundStateTest χ hN f).toFun x at hg
  rw [hU, hv, hg]
  change hsGroundStateMultiplier χ x * f (hsLiftPoint N x) =
    hsGroundStateTest χ hN f (hsLiftPoint N x)
  rw [hsGroundStateTest_apply]
  rfl

/-- Multiplication by the inverse normalized ground state also preserves
the entire test class. -/
def hsInverseGroundStateTest (hN : 2 ≤ (N : ℕ)) (f : HsTestFunction N) : HsTestFunction N :=
  (hsExponentialTest hN χ (1 / 2) f).smul (Real.sqrt (hsPartitionFunction χ).toReal)

include hc in
/-- The two normalized test transformations are actual inverses. -/
theorem hsGroundStateTest_inverse (hN : 2 ≤ (N : ℕ)) (f : HsTestFunction N) :
    hsGroundStateTest χ hN (hsInverseGroundStateTest χ hN f) = f := by
  have hZ : Real.sqrt (hsPartitionFunction χ).toReal ≠ 0 :=
    (Real.sqrt_pos.mpr (ENNReal.toReal_pos (hsPartitionFunction_pos χ).ne'
      (hsPartitionFunction_lt_top χ hc).ne)).ne'
  apply HsTestFunction.ext
  funext x
  rw [show (hsGroundStateTest χ hN (hsInverseGroundStateTest χ hN f)).toFun x =
    (Real.sqrt (hsPartitionFunction χ).toReal)⁻¹ * Real.exp (-hsPairExpression χ x / 2) *
      hsInverseGroundStateTest χ hN f x from hsGroundStateTest_apply χ hN _ x]
  change (Real.sqrt (hsPartitionFunction χ).toReal)⁻¹ * Real.exp (-hsPairExpression χ x / 2) *
    (Real.sqrt (hsPartitionFunction χ).toReal * (f x * Real.exp ((1 / 2) * hsPairExpression χ x))) = _
  calc
    _ = ((Real.sqrt (hsPartitionFunction χ).toReal)⁻¹ * Real.sqrt (hsPartitionFunction χ).toReal) *
        (Real.exp (-hsPairExpression χ x / 2) * Real.exp ((1 / 2) * hsPairExpression χ x)) * f x := by ring
    _ = f x := by
      rw [inv_mul_cancel₀ hZ, ← Real.exp_add]
      have he : -hsPairExpression χ x / 2 + (1 / 2) * hsPairExpression χ x = 0 := by ring
      rw [he, Real.exp_zero, one_mul, one_mul]

/-- The transported domain of `S₀` is precisely the same smooth
collision-free test class in unweighted `L²`. -/
theorem hsGroundStateOperator_domain (hN : 2 ≤ (N : ℕ)) :
    (hsGroundStateOperator χ hc).domain = hsTestL2Domain (hsConfigurationVolume N) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨f, hf⟩ := (mem_hsTestL2Domain _ _).mp
      (show (hsGroundStateEquiv χ hc (F := ℝ)).symm v ∈ hsTestL2Domain _ from
        hsTestL2Operator_domain hN χ hc ▸ hv)
    apply (mem_hsTestL2Domain _ _).mpr
    refine ⟨hsGroundStateTest χ hN f, ?_⟩
    rw [← hsGroundStateEquiv_on_test χ hc hN f, hf, LinearIsometryEquiv.apply_symm_apply]
  · intro v hv
    obtain ⟨f, rfl⟩ := (mem_hsTestL2Domain _ v).mp hv
    rw [mem_hsGroundStateOperator_domain, hsTestL2Operator_domain hN χ hc]
    apply (mem_hsTestL2Domain _ _).mpr
    refine ⟨hsInverseGroundStateTest χ hN f, ?_⟩
    apply (hsGroundStateEquiv χ hc (F := ℝ)).injective
    rw [hsGroundStateEquiv_on_test χ hc hN, hsGroundStateTest_inverse χ hc hN,
      LinearIsometryEquiv.apply_symm_apply]

/-- The normalized transformed test function satisfies the Schrödinger
product identity at every interior point. -/
theorem hsGroundStateTest_schrodinger (hN : 2 ≤ (N : ℕ)) (f : HsTestFunction N)
    {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    -Δ (hsGroundStateTest χ hN f).toFun x +
        hsGroundStatePotential χ x * hsGroundStateTest χ hN f x =
      (Real.sqrt (hsPartitionFunction χ).toReal)⁻¹ * Real.exp (-hsPairExpression χ x / 2) *
        (inner ℝ (gradient (hsPairExpression χ) x) (gradient f.toFun x) - Δ f.toFun x) := by
  let a := (Real.sqrt (hsPartitionFunction χ).toReal)⁻¹
  let g := fun z => Real.exp (-hsPairExpression χ z / 2) * f z
  have he : (hsGroundStateTest χ hN f).toFun = a • g := by
    funext z
    simpa only [a, g, Pi.smul_apply, smul_eq_mul, mul_assoc] using
      hsGroundStateTest_apply χ hN f z
  have hg : ContDiffAt ℝ 2 g x := by
    apply ContDiffAt.of_le
      (((((hsPairExpression_contDiffOn χ).neg.div_const 2).exp.mul
        f.smooth.contDiffOn).contDiffAt ((isOpen_hsChamber N).mem_nhds hx)))
    norm_num
  rw [he, InnerProductSpace.laplacian_smul a hg]
  have hp := hsGroundState_differential χ f.smooth.contDiffOn hx
  change -(a * Δ g x) + hsGroundStatePotential χ x * (a * g x) = _
  calc
    _ = a * (-Δ g x + hsGroundStatePotential χ x * g x) := by ring
    _ = _ := by rw [hp]; ring

end Riesz1
