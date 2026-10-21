/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopMasterTransport
import all Mathlib.Basic.Complex.Basic
import all Mathlib.Basic.Real.Basic

/-!
# Pulling Fourier coefficients back to the unit circle

The change of variables behind the transport scaling in
Proposition 5.5.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ContDiff Real

namespace Riesz1

/-- Pullback along the dilation from the unit circle to the circle of length `L`. -/
noncomputable def loopMasterPullback (L : Length) (f : Circle L → ℝ) : UnitAddCircle → ℝ :=
  fun z => f (AddCircle.equivAddCircle 1 L.val one_ne_zero L.property.ne' z)

lemma loopMasterPullback_coe (L : Length) (f : Circle L → ℝ) (x : ℝ) :
    loopMasterPullback L f (x : UnitAddCircle) = f ((x * L.val : ℝ) : Circle L) := by
  simp only [loopMasterPullback, AddCircle.equivAddCircle_apply_mk, inv_one, one_mul]

lemma loopMasterPullback_smooth (L : Length) (f : Circle L → ℝ)
    (hf : ContDiff ℝ ∞ (fun u : ℝ => f (u : Circle L))) :
    IsSmoothCircle (loopMasterPullback L f) := by
  unfold IsSmoothCircle
  simp_rw [loopMasterPullback_coe]
  exact hf.comp (contDiff_id.mul contDiff_const)

/-- A smooth real function on the circle of length `L` is on the `L²` carrier. -/
@[reducible] noncomputable def loopMasterLengthTest (L : Length) (f : Circle L → ℝ)
    (hf : ContDiff ℝ ∞ (fun u : ℝ => f (u : Circle L))) :
    {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)} := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  haveI : IsFiniteMeasure (arclength L) := by unfold arclength; infer_instance
  have hc : Continuous f :=
    (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 hf.continuous
  refine ⟨f, ?_⟩
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine MemLp.of_bound (Complex.continuous_ofReal.comp hc).aestronglyMeasurable C ?_
  exact Eventually.of_forall fun z => by
    rw [Complex.norm_real]
    exact hC z (mem_univ _)

/-- Normalized Fourier coefficients are unchanged by pullback to the unit circle. -/
theorem loopMaster_coeff_pullback (L : Length)
    (f : {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)}) (k : ℤ) :
    circleCoeff (loopMasterPullback L f.val) k =
      coeff L ⟨(fun z => (f.val z : ℂ)), complexL2Integrable L _ f.property⟩ k := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  unfold coeff
  rw [fourierCoeff_eq_intervalIntegral _ k 0, circleCoeff_eq_intervalIntegral]
  simp only [zero_add, smul_eq_mul, fourier_coe_apply, loopMasterPullback_coe]
  let G : ℝ → ℂ := fun u => Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) * u / L.val) *
    (f.val (u : Circle L) : ℂ)
  have hi := intervalIntegral.integral_comp_mul_right (a := (0 : ℝ)) (b := 1) G L.property.ne'
  simp only [zero_mul, one_mul] at hi
  have he (u : ℝ) : Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) * u) *
      (f.val ((u * L.val : ℝ) : Circle L) : ℂ) = G (u * L.val) := by
    dsimp only [G]
    congr 2
    push_cast
    field_simp [Complex.ofReal_ne_zero.2 L.property.ne']
  simp_rw [he]
  rw [hi]
  simp only [one_div]
  rfl

/-- The rescaled unit-circle transport `L⁻ˢ ψ(L·)`. -/
noncomputable def loopMasterTransportPullback (P : Parameters) (L : Length)
    (ψ : Circle L → ℝ) : UnitAddCircle → ℝ :=
  fun z => L.val ^ (-P.val.2) * loopMasterPullback L ψ z

/-- Scaling of the transport multiplier itself, including its zero mode. -/
theorem loopMaster_transportCoeffs_pullback (P : Parameters) (L : Length)
    (ξ : Circle L → ℝ)
    (hξ : ContDiff ℝ ∞ (fun u : ℝ => ξ (u : Circle L))) (k : ℤ) :
    ((L.val ^ (-P.val.2) : ℝ) : ℂ) * transportCoeffs P L (loopMasterLengthTest L ξ hξ) k =
      transportCoeffs P unitLength
        (loopMasterTest (loopMasterPullback L ξ) (loopMasterPullback_smooth L ξ hξ)) k := by
  unfold transportCoeffs
  by_cases hk : k = 0
  · subst k
    simp
  · rw [ite_eq_right hk, ite_eq_right hk]
    change ((L.val ^ (-P.val.2) : ℝ) : ℂ) *
      (-((|2 * π * (k : ℝ) / L.val| ^ (1 - P.val.2) : ℝ) : ℂ) /
        ((2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) *
          (2 * π * I * (k : ℂ) / L.val)) *
        coeff L ⟨(fun z => (ξ z : ℂ)), _⟩ k) =
      -((|2 * π * (k : ℝ) / 1| ^ (1 - P.val.2) : ℝ) : ℂ) /
        ((2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) *
          (2 * π * I * (k : ℂ) / 1)) * circleCoeff (loopMasterPullback L ξ) k
    rw [loopMaster_coeff_pullback L (loopMasterLengthTest L ξ hξ)]
    rw [div_one, div_one, abs_div, abs_of_pos L.property,
      Real.div_rpow (abs_nonneg _) L.property.le]
    have he : L.val ^ (1 - P.val.2) = L.val * L.val ^ (-P.val.2) := by
      rw [show 1 - P.val.2 = 1 + -P.val.2 by ring, Real.rpow_add L.property, Real.rpow_one]
    rw [he]
    push_cast
    have hL : (L.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 L.property.ne'
    have hp : ((L.val ^ (-P.val.2) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos L.property _).ne'
    field_simp


/-- The rescaled transport has the unit-circle transport coefficients. -/
theorem loopMaster_transport_pullback (P : Parameters) (L : Length)
    (ξ ψ : Circle L → ℝ)
    (hξ : ContDiff ℝ ∞ (fun u : ℝ => ξ (u : Circle L)))
    (hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle L)))
    (htransport : ∀ k, coeff L
      ⟨(fun z => (ψ z : ℂ)), complexL2Integrable L _ (loopMasterLengthTest L ψ hψ).property⟩ k =
      transportCoeffs P L (loopMasterLengthTest L ξ hξ) k) (k : ℤ) :
    circleCoeff (loopMasterTransportPullback P L ψ) k =
      transportCoeffs P unitLength
        (loopMasterTest (loopMasterPullback L ξ) (loopMasterPullback_smooth L ξ hξ)) k := by
  have hc : circleCoeff (loopMasterTransportPullback P L ψ) k =
      ((L.val ^ (-P.val.2) : ℝ) : ℂ) * circleCoeff (loopMasterPullback L ψ) k := by
    unfold circleCoeff loopMasterTransportPullback
    simp only [Complex.ofReal_mul]
    exact fourierCoeff.const_mul _ _ _
  rw [hc, loopMaster_coeff_pullback L (loopMasterLengthTest L ψ hψ), htransport]
  exact loopMaster_transportCoeffs_pullback P L ξ hξ k

end Riesz1

end
