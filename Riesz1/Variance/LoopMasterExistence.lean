/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopMasterTransport
public import Riesz1.Variance.LoopMasterScaling
public import Riesz1.Kernel.TransportSeries
public import Riesz1.Kernel.MeanFieldEnergyAlgebra
import all Mathlib.Basic.Complex.Basic
import all Mathlib.Basic.Real.Basic

/-!
# Smooth representatives of the transport

Existence from the rapidly decreasing Fourier coefficients of a smooth test,
with no convolution equation or regularity certificate assumed for the transport.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ContDiff Real ComplexConjugate

namespace Riesz1

lemma loopMaster_rieszConstant_pos (P : Parameters) :
    0 < rieszConstant (parametersExponent P) := by
  unfold rieszConstant
  exact div_pos (mul_pos (mul_pos (by positivity) (Real.sqrt_pos.2 Real.pi_pos))
    (Real.Gamma_pos_of_pos (by linarith [(parametersExponent P).property.2])))
    (Real.Gamma_pos_of_pos (by linarith [(parametersExponent P).property.1]))

/-- All polynomially weighted transport coefficient series converge. -/
lemma loopMaster_summable_transport (P : Parameters) (ξ : UnitAddCircle → ℝ)
    (hξ : IsSmoothCircle ξ) (m : ℕ) :
    Summable fun k : ℤ => |(k : ℝ)| ^ m *
      ‖transportCoeffs P unitLength (loopMasterTest ξ hξ) k‖ := by
  let A := 1 / (2 * P.val.1 * rieszConstant (parametersExponent P))
  have hA : 0 < A := by dsimp [A]; positivity [loopMaster_rieszConstant_pos P, P.property.1]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_norm_two_pi_pow_mul ξ hξ m).mul_left A)
  by_cases hk : k = 0
  · subst k
    simp [transportCoeffs]
    positivity
  · have hab : |2 * π * (k : ℝ)| = 2 * π * |(k : ℝ)| := by
      rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_two]
    have ha : 1 ≤ |2 * π * (k : ℝ)| := by
      have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
      rw [hab]
      nlinarith [Real.two_le_pi]
    have har : |2 * π * (k : ℝ)| ^ (1 - P.val.2) ≤ |2 * π * (k : ℝ)| := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le ha (show 1 - P.val.2 ≤ 1 by linarith [P.property.2.1])
    have hn : ‖transportCoeffs P unitLength (loopMasterTest ξ hξ) k‖ ≤ A * ‖circleCoeff ξ k‖ := by
      unfold transportCoeffs
      rw [ite_eq_right hk]
      simp only [unitLength, Complex.ofReal_one, div_one, coeff]
      change ‖-((|2 * π * (k : ℝ)| ^ (1 - P.val.2) : ℝ) : ℂ) /
        ((2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) * (2 * π * I * (k : ℂ))) *
        circleCoeff ξ k‖ ≤ _
      rw [norm_transport_term _ _ _ P.property.1 (loopMaster_rieszConstant_pos P) hk]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      dsimp [A]
      have hden : 0 < 2 * P.val.1 * rieszConstant (parametersExponent P) :=
        mul_pos (mul_pos two_pos P.property.1) (loopMaster_rieszConstant_pos P)
      calc |2 * π * (k : ℝ)| ^ (1 - P.val.2) /
          ((2 * P.val.1 * rieszConstant (parametersExponent P)) * |2 * π * (k : ℝ)|)
          ≤ |2 * π * (k : ℝ)| /
            ((2 * P.val.1 * rieszConstant (parametersExponent P)) * |2 * π * (k : ℝ)|) :=
            div_le_div_of_nonneg_right har (mul_pos hden (lt_of_lt_of_le zero_lt_one ha)).le
        _ = 1 / (2 * P.val.1 * rieszConstant (parametersExponent P)) := by
          field_simp
    have hkpow : |(k : ℝ)| ^ m ≤ |2 * π * (k : ℝ)| ^ m := by
      apply pow_le_pow_left₀ (abs_nonneg _)
      rw [hab]
      nlinarith [Real.two_le_pi, abs_nonneg (k : ℝ)]
    calc |(k : ℝ)| ^ m * ‖transportCoeffs P unitLength (loopMasterTest ξ hξ) k‖
        ≤ |2 * π * (k : ℝ)| ^ m * (A * ‖circleCoeff ξ k‖) :=
          mul_le_mul hkpow hn (norm_nonneg _) (pow_nonneg (abs_nonneg _) _)
      _ = A * (|2 * π * (k : ℝ)| ^ m * ‖circleCoeff ξ k‖) := by ring

lemma loopMaster_transport_conj (P : Parameters) (ξ : UnitAddCircle → ℝ)
    (hξ : IsSmoothCircle ξ) (k : ℤ) :
    conj (transportCoeffs P unitLength (loopMasterTest ξ hξ) k) =
      transportCoeffs P unitLength (loopMasterTest ξ hξ) (-k) := by
  have hc : conj (circleCoeff ξ k) = circleCoeff ξ (-k) := by
    simp only [circleCoeff, fourierCoeff, ← integral_conj, smul_eq_mul,
      map_mul, conj_ofReal, neg_neg, ← fourier_neg]
  unfold transportCoeffs
  by_cases hk : k = 0
  · subst k
    simp
  · rw [ite_eq_right hk, ite_eq_right (neg_ne_zero.mpr hk)]
    simp only [unitLength, Complex.ofReal_one, div_one, coeff]
    change conj (-((|2 * π * (k : ℝ)| ^ (1 - P.val.2) : ℝ) : ℂ) /
      ((2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) * (2 * π * I * (k : ℂ))) *
      circleCoeff ξ k) = _
    simp only [map_mul, map_div₀, map_neg, conj_ofReal, map_ofNat, conj_I,
      map_intCast, Int.cast_neg, mul_neg, abs_neg]
    rw [hc]
    unfold circleCoeff
    ring

/-- Every smooth real test has a smooth, real, mean-zero representative of its transport. -/
theorem loopMaster_exists_transport_unit (P : Parameters) (ξ : UnitAddCircle → ℝ)
    (hξ : IsSmoothCircle ξ) :
    ∃ ψ : UnitAddCircle → ℝ, IsSmoothCircle ψ ∧
      (∀ k, circleCoeff ψ k = transportCoeffs P unitLength (loopMasterTest ξ hξ) k) ∧
      (∫ u in (0 : ℝ)..1, ψ (u : UnitAddCircle)) = 0 := by
  let c := transportCoeffs P unitLength (loopMasterTest ξ hξ)
  let G : UnitAddCircle → ℂ := fun z => ∑' k : ℤ, c k * fourier k z
  have hG (z : UnitAddCircle) : (G z).im = 0 := by
    apply Complex.conj_eq_iff_im.mp
    dsimp only [G, c]
    rw [Complex.conj_tsum]
    simp_rw [map_mul, loopMaster_transport_conj, ← fourier_neg]
    exact (Equiv.neg ℤ).tsum_eq (fun k => c k * fourier k z)
  have hreal (z : UnitAddCircle) : ((G z).re : ℂ) = G z := by
    exact Complex.ext (by simp) (by simp [hG z])
  have hsm : IsSmoothCircle (fun z => (G z).re) :=
    Complex.reCLM.contDiff.comp (contDiff_fourierSeries (loopMaster_summable_transport P ξ hξ))
  have hc (k : ℤ) : circleCoeff (fun z => (G z).re) k = c k := by
    unfold circleCoeff
    simp_rw [hreal]
    exact fourierCoeff_fourierSeries (by simpa using loopMaster_summable_transport P ξ hξ 0) k
  refine ⟨fun z => (G z).re, hsm, hc, ?_⟩
  have hz := hc 0
  rw [circleCoeff_eq_intervalIntegral] at hz
  simp only [neg_zero, Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul] at hz
  change (∫ u in (0 : ℝ)..1, ((G (u : UnitAddCircle)).re : ℂ)) = 0 at hz
  rw [intervalIntegral.integral_ofReal] at hz
  exact_mod_cast hz

/-- Existence of a smooth real transport on every positive-length circle, with precisely
the coefficients `transportCoeffs`. -/
theorem loopMaster_exists_transport_length (P : Parameters) (L : Length)
    (ξ : Circle L → ℝ) (hξ : ContDiff ℝ ∞ (fun u : ℝ => ξ (u : Circle L))) :
    ∃ ψ : Circle L → ℝ, ∃ hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle L)),
      ∀ k, coeff L
        ⟨(fun z => (ψ z : ℂ)), complexL2Integrable L _ (loopMasterLengthTest L ψ hψ).property⟩ k =
        transportCoeffs P L (loopMasterLengthTest L ξ hξ) k := by
  obtain ⟨ψ1, hψ1, hc1, _⟩ := loopMaster_exists_transport_unit P (loopMasterPullback L ξ)
    (loopMasterPullback_smooth L ξ hξ)
  let e := AddCircle.equivAddCircle 1 L.val one_ne_zero L.property.ne'
  let ψ : Circle L → ℝ := fun z => L.val ^ P.val.2 * ψ1 (e.symm z)
  have he (u : ℝ) : ψ (u : Circle L) = L.val ^ P.val.2 * ψ1 ((u / L.val : ℝ) : UnitAddCircle) := by
    dsimp only [ψ, e]
    rw [AddCircle.equivAddCircle_symm_apply_mk]
    simp only [mul_one, div_eq_mul_inv]
  have hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle L)) := by
    simp_rw [he]
    exact contDiff_const.mul (hψ1.comp (contDiff_id.div_const L.val))
  refine ⟨ψ, hψ, fun k => ?_⟩
  have heq : loopMasterPullback L ψ = fun z => L.val ^ P.val.2 * ψ1 z := by
    funext z
    change L.val ^ P.val.2 * ψ1 (e.symm (e z)) = _
    rw [e.symm_apply_apply]
  have hcψ : coeff L
      ⟨(fun z => (ψ z : ℂ)), complexL2Integrable L _ (loopMasterLengthTest L ψ hψ).property⟩ k =
      ((L.val ^ P.val.2 : ℝ) : ℂ) * circleCoeff ψ1 k := by
    rw [← loopMaster_coeff_pullback L (loopMasterLengthTest L ψ hψ), heq]
    unfold circleCoeff
    simp only [Complex.ofReal_mul]
    exact fourierCoeff.const_mul _ _ _
  rw [hcψ, hc1]
  have hscale := loopMaster_transportCoeffs_pullback P L ξ hξ k
  rw [← hscale]
  have hp : L.val ^ P.val.2 * L.val ^ (-P.val.2) = 1 := by
    rw [← Real.rpow_add L.property, add_neg_cancel, Real.rpow_zero]
  rw [← mul_assoc, ← Complex.ofReal_mul, hp, Complex.ofReal_one, one_mul]

/-- The zero Fourier mode forces the long-circle transport to have zero integral. -/
lemma loopMaster_transport_mean_zero (P : Parameters) (L : Length)
    (ξ ψ : Circle L → ℝ)
    (hξ : ContDiff ℝ ∞ (fun u : ℝ => ξ (u : Circle L)))
    (hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle L)))
    (htransport : ∀ k, coeff L
      ⟨(fun z => (ψ z : ℂ)), complexL2Integrable L _ (loopMasterLengthTest L ψ hψ).property⟩ k =
      transportCoeffs P L (loopMasterLengthTest L ξ hξ) k) :
    (∫ u in (0 : ℝ)..L.val, ψ (u : Circle L)) = 0 := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hz := htransport 0
  unfold coeff transportCoeffs at hz
  rw [fourierCoeff_eq_intervalIntegral _ 0 0] at hz
  simp only [zero_add, neg_zero, fourier_zero, ite_true, smul_eq_mul, one_mul, Complex.real_smul] at hz
  rw [intervalIntegral.integral_ofReal] at hz
  have hL : ((1 / L.val : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (one_div_ne_zero L.property.ne')
  have hi := (mul_eq_zero.mp hz).resolve_left hL
  exact_mod_cast hi

end Riesz1

end
