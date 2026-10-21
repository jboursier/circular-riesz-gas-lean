/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityMembership
public import Riesz1.Kernel.TransportScaledMain

/-!
# Coefficients of a periodized profile as samples of one continuous integral

The angular-frequency integral of the fixed zero extension supplies all enlarged-circle
coefficients. Its continuity permits a shrinking-grid limit.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- Every zero extension is integrable on the line, with its actual compact support. -/
theorem zeroExtension_integrable (p : Profile) : Integrable (zeroExtension p) := by
  apply (zeroExtension_integrableOn p unitLength).1.integrable_of_forall_notMem_eq_zero
  intro x hx
  have hn : ¬ |x| < 1 / 2 := by
    intro ht
    apply hx
    change x ∈ Ioc (-(1 / 2 : ℝ)) (1 / 2)
    exact ⟨(abs_lt.mp ht).1, (abs_lt.mp ht).2.le⟩
  simp only [zeroExtension, ite_eq_right hn]

/-- The angular-frequency integral of a fixed profile is continuous. -/
theorem continuous_zeroExtension_fourierIntegral (p : Profile) :
    Continuous (fun w : ℝ => ∫ x : ℝ,
      (zeroExtension p x : ℂ) * Complex.exp (((-w * x : ℝ) : ℂ) * Complex.I)) := by
  have hz : Integrable (fun x => (zeroExtension p x : ℂ)) :=
    Complex.ofRealCLM.integrable_comp (zeroExtension_integrable p)
  apply continuous_of_dominated
    (bound := fun x => |zeroExtension p x|)
  · intro w
    exact hz.aestronglyMeasurable.mul (by fun_prop : Continuous
      (fun x : ℝ => Complex.exp (((-w * x : ℝ) : ℂ) * Complex.I))).aestronglyMeasurable
  · intro w
    exact ae_of_all _ fun x => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  · exact (zeroExtension_integrable p).abs
  · exact ae_of_all _ fun x => by fun_prop

/-- The line integral is uniformly bounded by the fixed profile's integral norm. -/
theorem norm_zeroExtension_fourierIntegral_le (p : Profile) (w : ℝ) :
    ‖∫ x : ℝ, (zeroExtension p x : ℂ) *
      Complex.exp (((-w * x : ℝ) : ℂ) * Complex.I)‖ ≤ ∫ x : ℝ, |zeroExtension p x| := by
  calc _ ≤ ∫ x : ℝ, ‖(zeroExtension p x : ℂ) *
          Complex.exp (((-w * x : ℝ) : ℂ) * Complex.I)‖ := norm_integral_le_integral_norm _
    _ = _ := by
      congr 1
      funext x
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- Exact arclength normalization: multiplying a periodized coefficient by the circle
length gives the fixed zero extension's angular-frequency integral at that frequency. -/
theorem length_mul_periodizedProfile_coeff (p : Profile) (a : Scale) (k : ℤ) :
    ((observationLength a).val : ℂ) * coeff (observationLength a)
      ⟨(fun x => (periodizedProfile p (observationLength a) x : ℂ)),
        complexL2Integrable _ _ (periodizedProfileL2 p a)⟩ k =
      ∫ x : ℝ, (zeroExtension p x : ℂ) *
        Complex.exp (((-(2 * Real.pi * (k : ℝ) / (observationLength a).val) * x : ℝ) : ℂ) *
          Complex.I) := by
  let L := observationLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hL1 : 1 ≤ L.val := (one_le_inv₀ a.property.1).mpr a.property.2
  change (L.val : ℂ) * fourierCoeff (fun x : Circle L => (periodizedProfile p L x : ℂ)) k = _
  rw [fourierCoeff_eq_intervalIntegral _ k (-(L.val / 2)),
    show -(L.val / 2) + L.val = L.val / 2 by ring]
  simp only [one_div, smul_eq_mul, Complex.real_smul, Complex.ofReal_inv]
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast L.property.ne'), one_mul]
  have heq : (∫ x in (-(L.val / 2))..(L.val / 2), fourier (-k) (x : Circle L) *
      (periodizedProfile p L (x : Circle L) : ℂ)) =
      ∫ x in (-(L.val / 2))..(L.val / 2), (zeroExtension p x : ℂ) *
        Complex.exp (((-(2 * Real.pi * (k : ℝ) / L.val) * x : ℝ) : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith [L.property])
    intro x hx
    dsimp only
    have hcell : x ∈ Ico (-L.val / 2) (-L.val / 2 + L.val) :=
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hrep : centralRep L (x : Circle L) = x := by
      unfold centralRep
      exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hcell)
    rw [admissibility_periodizedProfile_eq_zeroExtension p L hL1, hrep, fourier_coe_apply]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  rw [heq, intervalIntegral.integral_of_le (by linarith [L.property])]
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  exact ae_of_all _ fun x hx => by
    have hx0 : zeroExtension p x = 0 := by
      have hn : ¬ |x| < 1 / 2 := by
        intro ht
        apply hx
        have hab := abs_lt.mp ht
        exact ⟨by linarith [hab.1], by linarith [hab.2]⟩
      simp only [zeroExtension, ite_eq_right hn]
    rw [hx0, Complex.ofReal_zero, zero_mul]

end Riesz1
