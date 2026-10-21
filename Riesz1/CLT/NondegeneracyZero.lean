/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityConsequences
public import Riesz1.ToMathlib.CircleFourierUniqueness
public import Riesz1.Gibbs.FluctuationMoments
public import Riesz1.Frozen.NormalizedStatistic
public import Riesz1.Frozen.NormalLaw
public import Riesz1.CLT.IdentityDefs

/-!
# Zero variance in the CLT

The zero-variance characterizations in the nondegeneracy argument for Theorem 3.
The statements use the extended nonnegative variances, so they also apply
before Sobolev finiteness has been established.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Riesz1

/-- The extension of the circle variance to arbitrary square-integrable
tests agrees with the profile variance. -/
theorem circleVariance_eq_cltVariance (P : Parameters) (p : Profile) (a : Scale) :
    circleVariance P p a = cltVariance P a
      ⟨(fun x => (testAtScale p a x : ℂ)), testAtScaleL2 p a⟩ := rfl

namespace Internal

lemma nondegeneracy_variance_prefactor_pos (P : Parameters) (a : Scale) :
    0 < (2 * Real.pi) ^ (1 - P.val.2) /
      (2 * P.val.1 * rieszConstant (parametersExponent P)) * a.val ^ (-P.val.2) := by
  have hc := rieszConstant_pos (parametersExponent P)
  have hb := P.property.1
  have ha := a.property.1
  positivity

lemma nondegeneracy_coeff_const (c : ℂ) (k : ℤ) :
    fourierCoeff (fun _ : UnitAddCircle => c) k = if k = 0 then c else 0 := by
  have he : (fun _ : UnitAddCircle => c) = fun x => c * fourier (0 : ℤ) x := by
    ext x
    simp
  rw [he, fourierCoeff.const_mul, fourierCoeff_fourier]
  by_cases hk : k = 0 <;> simp [hk]

end Internal

/-- A circle homogeneous Sobolev seminorm vanishes precisely on constants.
This holds for every real order, since every nonzero Fourier weight is positive. -/
theorem circleSobolevSq_eq_zero_iff (r : ℝ)
    (f : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) :
    circleSobolevSq r f = 0 ↔ ∃ c : ℂ, f.val =ᵐ[volume] fun _ => c := by
  constructor
  · intro hz
    have hcoeff (k : ℤ) (hk : k ≠ 0) : fourierCoeff f.val k = 0 := by
      have ht := (ENNReal.tsum_eq_zero.mp hz) k
      have ht : ENNReal.ofReal (|(k : ℝ)| ^ (2 * r) * ‖fourierCoeff f.val k‖ ^ 2) = 0 := by
        simpa only [ite_eq_right hk] using ht
      have hp : 0 < |(k : ℝ)| ^ (2 * r) :=
        Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr hk)) _
      have hn : ‖fourierCoeff f.val k‖ ^ 2 = 0 := by
        nlinarith [ENNReal.ofReal_eq_zero.mp ht, sq_nonneg ‖fourierCoeff f.val k‖]
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    refine ⟨fourierCoeff f.val 0, CircleFourier.ae_eq_of_coeff_eq f.property (memLp_const _) ?_⟩
    intro k
    rw [Internal.nondegeneracy_coeff_const]
    split_ifs with hk
    · subst k; rfl
    · exact hcoeff k hk
  · rintro ⟨c, hc⟩
    unfold circleSobolevSq
    apply ENNReal.tsum_eq_zero.mpr
    intro k
    rw [fourierCoeff_congr_ae hc k, Internal.nondegeneracy_coeff_const]
    by_cases hk : k = 0 <;> simp [hk]

/-- The macroscopic zero-variance characterization in the nondegeneracy
argument for Theorem 3, for every real square-integrable profile. -/
theorem clt_nondegeneracy_macroscopic_zero (P : Parameters) (p : Profile) :
    circleVariance P p ⟨1, by norm_num⟩ = 0 ↔
      ∃ c : ℝ, p.val =ᵐ[volume] fun _ => c := by
  have hp := Internal.nondegeneracy_variance_prefactor_pos P ⟨1, by norm_num⟩
  have hne := (ENNReal.ofReal_pos.mpr hp).ne'
  simp only [circleVariance, mul_eq_zero, hne, false_or, testAtScale, ite_true]
  rw [circleSobolevSq_eq_zero_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.re, hc.mono fun x hx => congrArg Complex.re hx⟩
  · rintro ⟨c, hc⟩
    exact ⟨(c : ℂ), hc.mono fun x hx => congrArg Complex.ofReal hx⟩

/-- Unlike the circle seminorm, the line homogeneous Sobolev seminorm is
positive definite on `L²`: the exceptional zero frequency is Lebesgue-null. -/
theorem lineSobolevSq_eq_zero_iff (r : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    lineSobolevSq r f = 0 ↔ f = 0 := by
  constructor
  · intro hz
    have hm : AEMeasurable (fun η : ℝ =>
        ENNReal.ofReal (|η| ^ (2 * r) * ‖Lp.fourierTransformₗᵢ ℝ ℂ f η‖ ^ 2)) volume := by
      fun_prop
    have hae := (lintegral_eq_zero_iff' hm).mp hz
    have hF : Lp.fourierTransformₗᵢ ℝ ℂ f = 0 := by
      apply Lp.ext
      filter_upwards [hae, volume.ae_ne 0, Lp.coeFn_zero ℂ 2 volume]
        with η hη hη0 hzero
      rw [hzero]
      have hp : 0 < |η| ^ (2 * r) := Real.rpow_pos_of_pos (abs_pos.mpr hη0) _
      have hn : ‖Lp.fourierTransformₗᵢ ℝ ℂ f η‖ ^ 2 = 0 := by
        nlinarith [ENNReal.ofReal_eq_zero.mp hη,
          sq_nonneg ‖Lp.fourierTransformₗᵢ ℝ ℂ f η‖]
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    exact (Lp.fourierTransformₗᵢ ℝ ℂ).injective (by simpa using hF)
  · rintro rfl
    simp [lineSobolevSq]

/-- The line zero-variance characterization in the nondegeneracy argument for Theorem 3.
No compact support or regularity assumption is needed for this implication. -/
theorem clt_nondegeneracy_line_zero (P : Parameters) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    lineVariance P f = 0 ↔ f = 0 := by
  have hp := Internal.nondegeneracy_variance_prefactor_pos P ⟨1, by norm_num⟩
  simp only [Real.one_rpow, mul_one] at hp
  simp only [lineVariance, mul_eq_zero, (ENNReal.ofReal_pos.mpr hp).ne', false_or]
  exact lineSobolevSq_eq_zero_iff _ f

/-- The compact-profile formulation, using the zero extension. -/
theorem clt_nondegeneracy_compact_zero (P : Parameters) (p : Profile)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : RepresentsZeroExtension p f) :
    lineVariance P f = 0 ↔ zeroExtension p =ᵐ[volume] fun _ => 0 := by
  rw [clt_nondegeneracy_line_zero]
  constructor
  · intro hz
    have hc := hf.symm.trans (hz ▸ Lp.coeFn_zero ℂ 2 volume)
    exact hc.mono fun x hx => Complex.ofReal_injective hx
  · intro hz
    have hc : (fun x => (zeroExtension p x : ℂ)) =ᵐ[volume] fun _ => 0 :=
      hz.mono fun x hx => by simpa only [Complex.ofReal_zero] using congrArg Complex.ofReal hx
    exact Lp.ext (hf.trans (hc.trans (Lp.coeFn_zero ℂ 2 volume).symm))

end Riesz1
