/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleFourierDerivative
public import Riesz1.ToMathlib.MollifierPointwise.Derivative

/-!
# Classical circle derivatives and absolute Fourier bounds

Smoothness is already supplied by convolution. Fourier reconstruction of the
continuous derivative then bounds its supremum by its absolute coefficient sum.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1.CircleFourier

/-- The derivative of a smooth real periodic function descends continuously
and its Fourier coefficients have the physical differentiation multiplier. -/
theorem exists_circle_derivative {L : ℝ} [hL : Fact (0 < L)]
    {g : AddCircle L → ℝ} (hg : Continuous g)
    (hs : ContDiff ℝ ∞ (fun x : ℝ => g (x : AddCircle L))) :
    ∃ d : AddCircle L → ℝ, Continuous d ∧
      ContDiff ℝ ∞ (fun x : ℝ => d (x : AddCircle L)) ∧
      (∀ x : ℝ, d (x : AddCircle L) = deriv (fun t : ℝ => g (t : AddCircle L)) x) ∧
      ∀ k : ℤ, fourierCoeff (fun x => (d x : ℂ)) k =
        (2 * Real.pi * Complex.I * (k : ℂ) / L) * fourierCoeff (fun x => (g x : ℂ)) k := by
  let F := fun x : ℝ => g (x : AddCircle L)
  have hp : Function.Periodic F L := by intro x; simp only [F, AddCircle.coe_add_period]
  have hdp := Riesz1.periodic_deriv hp
  let d : AddCircle L → ℝ := hdp.lift
  have hd (x : ℝ) : d (x : AddCircle L) = deriv F x := hdp.lift_coe x
  have hds : ContDiff ℝ ∞ (fun x : ℝ => d (x : AddCircle L)) := by
    simpa only [hd] using (contDiff_infty_iff_deriv.mp hs).2
  have hdc : Continuous d :=
    (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L)).continuous_iff.mpr
      hds.continuous
  refine ⟨d, hdc, hds, hd, fun k => ?_⟩
  have hJ := integral_deriv_mul_fourier hg Set.countable_empty
    (fun x _ => hs.differentiable (by simp) x)
    ((hs.continuous_deriv (by simp)).intervalIntegrable 0 L) k
  rw [fourierCoeff_eq_intervalIntegral _ k (0 : ℝ)]
  simp only [zero_add, hd, smul_eq_mul, Complex.real_smul]
  have he : (∫ x in (0 : ℝ)..L, fourier (-k) (x : AddCircle L) * ((deriv F x : ℝ) : ℂ)) =
      (L : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ) / L) *
        fourierCoeff (fun x => (g x : ℂ)) k := by
    rw [← hJ]
    apply intervalIntegral.integral_congr
    intro x _
    exact mul_comm _ _
  rw [he]
  simp only [one_div, Complex.ofReal_inv]
  field_simp

/-- An absolute coefficient bound controls the actual continuous function. -/
theorem abs_le_tsum_norm_fourierCoeff {L : ℝ} [Fact (0 < L)]
    {g : AddCircle L → ℝ} (hg : Continuous g)
    (hs : Summable (fun k : ℤ => ‖fourierCoeff (fun x => (g x : ℂ)) k‖))
    (x : AddCircle L) : |g x| ≤ ∑' k : ℤ, ‖fourierCoeff (fun x => (g x : ℂ)) k‖ := by
  let G : C(AddCircle L, ℂ) := ⟨(fun x => (g x : ℂ)), Complex.continuous_ofReal.comp hg⟩
  have ht := has_pointwise_sum_fourier_series_of_summable (f := G) (.of_norm hs) x
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  change ‖G x‖ ≤ _
  rw [← ht.tsum_eq]
  calc _ ≤ ∑' k : ℤ, ‖fourierCoeff G k • fourier k x‖ :=
      norm_tsum_le_tsum_norm (by
        simpa only [norm_smul, fourier_apply, Circle.norm_coe, mul_one, G, ContinuousMap.coe_mk] using hs)
    _ = _ := by simp only [norm_smul, fourier_apply, Circle.norm_coe, mul_one]; rfl

/-- Absolute first frequency moments bound the classical derivative. -/
theorem abs_deriv_le_fourier_moment {L : ℝ} [Fact (0 < L)]
    {g : AddCircle L → ℝ} (hg : Continuous g)
    (hs : ContDiff ℝ ∞ (fun x : ℝ => g (x : AddCircle L)))
    (hm : Summable (fun k : ℤ =>
      ‖(2 * Real.pi * Complex.I * (k : ℂ) / L)‖ *
        ‖fourierCoeff (fun x => (g x : ℂ)) k‖)) (x : ℝ) :
    |deriv (fun t : ℝ => g (t : AddCircle L)) x| ≤
      ∑' k : ℤ, ‖(2 * Real.pi * Complex.I * (k : ℂ) / L)‖ *
        ‖fourierCoeff (fun x => (g x : ℂ)) k‖ := by
  obtain ⟨d, hdc, _, hd, hcoeff⟩ := exists_circle_derivative hg hs
  have hdsm : Summable (fun k : ℤ => ‖fourierCoeff (fun y => (d y : ℂ)) k‖) := by
    simpa only [hcoeff, norm_mul] using hm
  rw [← hd]
  have hb := abs_le_tsum_norm_fourierCoeff hdc hdsm (x : AddCircle L)
  simpa only [hcoeff, norm_mul] using hb

/-- Absolute second frequency moments bound the second classical derivative. -/
theorem abs_secondDeriv_le_fourier_moment {L : ℝ} [Fact (0 < L)]
    {g : AddCircle L → ℝ} (hg : Continuous g)
    (hs : ContDiff ℝ ∞ (fun x : ℝ => g (x : AddCircle L)))
    (hm : Summable (fun k : ℤ =>
      ‖(2 * Real.pi * Complex.I * (k : ℂ) / L)‖ ^ 2 *
        ‖fourierCoeff (fun x => (g x : ℂ)) k‖)) (x : ℝ) :
    |deriv (deriv (fun t : ℝ => g (t : AddCircle L))) x| ≤
      ∑' k : ℤ, ‖(2 * Real.pi * Complex.I * (k : ℂ) / L)‖ ^ 2 *
        ‖fourierCoeff (fun x => (g x : ℂ)) k‖ := by
  obtain ⟨d, hdc, hds, hd, hcoeff⟩ := exists_circle_derivative hg hs
  have hdsm : Summable (fun k : ℤ =>
      ‖(2 * Real.pi * Complex.I * (k : ℂ) / L)‖ *
        ‖fourierCoeff (fun y => (d y : ℂ)) k‖) := by
    simpa only [hcoeff, norm_mul, ← mul_assoc, ← pow_two] using hm
  have he : (fun x : ℝ => d (x : AddCircle L)) =
      deriv (fun x : ℝ => g (x : AddCircle L)) := funext hd
  have hb := abs_deriv_le_fourier_moment hdc hds hdsm x
  rw [he] at hb
  simpa only [hcoeff, norm_mul, ← mul_assoc, ← pow_two] using hb

end Riesz1.CircleFourier
