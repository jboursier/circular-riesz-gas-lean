/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleFourierDerivative
public import Riesz1.Kernel.AdmissibleExamplesRieszTransport

/-!
# Mean-zero primitives of continuous circle functions

A continuous real circle function has a continuously differentiable mean-zero
periodic primitive after centering. The Fourier identity holds across a full period.
-/

public section

open MeasureTheory Set Filter Topology intervalIntegral

namespace Riesz1

/-- Centering a continuous circle function and integrating gives a real periodic
primitive, with zero Fourier mode zero and the expected nonzero coefficients. -/
theorem exists_continuous_centered_primitive {f : UnitAddCircle → ℝ} (hc : Continuous f) :
    ∃ H : UnitAddCircle → ℝ, Continuous H ∧
      fourierCoeff (fun x => (H x : ℂ)) 0 = 0 ∧
      (∀ x : ℝ, HasDerivAt (fun u : ℝ => H (u : UnitAddCircle))
        (f (x : UnitAddCircle) - ∫ t in (0 : ℝ)..1, f (t : UnitAddCircle)) x) ∧
      ∀ k : ℤ, k ≠ 0 → (2 * Real.pi * Complex.I * (k : ℂ)) *
        fourierCoeff (fun x => (H x : ℂ)) k = fourierCoeff (fun x => (f x : ℂ)) k := by
  let m : ℝ := ∫ t in (0 : ℝ)..1, f (t : UnitAddCircle)
  let q : ℝ → ℝ := fun x => f (x : UnitAddCircle) - m
  have hqc : Continuous q := (hc.comp (AddCircle.continuous_mk' 1)).sub continuous_const
  have hqp : Function.Periodic q 1 := fun x => by simp only [q, AddCircle.coe_add_period]
  have hq0 : ∫ t in (0 : ℝ)..1, q t = 0 := by
    rw [show q = (fun x : ℝ => f (x : UnitAddCircle) - m) from rfl,
      intervalIntegral.integral_sub (f := fun x : ℝ => f (x : UnitAddCircle))
        (g := fun _ : ℝ => m) ((hc.comp (AddCircle.continuous_mk' 1)).intervalIntegrable 0 1)
        intervalIntegrable_const, intervalIntegral.integral_const]
    simp [m]
  let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, q t
  have hFp : Function.Periodic F 1 := by
    intro x
    apply sub_eq_zero.mp
    change (∫ t in (0 : ℝ)..(x + 1), q t) - (∫ t in (0 : ℝ)..x, q t) = 0
    rw [integral_interval_sub_left (hqc.intervalIntegrable _ _) (hqc.intervalIntegrable _ _),
      hqp.intervalIntegral_add_eq x 0, zero_add, hq0]
  let H₀ : UnitAddCircle → ℝ := hFp.lift
  have hH₀coe (x : ℝ) : H₀ (x : UnitAddCircle) = F x := hFp.lift_coe x
  have hH₀c : Continuous H₀ := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    change Continuous (fun x : ℝ => H₀ (x : UnitAddCircle))
    exact (continuous_primitive (fun a b => hqc.intervalIntegrable a b) 0).congr
      fun x => (hH₀coe x).symm
  let n : ℝ := ∫ x : UnitAddCircle, H₀ x ∂AddCircle.haarAddCircle
  let H : UnitAddCircle → ℝ := fun x => H₀ x - n
  have hHd (x : ℝ) : HasDerivAt (fun u : ℝ => H (u : UnitAddCircle)) (q x) x := by
    have hd := (hqc.integral_hasStrictDerivAt 0 x).hasDerivAt.sub_const n
    simpa only [H, hH₀coe, F] using hd
  have hHc : Continuous H := hH₀c.sub continuous_const
  have hiH₀ : Integrable (fun x : UnitAddCircle => (H₀ x : ℂ)) AddCircle.haarAddCircle :=
    integrable_of_continuous_circle (Complex.continuous_ofReal.comp hH₀c)
  have hH0 : fourierCoeff (fun x => (H x : ℂ)) 0 = 0 := by
    simp only [H, Complex.ofReal_sub]
    rw [fourierCoeff_sub_const hiH₀ (n : ℂ) 0]
    simp only [fourierCoeff, neg_zero, fourier_zero, one_smul, n, integral_complex_ofReal]
    simp
  refine ⟨H, hHc, hH0, hHd, fun k hk => ?_⟩
  have hder : deriv (fun u : ℝ => H (u : UnitAddCircle)) = q := funext fun x => (hHd x).deriv
  have he := CircleFourier.integral_deriv_mul_fourier hHc (S := ∅) Set.countable_empty
    (fun x _ => (hHd x).differentiableAt)
    (by rw [hder]; exact hqc.intervalIntegrable 0 1) k
  simp only [Complex.ofReal_one, one_mul, div_one] at he
  rw [hder] at he
  have hfi : Integrable (fun x : UnitAddCircle => (f x : ℂ)) AddCircle.haarAddCircle :=
    integrable_of_continuous_circle (Complex.continuous_ofReal.comp hc)
  have hcf := fourierCoeff_eq_intervalIntegral
    (fun x : UnitAddCircle => ((f x - m : ℝ) : ℂ)) k 0
  simp only [zero_add, one_div_one, one_smul, smul_eq_mul] at hcf
  have hcoeff : (∫ t in (0 : ℝ)..1, (q t : ℂ) * fourier (-k) (t : UnitAddCircle)) =
      fourierCoeff (fun x => (f x : ℂ)) k := by
    rw [show (fun t : ℝ => (q t : ℂ) * fourier (-k) (t : UnitAddCircle)) =
      fun t : ℝ => fourier (-k) (t : UnitAddCircle) * ((f (t : UnitAddCircle) - m : ℝ) : ℂ)
      from funext fun t => mul_comm _ _, ← hcf]
    simp only [Complex.ofReal_sub]
    rw [fourierCoeff_sub_const hfi (m : ℂ) k, fourierCoeff_one]
    simp [hk]
  exact he.symm.trans hcoeff

end Riesz1
