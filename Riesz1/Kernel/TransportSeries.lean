/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HeatKernel.Operators
public import Riesz1.ToMathlib.CircleBasics
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Smooth Fourier series on the unit circle

For a sequence `c : ℤ → ℂ` with `∑_k |k|^m ‖c_k‖ < ∞` for every `m`, the series
`x ↦ ∑_k c_k e^{2πikx}` is `C^∞` on `ℝ`, and its Fourier coefficients are the `c_k`.

These are the two facts used to identify the transport of a smooth profile: its Fourier
multiplier series is smooth, and its coefficients are the transport coefficients.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ContDiff Real

namespace Riesz1

/-- The character `x ↦ e^{2πikx}` on `ℝ`, through the circle. -/
lemma hasDerivAt_fourier_coe (k : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => fourier k (y : UnitAddCircle))
      (2 * π * I * (k : ℂ) * fourier k (x : UnitAddCircle)) x := by
  have h1 : (fun y : ℝ => fourier k (y : UnitAddCircle)) =
      fun y : ℝ => Complex.exp (2 * π * I * (k : ℂ) * (y : ℂ)) := by
    funext y
    rw [fourier_coe_apply]
    simp only [Complex.ofReal_one, div_one]
  rw [h1, show 2 * π * I * (k : ℂ) * fourier k (x : UnitAddCircle) =
    Complex.exp (2 * π * I * (k : ℂ) * (x : ℂ)) * (2 * π * I * (k : ℂ)) by
      rw [fourier_coe_apply]; simp only [Complex.ofReal_one, div_one]; ring]
  have h2 : HasDerivAt (fun y : ℝ => 2 * π * I * (k : ℂ) * (y : ℂ))
      (2 * π * I * (k : ℂ)) x := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (2 * π * I * (k : ℂ)))
  have h3 := h2.cexp
  convert h3 using 1

/-- The character `x ↦ e^{2πikx}` is continuous on `ℝ`. -/
lemma continuous_fourier_coe (k : ℤ) : Continuous fun x : ℝ => fourier k (x : UnitAddCircle) :=
  (fourier k).continuous.comp continuous_quotient_mk'

/-- A norm-summable Fourier series of coefficients is continuous. -/
lemma continuous_fourierSeries {c : ℤ → ℂ} (hc : Summable fun k => ‖c k‖) :
    Continuous fun x : ℝ => ∑' k, c k * fourier k (x : UnitAddCircle) :=
  continuous_tsum (fun k => continuous_const.mul (continuous_fourier_coe k)) hc
    (fun k x => by rw [norm_mul, norm_fourier_coe, mul_one])

/-- The norm of `2πik` is `2π|k|`. -/
lemma norm_two_pi_I_mul_intCast (k : ℤ) : ‖(2 * π * I * (k : ℂ))‖ = 2 * π * |(k : ℝ)| := by
  simp [Complex.norm_intCast]

/-- The weighted norm bound of the coefficients `2πik c_k` is inherited from `c`. -/
lemma summable_pow_mul_norm_mul_two_pi_I {c : ℤ → ℂ} {m : ℕ}
    (hc : Summable fun k : ℤ => |(k : ℝ)| ^ (m + 1) * ‖c k‖) :
    Summable fun k : ℤ => |(k : ℝ)| ^ m * ‖c k * (2 * π * I * (k : ℂ))‖ := by
  refine (hc.mul_left (2 * π)).congr fun k => ?_
  rw [norm_mul, norm_two_pi_I_mul_intCast]
  ring

/-- Smoothness of the Fourier series, by induction on the order of differentiation. -/
lemma contDiff_fourierSeries_aux (n : ℕ) : ∀ c : ℤ → ℂ,
    (∀ m : ℕ, Summable fun k : ℤ => |(k : ℝ)| ^ m * ‖c k‖) →
      ContDiff ℝ n (fun x : ℝ => ∑' k, c k * fourier k (x : UnitAddCircle)) := by
  induction n with
  | zero =>
    intro c hc
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_fourierSeries (by simpa using hc 0)
  | succ n ih =>
    intro c hc
    set c' : ℤ → ℂ := fun k => c k * (2 * π * I * (k : ℂ)) with hc'def
    have hc' : ∀ m : ℕ, Summable fun k : ℤ => |(k : ℝ)| ^ m * ‖c' k‖ := fun m =>
      summable_pow_mul_norm_mul_two_pi_I (hc (m + 1))
    have hu1 : Summable fun k : ℤ => ‖c' k‖ := by simpa using hc' 0
    have hc0 : Summable fun k : ℤ => ‖c k‖ := by simpa using hc 0
    have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ∑' k, c k * fourier k (y : UnitAddCircle))
        (∑' k, c' k * fourier k (x : UnitAddCircle)) x := by
      intro x
      refine hasDerivAt_tsum (g := fun k (y : ℝ) => c k * fourier k (y : UnitAddCircle))
        (g' := fun k (y : ℝ) => c' k * fourier k (y : UnitAddCircle)) (y₀ := x) hu1 ?_ ?_ ?_ x
      · intro k y
        have h := (hasDerivAt_fourier_coe k y).const_mul (c k)
        convert h using 1
        simp only [hc'def]
        ring
      · intro k y
        rw [norm_mul, norm_fourier_coe, mul_one]
      · exact Summable.of_norm_bounded hc0 (fun k => by
          rw [norm_mul, norm_fourier_coe, mul_one])
    have hderiv : deriv (fun y : ℝ => ∑' k, c k * fourier k (y : UnitAddCircle)) =
        fun x : ℝ => ∑' k, c' k * fourier k (x : UnitAddCircle) :=
      funext fun x => (hd x).deriv
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hd x).differentiableAt, fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · rw [hderiv]
      exact ih c' hc'

/-- The Fourier series with coefficients of rapid decay is `C^∞`. -/
lemma contDiff_fourierSeries {c : ℤ → ℂ}
    (hc : ∀ m : ℕ, Summable fun k : ℤ => |(k : ℝ)| ^ m * ‖c k‖) :
    ContDiff ℝ ∞ (fun x : ℝ => ∑' k, c k * fourier k (x : UnitAddCircle)) :=
  contDiff_infty.2 fun n => contDiff_fourierSeries_aux n c hc

/-- The Fourier coefficients of a norm-summable Fourier series are its coefficients. -/
lemma fourierCoeff_fourierSeries {c : ℤ → ℂ} (hc : Summable fun k => ‖c k‖) (m : ℤ) :
    fourierCoeff (fun z : UnitAddCircle => ∑' k, c k * fourier k z) m = c m := by
  have hterm : ∀ k : ℤ, fourierCoeff (fun z : UnitAddCircle => c k * fourier k z) m =
      c k * (Pi.single k (1 : ℂ) : ℤ → ℂ) m := by
    intro k
    calc fourierCoeff (fun z : UnitAddCircle => c k * fourier k z) m
        = c k * fourierCoeff (fun z : UnitAddCircle => fourier k z) m :=
          fourierCoeff.const_mul _ _ _
      _ = c k * (Pi.single k (1 : ℂ) : ℤ → ℂ) m := by
          rw [show (fun z : UnitAddCircle => fourier k z) = ⇑(fourier k) from rfl,
            congrFun (fourierCoeff_fourier (T := 1) k) m]
  have hexch : fourierCoeff (fun z : UnitAddCircle => ∑' k, c k * fourier k z) m =
      ∑' k, fourierCoeff (fun z : UnitAddCircle => c k * fourier k z) m := by
    unfold fourierCoeff
    have hpt : ∀ z : UnitAddCircle, fourier (-m) z • (∑' k, c k * fourier k z) =
        ∑' k, fourier (-m) z • (c k * fourier k z) := by
      intro z
      simp only [smul_eq_mul]
      exact tsum_mul_left.symm
    simp_rw [hpt]
    have hbd : ∀ k : ℤ, ∀ z : UnitAddCircle, ‖fourier (-m) z • (c k * fourier k z)‖ = ‖c k‖ := by
      intro k z
      rw [norm_smul, norm_mul, norm_fourier_apply, norm_fourier_apply]
      ring
    have hint : ∀ k : ℤ, Integrable (fun z : UnitAddCircle => fourier (-m) z • (c k * fourier k z))
        AddCircle.haarAddCircle := by
      intro k
      refine (MemLp.of_bound ?_ ‖c k‖ (Eventually.of_forall fun z => (hbd k z).le)).integrable
        le_rfl
      exact (by fun_prop : Continuous fun z : UnitAddCircle =>
        fourier (-m) z • (c k * fourier k z)).aestronglyMeasurable
    refine (integral_tsum_of_summable_integral_norm hint ?_).symm
    refine hc.congr fun k => ?_
    simp only [hbd k, integral_const, probReal_univ, one_smul]
  rw [hexch]
  simp_rw [hterm]
  simp [Pi.single_apply]

end Riesz1
