/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportSeries
public import Riesz1.Kernel.AdmissibleExamplesPrimitive

/-!
# Finite differentiability of Fourier series

A summable second frequency moment supplies a real, globally twice continuously
differentiable representative, with a uniform bound for its second derivative.
-/

public section

open MeasureTheory Set Filter Topology ComplexConjugate
open scoped ContDiff

namespace Riesz1

/-- Differentiate an absolutely convergent Fourier series when its first frequency
moment is summable. -/
theorem hasDerivAt_fourierSeries_of_summable {c : ℤ → ℂ}
    (hc : Summable fun k => ‖c k‖)
    (hd : Summable fun k => ‖c k * (2 * Real.pi * Complex.I * (k : ℂ))‖) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∑' k, c k * fourier k (y : UnitAddCircle))
      (∑' k, (c k * (2 * Real.pi * Complex.I * (k : ℂ))) * fourier k (x : UnitAddCircle)) x := by
  refine hasDerivAt_tsum (g := fun k (y : ℝ) => c k * fourier k (y : UnitAddCircle))
    (g' := fun k (y : ℝ) => (c k * (2 * Real.pi * Complex.I * (k : ℂ))) *
      fourier k (y : UnitAddCircle)) (y₀ := x) hd ?_ ?_ ?_ x
  · intro k y
    convert (hasDerivAt_fourier_coe k y).const_mul (c k) using 1
    ring
  · intro k y
    rw [norm_mul, norm_fourier_coe, mul_one]
  · exact Summable.of_norm_bounded hc (fun k => by
      rw [norm_mul, norm_fourier_coe, mul_one])

/-- Summability of each frequency moment through order `n` gives `C^n` regularity. -/
theorem contDiff_fourierSeries_of_moments (n : ℕ) (c : ℤ → ℂ)
    (hc : ∀ m : ℕ, m ≤ n → Summable fun k : ℤ => |(k : ℝ)| ^ m * ‖c k‖) :
    ContDiff ℝ n (fun x : ℝ => ∑' k, c k * fourier k (x : UnitAddCircle)) := by
  induction n generalizing c with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_fourierSeries (by simpa using hc 0 le_rfl)
  | succ n ih =>
    let d : ℤ → ℂ := fun k => c k * (2 * Real.pi * Complex.I * (k : ℂ))
    have hd : ∀ m : ℕ, m ≤ n → Summable fun k : ℤ => |(k : ℝ)| ^ m * ‖d k‖ :=
      fun m hm => summable_pow_mul_norm_mul_two_pi_I (hc (m + 1) (by omega))
    have hder : deriv (fun y : ℝ => ∑' k, c k * fourier k (y : UnitAddCircle)) =
        fun x : ℝ => ∑' k, d k * fourier k (x : UnitAddCircle) :=
      funext fun x => (hasDerivAt_fourierSeries_of_summable
        (by simpa using hc 0 (by omega)) (by simpa only [pow_zero, one_mul] using hd 0 (by omega)) x).deriv
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hasDerivAt_fourierSeries_of_summable
      (by simpa using hc 0 (by omega)) (by simpa only [pow_zero, one_mul] using hd 0 (by omega)) x).differentiableAt,
      fun h => absurd h (by simp), ?_⟩
    rw [hder]
    exact ih d hd

/-- A conjugate-symmetric sequence with summable frequency moments through order two
has a real `C²` representative, with the exact coefficients and bounded second derivative. -/
theorem exists_real_C2_fourierSeries (c : ℤ → ℂ)
    (hc : ∀ m : ℕ, m ≤ 2 → Summable fun k : ℤ => |(k : ℝ)| ^ m * ‖c k‖)
    (hsym : ∀ k, conj (c k) = c (-k)) :
    ∃ G : UnitAddCircle → ℝ, Continuous G ∧
      (∀ k, fourierCoeff (fun x => (G x : ℂ)) k = c k) ∧
      ContDiff ℝ 2 (fun x : ℝ => G (x : UnitAddCircle)) ∧
      ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ,
        |deriv (deriv (fun y : ℝ => G (y : UnitAddCircle))) x| ≤ B := by
  let F : UnitAddCircle → ℂ := fun x => ∑' k : ℤ, c k * fourier k x
  have hc0 : Summable fun k => ‖c k‖ := by simpa using hc 0 (by norm_num)
  have hFc : Continuous F := continuous_tsum
    (fun k => continuous_const.mul (fourier k).continuous) hc0
    (fun k x => by rw [norm_mul, norm_fourier_point, mul_one])
  have hreal : ∀ x, ((F x).re : ℂ) = F x := by
    intro x
    apply Complex.conj_eq_iff_re.mp
    dsimp only [F]
    rw [Complex.conj_tsum]
    calc
      ∑' k : ℤ, conj (c k * fourier k x) = ∑' k : ℤ, c (-k) * fourier (-k) x := by
        apply tsum_congr
        intro k
        rw [map_mul, hsym, ← fourier_neg]
      _ = ∑' k : ℤ, c k * fourier k x := (Equiv.neg ℤ).tsum_eq (fun k : ℤ => c k * fourier k x)
  let G : UnitAddCircle → ℝ := fun x => (F x).re
  have hGcd : ContDiff ℝ 2 (fun x : ℝ => G (x : UnitAddCircle)) :=
    Complex.reCLM.contDiff.comp (contDiff_fourierSeries_of_moments 2 c hc)
  refine ⟨G, Complex.continuous_re.comp hFc, ?_, hGcd, ?_⟩
  · intro k
    change fourierCoeff (fun x => ((F x).re : ℂ)) k = c k
    simp_rw [hreal]
    exact fourierCoeff_tsum_fourier c hc0 k
  · let d : ℤ → ℂ := fun k => c k * (2 * Real.pi * Complex.I * (k : ℂ))
    let e : ℤ → ℂ := fun k => d k * (2 * Real.pi * Complex.I * (k : ℂ))
    have hd : ∀ m : ℕ, m ≤ 1 → Summable fun k : ℤ => |(k : ℝ)| ^ m * ‖d k‖ :=
      fun m hm => summable_pow_mul_norm_mul_two_pi_I (hc (m + 1) (by omega))
    have hd0 : Summable fun k => ‖d k‖ := by simpa using hd 0 (by norm_num)
    have he0 : Summable fun k => ‖e k‖ := by
      simpa only [pow_zero, one_mul] using summable_pow_mul_norm_mul_two_pi_I (hd 1 le_rfl)
    have hGd : deriv (fun y : ℝ => G (y : UnitAddCircle)) =
        fun x : ℝ => (∑' k, d k * fourier k (x : UnitAddCircle)).re := by
      funext x
      exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
        (hasDerivAt_fourierSeries_of_summable hc0 hd0 x)).deriv
    have hGdd (x : ℝ) : deriv (deriv (fun y : ℝ => G (y : UnitAddCircle))) x =
        (∑' k, e k * fourier k (x : UnitAddCircle)).re := by
      rw [hGd]
      exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
        (hasDerivAt_fourierSeries_of_summable hd0 he0 x)).deriv
    refine ⟨1 + ∑' k, ‖e k‖, by positivity, fun x => ?_⟩
    rw [hGdd]
    calc
      |(∑' k, e k * fourier k (x : UnitAddCircle)).re|
        ≤ ‖∑' k, e k * fourier k (x : UnitAddCircle)‖ := Complex.abs_re_le_norm _
      _ ≤ ∑' k, ‖e k * fourier k (x : UnitAddCircle)‖ :=
        norm_tsum_le_tsum_norm (by simpa only [norm_mul, norm_fourier_point, mul_one] using he0)
      _ ≤ 1 + ∑' k, ‖e k‖ := by
        simp only [norm_mul, norm_fourier_point, mul_one]
        linarith

end Riesz1
