/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.Coefficients
public import Riesz1.ToMathlib.HeatKernel.Operators
public import Riesz1.Kernel.FundamentalZeta

/-!
# The fundamental solution of the fractional Laplacian: Fourier form

Lemma 2.1, Fourier part. The periodic Riesz kernel `g_s` is the function
`Riesz1.rieszRepresentative s`, and its coefficients are `c_s (2π|k|)^{s-1}` for `k ≠ 0`.

A periodic distribution is identified with its Fourier coefficient sequence.
The distributional equation `(-Δ)^{(1-s)/2} g_s = c_s (δ_0 - 1)` and its uniqueness among
mean-zero distributions are therefore stated coefficientwise. The target `δ_0 - 1` has coefficients
`1 - [k = 0]`, since `δ_0` has coefficient `1` at every frequency.
-/

public section

open MeasureTheory Complex Set

namespace Riesz1

/-- The distributional equation `(-Δ)^{(1-s)/2} g_s = c_s (δ_0 - 1)` on `UnitAddCircle`, read
on Fourier coefficients (equation (1.2)). The coefficient of `g_s` at frequency `k` is
`fourierCoeff` of `rieszRepresentative s`, and the multiplier is
`fractionalLaplacianCoeffs` on the unit length with exponent `(1 - s) / 2`. -/
theorem fundamental_equation (s : RieszExponent) (k : ℤ) :
    fractionalLaplacianCoeffs unitLength ((1 - s.val) / 2)
        (fun j : ℤ => fourierCoeff (fun x : UnitAddCircle => (rieszRepresentative s x : ℂ)) j) k =
      (rieszConstant s : ℂ) * ((1 : ℂ) - if k = 0 then 1 else 0) := by
  rw [fractionalLaplacianCoeffs_unit]
  by_cases hk : k = 0
  · simp [hk]
  · have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    simp only [hk, ite_false, fourierCoeff_rieszRepresentative]
    have hpos : 0 < 2 * Real.pi * |(k : ℝ)| := by
      have : 0 < |(k : ℝ)| := abs_pos.mpr hk'
      positivity
    have habs : |2 * Real.pi * (k : ℝ)| = 2 * Real.pi * |(k : ℝ)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have hexp : (1 - s.val) + (s.val - 1) = 0 := by ring
    have hprod : (2 * Real.pi * |(k : ℝ)|) ^ (1 - s.val) *
        (2 * Real.pi * |(k : ℝ)|) ^ (s.val - 1) = 1 := by
      rw [← Real.rpow_add hpos, hexp, Real.rpow_zero]
    have hreal : |2 * Real.pi * (k : ℝ)| ^ (2 * ((1 - s.val) / 2)) *
        (rieszConstant s * (2 * Real.pi * |(k : ℝ)|) ^ (s.val - 1)) = rieszConstant s := by
      rw [habs, show 2 * ((1 - s.val) / 2) = 1 - s.val by ring]
      linear_combination (rieszConstant s) * hprod
    have key := congrArg (fun r : ℝ => (r : ℂ)) hreal
    push_cast at key ⊢
    linear_combination key

/-- Uniqueness of the fundamental solution: every coefficient sequence `a` with mean zero and
satisfying the distributional equation `(-Δ)^{(1-s)/2} a = c_s (δ_0 - 1)` is the coefficient
sequence of `g_s`. The equation fixes `a k` for each `k ≠ 0`, and mean zero fixes `a 0`. -/
theorem fundamental_unique (s : RieszExponent) (a : ℤ → ℂ) (ha0 : a 0 = 0)
    (ha : ∀ k : ℤ, fractionalLaplacianCoeffs unitLength ((1 - s.val) / 2) a k =
      (rieszConstant s : ℂ) * ((1 : ℂ) - if k = 0 then 1 else 0)) :
    a = fun j : ℤ => fourierCoeff (fun x : UnitAddCircle => (rieszRepresentative s x : ℂ)) j := by
  funext k
  by_cases hk : k = 0
  · subst hk
    show a 0 = fourierCoeff (fun x : UnitAddCircle => (rieszRepresentative s x : ℂ)) 0
    rw [ha0, fourierCoeff_rieszRepresentative_zero]
  · have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hq : (|2 * Real.pi * (k : ℝ)| ^ (2 * ((1 - s.val) / 2)) : ℝ) ≠ 0 :=
      (Real.rpow_pos_of_pos (abs_pos.mpr (mul_ne_zero (by positivity) hk')) _).ne'
    have h1 := ha k
    simp only [fractionalLaplacianCoeffs_unit, hk, ite_false] at h1
    have h2 := fundamental_equation s k
    simp only [fractionalLaplacianCoeffs_unit, hk, ite_false] at h2
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hq) (h1.trans h2.symm)

/-- The Hurwitz zeta function at `x ∈ (0, 1]` is Mathlib's function on the circle: the shift is
empty. -/
lemma hurwitzZetaPos_eq_hurwitzZeta_of_mem {z : ℂ} {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    hurwitzZetaPos z x = HurwitzZeta.hurwitzZeta (x : UnitAddCircle) z := by
  have h := hurwitzZetaPos_eq_of_shift z (m := 0) (x := x) (by simpa using hx0)
    (by simpa using hx1)
  simpa using h

/-- The pointwise formula `g_s(x) = ζ(s, x) + ζ(s, 1 - x)` on `(0, 1)` (equation (2.2)),
from the definition of `rieszRepresentative` through the circle reflection `-x = 1 - x`. -/
lemma rieszRepresentative_eq_hurwitzZetaPos (s : RieszExponent) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    rieszRepresentative s x = (hurwitzZetaPos (s.val : ℂ) x).re +
      (hurwitzZetaPos (s.val : ℂ) (1 - x)).re := by
  rw [hurwitzZetaPos_eq_hurwitzZeta_of_mem hx0 hx1.le,
    hurwitzZetaPos_eq_hurwitzZeta_of_mem (by linarith) (by linarith)]
  have hneg : -(x : UnitAddCircle) = ((1 - x : ℝ) : UnitAddCircle) := by
    rw [show (1 - x : ℝ) = -x + 1 by ring, AddCircle.coe_add, AddCircle.coe_period]
    simp
  unfold rieszRepresentative
  rw [HurwitzZeta.hurwitzZetaEven_eq, hneg]
  simp only [Complex.div_ofNat_re, Complex.add_re]
  ring

/-- The fundamental solution `g_s` of the fractional Laplacian on `UnitAddCircle`, Fourier form
(Lemma 2.1), with the claims that are proved in Lean:

* the Fourier coefficients: `ĝ_s(0) = 0` and `ĝ_s(k) = c_s (2π|k|)^{s-1}` for `k ≠ 0`
  (Lemma 2.1 for the coefficients, where `c_s = rieszConstant s`).
* the distributional equation `(-Δ)^{(1-s)/2} g_s = c_s (δ_0 - 1)`, read on the coefficients of
  `fractionalLaplacianCoeffs` (equation (1.2)).
* uniqueness: every coefficient sequence with mean zero solving the equation is `ĝ_s`.
* the pointwise formula `g_s(x) = ζ(s, x) + ζ(s, 1 - x)` for `0 < x < 1`
  (equation (2.2)).

Not included: the pointwise singular-integral formula (equation (2.3)) for `g_s` at `x ≠ 0`.
The singular-integral formula of Lemma 2.1 for smooth `f` does not apply here, because `g_s` is
singular at `0`. That case needs a separate argument. -/
theorem fundamental (s : RieszExponent) :
    (∀ k : ℤ, fourierCoeff (fun x : UnitAddCircle => (rieszRepresentative s x : ℂ)) k =
      if k = 0 then 0 else
        ((rieszConstant s * (2 * Real.pi * |(k : ℝ)|) ^ (s.val - 1) : ℝ) : ℂ)) ∧
    (∀ k : ℤ, fractionalLaplacianCoeffs unitLength ((1 - s.val) / 2)
        (fun j : ℤ => fourierCoeff (fun x : UnitAddCircle => (rieszRepresentative s x : ℂ)) j) k =
      (rieszConstant s : ℂ) * ((1 : ℂ) - if k = 0 then 1 else 0)) ∧
    (∀ a : ℤ → ℂ, a 0 = 0 →
      (∀ k : ℤ, fractionalLaplacianCoeffs unitLength ((1 - s.val) / 2) a k =
        (rieszConstant s : ℂ) * ((1 : ℂ) - if k = 0 then 1 else 0)) →
      a = fun j : ℤ => fourierCoeff (fun x : UnitAddCircle => (rieszRepresentative s x : ℂ)) j) ∧
    (∀ x : ℝ, 0 < x → x < 1 →
      rieszRepresentative s x = (hurwitzZetaPos (s.val : ℂ) x).re +
        (hurwitzZetaPos (s.val : ℂ) (1 - x)).re) :=
  ⟨fourierCoeff_rieszRepresentative s, fundamental_equation s, fundamental_unique s,
    fun _ hx0 hx1 => rieszRepresentative_eq_hurwitzZetaPos s hx0 hx1⟩

end Riesz1

end
