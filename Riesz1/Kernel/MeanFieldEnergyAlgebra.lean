/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.TransportCoeffs
public import Riesz1.Frozen.ParametersExponent
public import Riesz1.Frozen.RieszConstant
public import Riesz1.Frozen.Profile
public import Riesz1.Frozen.Length
public import Riesz1.Kernel.MeanFieldEnergyFourier

/-!
# Algebra of the transport coefficients

For `k ≠ 0` the transport coefficient of a profile `ξ` on the unit circle is
`c k = -(2π|k|)^{1-s} / (2βc_s · 2π i k) · ξ̂ k`, where `ξ̂ k` is the Fourier coefficient of `ξ`.
This file records the modulus of `c k`, the cross term `conj(2π i k ξ̂) c`
that appears in `∫ ξ' ψ`, and the bound `k² |c k|² ≤ (|ξ̂ k|² + |2π i k ξ̂ k|²) / (4π² (2βc_s)²)`
that gives the finiteness of the second moment of the transport. These identities feed the
mean-field energy identity.
-/

public section

open MeasureTheory Set Complex Filter Topology
open scoped Real ComplexConjugate

namespace Riesz1

/-- The transport coefficient for a nonzero frequency, written with the Fourier coefficient
`z = ξ̂ k` of the profile. -/
lemma transportCoeffs_of_ne (P : Parameters) (ξ : Profile) {k : ℤ} (hk : k ≠ 0) :
    transportCoeffs P ⟨1, one_pos⟩ ξ k =
      -(((|2 * π * (k : ℝ)|) ^ (1 - P.val.2) : ℝ) : ℂ) /
        (((2 * P.val.1 * rieszConstant (parametersExponent P)) : ℝ) * (2 * π * I * (k : ℂ))) *
        fourierCoeff (fun x : UnitAddCircle => (ξ.val x : ℂ)) k := by
  simp only [transportCoeffs, hk, ite_false, coeff, Complex.ofReal_one, div_one]

/-- The complex number `2 π i k` for an integer `k`, written as a real multiple of `i`. -/
lemma two_pi_I_mul_eq (k : ℤ) : (2 * π * I * (k : ℂ)) = ((2 * π * (k : ℝ) : ℝ) : ℂ) * I := by
  push_cast
  ring

/-- The modulus of a transport coefficient for a nonzero frequency. -/
lemma norm_transport_term (β cs s : ℝ) (hβ : 0 < β) (hcs : 0 < cs) {k : ℤ} (hk : k ≠ 0) (z : ℂ) :
    ‖-(((|2 * π * (k : ℝ)|) ^ (1 - s) : ℝ) : ℂ) /
        (((2 * β * cs) : ℝ) * (2 * π * I * (k : ℂ))) * z‖ =
      (|2 * π * (k : ℝ)|) ^ (1 - s) / ((2 * β * cs) * |2 * π * (k : ℝ)|) * ‖z‖ := by
  have ht : 0 < |2 * π * (k : ℝ)| := abs_pos.mpr (mul_ne_zero (mul_ne_zero two_ne_zero
    Real.pi_ne_zero) (by exact_mod_cast hk))
  have hw : ‖(2 * π * I * (k : ℂ))‖ = |2 * π * (k : ℝ)| := by
    rw [two_pi_I_mul_eq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hY : ‖((2 * β * cs : ℝ) : ℂ)‖ = 2 * β * cs := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hX : ‖(((|2 * π * (k : ℝ)|) ^ (1 - s) : ℝ) : ℂ)‖ = (|2 * π * (k : ℝ)|) ^ (1 - s) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  rw [norm_mul, norm_div, norm_neg, hX, norm_mul, hY, hw]

/-- The cross term `conj(2π i k ξ̂) c` of the transport, a nonnegative real number. -/
lemma re_conj_mul_transport (β cs s : ℝ) (hβ : 0 < β) (hcs : 0 < cs) {k : ℤ} (hk : k ≠ 0)
    (z : ℂ) :
    (conj (2 * π * I * (k : ℂ) * z) *
      (-(((|2 * π * (k : ℝ)|) ^ (1 - s) : ℝ) : ℂ) /
        (((2 * β * cs) : ℝ) * (2 * π * I * (k : ℂ))) * z)).re =
      (|2 * π * (k : ℝ)|) ^ (1 - s) * ‖z‖ ^ 2 / (2 * β * cs) := by
  have hw : (2 * π * I * (k : ℂ)) ≠ 0 := by
    rw [two_pi_I_mul_eq]
    refine mul_ne_zero ?_ Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
      (by exact_mod_cast hk))
  have hconj : conj (2 * π * I * (k : ℂ)) = -(2 * π * I * (k : ℂ)) := by
    rw [two_pi_I_mul_eq, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hnorm : ((‖z‖ : ℝ) : ℂ) ^ 2 = conj z * z := by
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  have hYc : ((2 * β * cs : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hkey : conj (2 * π * I * (k : ℂ) * z) *
      (-(((|2 * π * (k : ℝ)|) ^ (1 - s) : ℝ) : ℂ) /
        (((2 * β * cs) : ℝ) * (2 * π * I * (k : ℂ))) * z) =
      ((((|2 * π * (k : ℝ)|) ^ (1 - s)) * ‖z‖ ^ 2 / (2 * β * cs) : ℝ) : ℂ) := by
    rw [map_mul, hconj]
    push_cast
    rw [hnorm]
    field_simp
  rw [hkey, Complex.ofReal_re]

/-- The square of `t ^ (1 - s)` is at most `1 + t ^ 2` for `t > 0` and `0 < s < 1`. -/
lemma rpow_sq_le_one_add_sq {t s : ℝ} (ht : 0 < t) (hs0 : 0 < s) (hs1 : s < 1) :
    (t ^ (1 - s)) ^ 2 ≤ 1 + t ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  rcases le_total t 1 with h | h
  · have h1 : t ^ ((1 - s) * ((2 : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one ht.le h (by push_cast; nlinarith)
    nlinarith [sq_nonneg t]
  · have h2 : t ^ ((1 - s) * ((2 : ℕ) : ℝ)) ≤ t ^ ((2 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h (by push_cast; linarith)
    rw [Real.rpow_natCast] at h2
    nlinarith [sq_nonneg t]

/-- The energy term identity: for `k ≠ 0`, `β |c_k|² · 8π²k² · c_s |2πk|^{s-1}` equals
`|2πk|^{1-s} |z|² / (2βc_s)`, where `c_k` is the transport coefficient with Fourier coefficient
`z = ξ̂ k`. -/
lemma energy_term_identity (β cs s : ℝ) (hβ : 0 < β) (hcs : 0 < cs) {k : ℤ} (hk : k ≠ 0)
    (z : ℂ) :
    β * ((|2 * π * (k : ℝ)|) ^ (1 - s) / ((2 * β * cs) * |2 * π * (k : ℝ)|) * ‖z‖) ^ 2 *
      (8 * π ^ 2 * (k : ℝ) ^ 2) * (cs * |2 * π * (k : ℝ)| ^ (s - 1)) =
      (|2 * π * (k : ℝ)|) ^ (1 - s) * ‖z‖ ^ 2 / (2 * β * cs) := by
  have ht : 0 < |2 * π * (k : ℝ)| := abs_pos.mpr (mul_ne_zero (mul_ne_zero two_ne_zero
    Real.pi_ne_zero) (by exact_mod_cast hk))
  have hsq : |2 * π * (k : ℝ)| ^ 2 = 4 * π ^ 2 * (k : ℝ) ^ 2 := by
    rw [sq_abs]; ring
  have hpow : |2 * π * (k : ℝ)| ^ (s - 1) = (|2 * π * (k : ℝ)| ^ (1 - s))⁻¹ := by
    rw [← Real.rpow_neg ht.le]
    congr 1
    ring
  have hY : 0 < 2 * β * cs := by positivity
  rw [hpow, show 8 * π ^ 2 * (k : ℝ) ^ 2 = 2 * |2 * π * (k : ℝ)| ^ 2 by rw [hsq]; ring]
  field_simp

/-- The second moment bound: for `k ≠ 0`, `k² |c_k|² ≤ (|z|² + |2πik z|²) / (4π² (2βc_s)²)`. -/
lemma sq_mul_norm_transport_le (β cs s : ℝ) (hβ : 0 < β) (hcs : 0 < cs) (hs0 : 0 < s)
    (hs1 : s < 1) {k : ℤ} (hk : k ≠ 0) (z : ℂ) :
    (k : ℝ) ^ 2 * ‖-(((|2 * π * (k : ℝ)|) ^ (1 - s) : ℝ) : ℂ) /
        (((2 * β * cs) : ℝ) * (2 * π * I * (k : ℂ))) * z‖ ^ 2 ≤
      (‖z‖ ^ 2 + ‖(2 * π * I * (k : ℂ)) * z‖ ^ 2) / (4 * π ^ 2 * (2 * β * cs) ^ 2) := by
  have ht : 0 < |2 * π * (k : ℝ)| := abs_pos.mpr (mul_ne_zero (mul_ne_zero two_ne_zero
    Real.pi_ne_zero) (by exact_mod_cast hk))
  have hsq : |2 * π * (k : ℝ)| ^ 2 = 4 * π ^ 2 * (k : ℝ) ^ 2 := by
    rw [sq_abs]; ring
  have hnI : ‖(2 * π * I * (k : ℂ))‖ = |2 * π * (k : ℝ)| := by
    rw [two_pi_I_mul_eq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  have hw : ‖(2 * π * I * (k : ℂ)) * z‖ = |2 * π * (k : ℝ)| * ‖z‖ := by
    rw [norm_mul, hnI]
  rw [norm_transport_term β cs s hβ hcs hk z, hw]
  have hbound := rpow_sq_le_one_add_sq (t := |2 * π * (k : ℝ)|) ht hs0 hs1
  have hY : 0 < 2 * β * cs := by positivity
  have hd : (k : ℝ) ^ 2 = |2 * π * (k : ℝ)| ^ 2 / (4 * π ^ 2) := by
    rw [hsq]
    field_simp
  have hd' : 0 < 4 * π ^ 2 * (2 * β * cs) ^ 2 := by positivity
  set u := |2 * π * (k : ℝ)| ^ (1 - s) with hu_def
  set t := |2 * π * (k : ℝ)| with ht_def
  set n := ‖z‖ with hn_def
  have hLHS : (k : ℝ) ^ 2 * (u / ((2 * β * cs) * t) * n) ^ 2 = u ^ 2 * n ^ 2 / (4 * π ^ 2 * (2 * β * cs) ^ 2) := by
    rw [hd]
    field_simp
  have hRHS : n ^ 2 + (t * n) ^ 2 = (1 + t ^ 2) * n ^ 2 := by ring
  rw [hLHS, hRHS]
  apply div_le_div_of_nonneg_right _ hd'.le
  exact mul_le_mul_of_nonneg_right hbound (sq_nonneg n)

end Riesz1
