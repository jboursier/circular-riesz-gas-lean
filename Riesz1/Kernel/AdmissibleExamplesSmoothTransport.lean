/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.FourierFiniteRegularity
public import Riesz1.Frozen.TransportCoeffs

/-!
# Twice continuously differentiable transports of cubic-decay profiles

A tool for the distance-power construction. Once the seam
corner is removed, cubic Fourier decay makes the second transport derivative an
absolutely convergent Fourier series.
-/

public section

open MeasureTheory Set Filter Topology ComplexConjugate
open scoped ContDiff

namespace Riesz1
namespace Internal

/-- A real sequence with decay strictly faster than cubic has a real `C²` Fourier sum. -/
lemma exists_real_C2_of_coeff_decay {c : ℤ → ℂ} {g K : ℝ}
    (hg : g < -3) (_hK : 0 ≤ K)
    (hb : ∀ k : ℤ, ‖c k‖ ≤ K * |(k : ℝ)| ^ g)
    (hsym : ∀ k, conj (c k) = c (-k)) :
    ∃ G : UnitAddCircle → ℝ, Continuous G ∧
      (∀ k, fourierCoeff (fun x => (G x : ℂ)) k = c k) ∧
      ContDiff ℝ 2 (fun x : ℝ => G (x : UnitAddCircle)) ∧
      ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ,
        |deriv (deriv (fun y : ℝ => G (y : UnitAddCircle))) x| ≤ B := by
  apply exists_real_C2_fourierSeries c _ hsym
  intro m hm
  have hmg : (m : ℝ) + g < -1 := by
    have hmR : (m : ℝ) ≤ 2 := by exact_mod_cast hm
    linarith
  have hs : Summable fun k : ℤ => |(k : ℝ)| ^ ((m : ℝ) + g) := by
    convert Real.summable_abs_int_rpow (show 1 < -((m : ℝ) + g) by linarith) using 1
    ext k
    congr 1
    ring
  apply Summable.of_nonneg_of_le (fun k => by positivity) _ (hs.mul_left K)
  intro k
  calc
    |(k : ℝ)| ^ m * ‖c k‖ ≤ |(k : ℝ)| ^ m * (K * |(k : ℝ)| ^ g) := by
      gcongr
      exact hb k
    _ = K * |(k : ℝ)| ^ ((m : ℝ) + g) := by
      by_cases hk : k = 0
      · subst k
        simp only [Int.cast_zero, abs_zero, Real.zero_rpow (by linarith : g ≠ 0),
          Real.zero_rpow (by linarith : (m : ℝ) + g ≠ 0), mul_zero]
      · rw [Real.rpow_add (abs_pos.mpr (by exact_mod_cast hk)), Real.rpow_natCast]
        ring

/-- A real profile with cubic Fourier decay has a globally `C²`, mean-zero transport
with the coefficients `transportCoeffs` and a bounded second derivative. -/
lemma exists_C2_transport_of_cubic_decay (P : Parameters) {f : UnitAddCircle → ℝ}
    (hf : MemLp (fun x => (f x : ℂ)) 2 volume) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ k : ℤ, k ≠ 0 →
      ‖fourierCoeff (fun x => (f x : ℂ)) k‖ ≤ K * |(k : ℝ)| ^ (-3 : ℝ)) :
    ∃ G : UnitAddCircle → ℝ, Continuous G ∧
      (∀ k, fourierCoeff (fun x => (G x : ℂ)) k =
        transportCoeffs P unitLength ⟨f, hf⟩ k) ∧
      ContDiff ℝ 2 (fun x : ℝ => G (x : UnitAddCircle)) ∧
      ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ,
        |deriv (deriv (fun y : ℝ => G (y : UnitAddCircle))) x| ≤ B := by
  let D := 2 * P.val.1 * rieszConstant (parametersExponent P)
  have hD : 0 < D := by dsimp [D]; positivity [P.2.1, rieszConstant_pos (parametersExponent P)]
  let A := (2 * Real.pi) ^ (1 - P.val.2) / (D * (2 * Real.pi))
  have hA : 0 < A := by dsimp [A]; positivity
  apply exists_real_C2_of_coeff_decay (g := -3 - P.val.2) (K := A * K)
    (by linarith [P.2.2.1]) (mul_nonneg hA.le hK)
  · intro k
    by_cases hk : k = 0
    · simp [transportCoeffs, hk, Real.zero_rpow (by linarith [P.2.2.1] : -3 - P.val.2 ≠ 0)]
    · have hkp : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
      simp only [transportCoeffs, hk, ↓reduceIte]
      change ‖-((|2 * Real.pi * (k : ℝ) / 1| ^ (1 - P.val.2) : ℝ) : ℂ) /
        ((D : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ) / 1)) *
        fourierCoeff (fun x => (f x : ℂ)) k‖ ≤ _
      simp only [norm_mul, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
        Complex.norm_ofNat, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one,
        Complex.norm_intCast, div_one, abs_of_pos hD]
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos,
        Real.mul_rpow (by positivity) hkp.le]
      calc
        ((2 * Real.pi) ^ (1 - P.val.2) * |(k : ℝ)| ^ (1 - P.val.2)) /
            (D * (2 * Real.pi * |(k : ℝ)|)) * ‖fourierCoeff (fun x => (f x : ℂ)) k‖
          ≤ ((2 * Real.pi) ^ (1 - P.val.2) * |(k : ℝ)| ^ (1 - P.val.2)) /
            (D * (2 * Real.pi * |(k : ℝ)|)) * (K * |(k : ℝ)| ^ (-3 : ℝ)) := by
              gcongr
              exact hb k hk
        _ = A * K * |(k : ℝ)| ^ (-3 - P.val.2) := by
          dsimp [A]
          rw [show 1 - P.val.2 = (-P.val.2) + 1 by ring, Real.rpow_add hkp,
            Real.rpow_one, show -3 - P.val.2 = (-P.val.2) + (-3) by ring,
            Real.rpow_add hkp]
          field_simp
  · intro k
    by_cases hk : k = 0
    · simp [hk, transportCoeffs]
    · simp only [transportCoeffs, hk, neg_ne_zero.mpr hk, ↓reduceIte, coeff,
        unitLength, map_mul, map_div₀, map_neg, Complex.conj_ofReal, Complex.conj_I,
        map_ofNat, map_intCast, Int.cast_neg, div_one, conj_fourierCoeff_real, mul_neg, abs_neg]
      congr 2
      ring

end Internal
end Riesz1
