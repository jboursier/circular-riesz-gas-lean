/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibleExamplesSobolev
public import Riesz1.Kernel.ExplicitFormulasPower
public import Riesz1.Kernel.AdmissibilityRegularityVariance

/-!
# Sharp Fourier obstruction for Riesz power profiles

Exact Riesz coefficients give the sharp
Sobolev obstruction, including the critical exponent. The transfer from this kernel
to a power of circle distance is a separate step.
-/

public section

open MeasureTheory

namespace Riesz1

namespace Internal

/-- A positive power-law lower bound on the positive Fourier modes forces the sharp
necessary exponent for finite Sobolev energy. -/
lemma sobolev_exponent_lt_of_coeff_lower_bound {r g K : ℝ} (hK : 0 < K)
    {f : UnitAddCircle → ℂ} (h : CircleSobolev r f)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → K * (n : ℝ) ^ g ≤ ‖fourierCoeff f (n : ℤ)‖) :
    2 * r + 2 * g < -1 := by
  have hs := (summable_circleSobolev_summand h).comp_injective
    (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℤ)))
  have hp : Summable (fun n : ℕ => if n = 0 then (0 : ℝ)
      else K ^ 2 * (n : ℝ) ^ (2 * r + 2 * g)) := by
    refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_) hs
    by_cases hn : n = 0
    · simp [hn]
    · have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      simp only [Function.comp_apply, Nat.cast_eq_zero, hn, ↓reduceIte, Int.cast_natCast,
        abs_of_pos hnR]
      calc K ^ 2 * (n : ℝ) ^ (2 * r + 2 * g)
          = (n : ℝ) ^ (2 * r) * (K * (n : ℝ) ^ g) ^ 2 := by
            rw [mul_pow, rpow_sq_eq_rpow_two_mul hnR.le, Real.rpow_add hnR]
            ring
        _ ≤ (n : ℝ) ^ (2 * r) * ‖fourierCoeff f (n : ℤ)‖ ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (hcoeff n hn) 2) (by positivity)
  have hp' : Summable (fun n : ℕ => if n = 0 then (0 : ℝ)
      else (n : ℝ) ^ (2 * r + 2 * g)) := by
    convert hp.mul_left (K ^ 2)⁻¹ using 1
    funext n
    split_ifs <;> simp [hK.ne']
  have ht : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (2 * r + 2 * g)) := by
    simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte] using
      (summable_nat_add_iff 1).mpr hp'
  exact Real.summable_nat_rpow.mp ((summable_nat_add_iff 1).mp ht)

/-- The Riesz coefficient norm is an exact positive constant times a power of the index. -/
lemma norm_fourierCoeff_riesz_nat (a : RieszExponent) {n : ℕ} (hn : n ≠ 0) :
    ‖fourierCoeff (fun x : UnitAddCircle => (rieszRepresentative a x : ℂ)) (n : ℤ)‖ =
      (rieszConstant a * (2 * Real.pi) ^ (a.val - 1)) * (n : ℝ) ^ (a.val - 1) := by
  rw [fourierCoeff_rieszRepresentative]
  simp only [Nat.cast_eq_zero, hn, ↓reduceIte, Int.cast_natCast,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (mul_pos (rieszConstant_pos a) (by positivity)),
    Real.mul_rpow (by positivity) (Nat.cast_nonneg n)]
  ring

/-- Any finite Sobolev energy of a Riesz kernel forces the strict spectral threshold. -/
theorem riesz_sobolev_exponent_lt (a : RieszExponent) {r : ℝ}
    (h : CircleSobolev r (fun x => (rieszRepresentative a x : ℂ))) :
    r < 1 / 2 - a.val := by
  have hK : 0 < rieszConstant a * (2 * Real.pi) ^ (a.val - 1) :=
    mul_pos (rieszConstant_pos a) (by positivity)
  have hh := Internal.sobolev_exponent_lt_of_coeff_lower_bound hK h
    (fun n hn => (Internal.norm_fourierCoeff_riesz_nat a hn).ge)
  linarith

end Internal

/-- A subcritical Riesz kernel belongs to the Sobolev space of order `(1 - s) / 2`. -/
theorem circleSobolev_riesz_of_lt (s a : RieszExponent) (ha : a.val < s.val / 2) :
    CircleSobolev ((1 - s.val) / 2) (fun x => (rieszRepresentative a x : ℂ)) := by
  obtain ⟨hL2, _, hfin⟩ := explicit_formulas_power s a ha 1 zero_lt_one
  exact ⟨hL2, lt_top_iff_ne_top.mpr (hfin hL2).1⟩

/-- Exact Sobolev threshold for the Riesz kernel, including exclusion at `a = s/2`.
This is the kernel part of the power argument. -/
theorem circleSobolev_riesz_iff (s a : RieszExponent) :
    CircleSobolev ((1 - s.val) / 2) (fun x => (rieszRepresentative a x : ℂ)) ↔
      a.val < s.val / 2 := by
  constructor
  · intro h
    have hh := Internal.riesz_sobolev_exponent_lt a h
    linarith
  · exact circleSobolev_riesz_of_lt s a

end Riesz1
