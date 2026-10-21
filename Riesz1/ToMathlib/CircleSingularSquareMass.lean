/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleSingularMass
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Square mass of a finite singular envelope

The estimate integrates the positive-exponent envelope used by
Lemma 5.3, with constants before the circle, set, marks and test.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

/-- An envelope with exponent below one half has uniformly bounded local
square mass. No separation of the marks or boundedness of the test is needed. -/
theorem lintegral_circle_sq_le_of_singular_envelope {L α h A B : ℝ}
    [Fact (0 < L)] (hα0 : 0 ≤ α) (hα1 : α < 1/2) (hh : 0 < h)
    (_hA : 0 ≤ A) (hB : 0 ≤ B) (m : ℕ) (a : Fin m → AddCircle L)
    (S : Set (AddCircle L)) (hS : volume S ≤ ENNReal.ofReal (B*h))
    (e : AddCircle L → ℝ)
    (he : ∀ᵐ x ∂volume.restrict S,
      |e x| ≤ A * (h^(-α) + ∑ j, dist x (a j)^(-α))) :
    (∫⁻ x in S, ENNReal.ofReal (e x ^ 2)) ≤
      ENNReal.ofReal (A^2 * ((m : ℝ)+1) *
        (B + (m : ℝ)*(2/(1-(2*α))+B)) * h^(1-(2*α))) := by
  classical
  have hden : 0 < 1-2*α := by linarith
  have hpow (t : ℝ) (ht : 0 ≤ t) : (t^(-α))^2 = t^(-(2*α)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    congr 1
    ring
  have hpt : ∀ᵐ x ∂volume.restrict S,
      ENNReal.ofReal (e x ^ 2) ≤
        ENNReal.ofReal (A^2*((m : ℝ)+1)) *
          (ENNReal.ofReal (h^(-(2*α))) + ∑ j, ENNReal.ofReal (dist x (a j)^(-(2*α)))) := by
    filter_upwards [he] with x hx
    have hs : (h^(-α) + ∑ j, dist x (a j)^(-α))^2 ≤
        ((m : ℝ)+1)*((h^(-α))^2 + ∑ j, (dist x (a j)^(-α))^2) := by
      have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun j : Fin (m+1) => (Fin.cases (h^(-α)) (fun k : Fin m => dist x (a k)^(-α)) j : ℝ))
      simpa only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, Finset.card_univ,
        Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hh
    have hsq : e x ^ 2 ≤ A^2*((m : ℝ)+1) *
        (h^(-(2*α)) + ∑ j, dist x (a j)^(-(2*α))) := by
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hx 2
      rw [sq_abs, mul_pow] at hsq
      apply hsq.trans
      have hs' := mul_le_mul_of_nonneg_left hs (sq_nonneg A)
      simpa only [hpow h hh.le, hpow _ dist_nonneg, mul_assoc] using hs'
    have hnn (j : Fin m) : 0 ≤ dist x (a j)^(-(2*α)) := Real.rpow_nonneg dist_nonneg _
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hnn j),
      ← ENNReal.ofReal_add (Real.rpow_nonneg hh.le _) (Finset.sum_nonneg fun j _ => hnn j),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ A^2*((m : ℝ)+1))]
    exact ENNReal.ofReal_le_ofReal hsq
  have hsing (j : Fin m) : (∫⁻ x in S, ENNReal.ofReal (dist x (a j)^(-(2*α)))) ≤
      ENNReal.ofReal ((2/(1-(2*α))+B)*h^(1-(2*α))) := by
    exact lintegral_circle_rpow_le_of_measure_le (by linarith : 0 ≤ 2*α)
      (by linarith : 2*α < 1) hh hB (a j) S hS
  have hconst : ENNReal.ofReal (h^(-(2*α))) * volume S ≤
      ENNReal.ofReal (B*h^(1-(2*α))) := by
    apply (mul_le_mul_of_nonneg_left hS zero_le).trans_eq
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hh.le _)]
    congr 1
    calc
      _ = B * (h^(-(2*α))*h^(1 : ℝ)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hh]; congr 2; ring
  calc
    _ ≤ ∫⁻ x in S, ENNReal.ofReal (A^2*((m : ℝ)+1)) *
        (ENNReal.ofReal (h^(-(2*α))) + ∑ j, ENNReal.ofReal (dist x (a j)^(-(2*α)))) :=
      lintegral_mono_ae hpt
    _ = ENNReal.ofReal (A^2*((m : ℝ)+1)) *
        (ENNReal.ofReal (h^(-(2*α))) * volume S +
          ∑ j, ∫⁻ x in S, ENNReal.ofReal (dist x (a j)^(-(2*α)))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const,
        lintegral_const, Measure.restrict_apply_univ, lintegral_finsetSum']
      exact fun j _ => ((by fun_prop : Measurable (fun x : AddCircle L => dist x (a j))).pow_const
        (-(2*α))).ennreal_ofReal.aemeasurable
    _ ≤ ENNReal.ofReal (A^2*((m : ℝ)+1)) *
        (ENNReal.ofReal (B*h^(1-(2*α))) +
          ∑ _j : Fin m, ENNReal.ofReal ((2/(1-(2*α))+B)*h^(1-(2*α)))) := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      exact add_le_add hconst (Finset.sum_le_sum fun j _ => hsing j)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_mul (Nat.cast_nonneg m),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ A^2*((m : ℝ)+1))]
      congr 1
      ring

end Riesz1
