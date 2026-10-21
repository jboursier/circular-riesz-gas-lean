/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZeta

/-!
# Reality of the even Hurwitz zeta function

Conjugation commutes with the real theta-kernel Mellin construction, including
Mathlib's assigned values at the poles. This proves the real-valuedness claim
in Lemma 2.1 without a restriction on the real exponent.
-/

public section

open Set MeasureTheory Complex
open scoped ComplexConjugate

namespace Riesz1

private lemma modifiedKernel_conj (a : UnitAddCircle) (t : ℝ) :
    conj ((HurwitzZeta.hurwitzEvenFEPair a).f_modif t) =
      (HurwitzZeta.hurwitzEvenFEPair a).f_modif t := by
  by_cases ht1 : t ∈ Ioi (1 : ℝ) <;>
    by_cases ht2 : t ∈ Ioo (0 : ℝ) 1 <;>
    by_cases ha : a = 0 <;>
    simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair,
      ht1, ht2, ha, Function.comp_def]

private lemma completedEvenEntire_conj (a : UnitAddCircle) (z : ℂ) :
    HurwitzZeta.completedHurwitzZetaEven₀ a (conj z) =
      conj (HurwitzZeta.completedHurwitzZetaEven₀ a z) := by
  simp only [HurwitzZeta.completedHurwitzZetaEven₀, WeakFEPair.Λ₀, mellin,
    smul_eq_mul, map_div₀, map_ofNat, ← integral_conj]
  apply congrArg (fun w : ℂ => w / 2)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [map_mul, modifiedKernel_conj]
  congr 1
  rw [show conj z / 2 - 1 = conj (z / 2 - 1) by
    simp only [map_sub, map_div₀, map_ofNat, map_one]]
  rw [Complex.cpow_conj _ _ (by
    rw [Complex.arg_ofReal_of_nonneg ht.le]
    exact Real.pi_pos.ne), conj_ofReal]

/-- The completed even Hurwitz zeta function commutes with conjugation. -/
lemma completedHurwitzZetaEven_conj (a : UnitAddCircle) (z : ℂ) :
    HurwitzZeta.completedHurwitzZetaEven a (conj z) =
      conj (HurwitzZeta.completedHurwitzZetaEven a z) := by
  simp only [HurwitzZeta.completedHurwitzZetaEven_eq, completedEvenEntire_conj,
    map_sub, map_div₀, map_one]
  by_cases ha : a = 0 <;> simp [ha]

/-- The even Hurwitz zeta function commutes with conjugation. -/
lemma hurwitzZetaEven_conj (a : UnitAddCircle) (z : ℂ) :
    HurwitzZeta.hurwitzZetaEven a (conj z) = conj (HurwitzZeta.hurwitzZetaEven a z) := by
  rcases eq_or_ne z 0 with rfl | hz
  · by_cases ha : a = 0 <;> simp only [map_zero, HurwitzZeta.hurwitzZetaEven_apply_zero, ha,
      ite_true, ite_false, map_div₀, map_neg, map_one, map_ofNat, map_zero]
  · rw [HurwitzZeta.hurwitzZetaEven_def_of_ne_or_ne (Or.inr (by simpa using hz)),
      HurwitzZeta.hurwitzZetaEven_def_of_ne_or_ne (Or.inr hz), map_div₀,
      completedHurwitzZetaEven_conj, Complex.Gammaℝ_conj]

/-- The even Hurwitz zeta function is real on real exponents
(Lemma 2.1), including the assigned value at `1`. -/
theorem hurwitzZetaEven_ofReal_im (a : UnitAddCircle) (s : ℝ) :
    (HurwitzZeta.hurwitzZetaEven a (s : ℂ)).im = 0 := by
  have h := congrArg Complex.im (hurwitzZetaEven_conj a (s : ℂ))
  simp only [conj_ofReal, conj_im] at h
  linarith

end Riesz1
