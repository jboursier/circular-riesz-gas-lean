/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.RieszRepresentative
public import Riesz1.Frozen.RieszConstant
public import Riesz1.ToMathlib.HurwitzKernel.Mean

/-!
# Integrability and the zero Fourier mode of the Riesz kernel

These results transfer the Hurwitz kernel's integrability and mean zero to
the Riesz representative. The measure in `fourierCoeff` agrees with volume
on the unit circle.
-/

public section

open MeasureTheory Complex
open scoped ComplexConjugate

namespace Riesz1

/-- The Riesz representative is integrable, including its assigned
value at the collision. -/
theorem integrable_rieszRepresentative (s : RieszExponent) :
    Integrable (rieszRepresentative s) := by
  exact (integrable_hurwitzZetaEven_re s.val s.property.1 s.property.2).const_mul 2

/-- The Riesz representative has zero mean. -/
theorem integral_rieszRepresentative (s : RieszExponent) :
    ∫ x : UnitAddCircle, rieszRepresentative s x = 0 := by
  simp only [rieszRepresentative, integral_const_mul,
    integral_hurwitzZetaEven_re s.val s.property.1 s.property.2, mul_zero]

/-- Integrability of the complex representative used by Fourier coefficients. -/
theorem integrable_rieszRepresentative_complex (s : RieszExponent) :
    Integrable (fun x : UnitAddCircle => (rieszRepresentative s x : ℂ)) :=
  (integrable_rieszRepresentative s).ofReal

/-- The zero Fourier coefficient of the Riesz kernel vanishes. -/
theorem fourierCoeff_rieszRepresentative_zero (s : RieszExponent) :
    fourierCoeff (fun x : UnitAddCircle => (rieszRepresentative s x : ℂ)) 0 = 0 := by
  simp only [fourierCoeff, neg_zero, fourier_zero, one_smul]
  rw [show (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))).symm]
  rw [integral_complex_ofReal, integral_rieszRepresentative, ofReal_zero]

/-- The representative is even on the circle, including the collision value. -/
theorem rieszRepresentative_neg (s : RieszExponent) (x : UnitAddCircle) :
    rieszRepresentative s (-x) = rieszRepresentative s x := by
  simp only [rieszRepresentative, HurwitzZeta.hurwitzZetaEven_neg]

/-- Real-valuedness removes the real-part operation in the definition. -/
theorem rieszRepresentative_complex_eq (s : RieszExponent) (x : UnitAddCircle) :
    (rieszRepresentative s x : ℂ) = 2 * HurwitzZeta.hurwitzZetaEven x (s.val : ℂ) := by
  apply Complex.ext <;> simp [rieszRepresentative, hurwitzZetaEven_ofReal_im]

/-- The positive and negative Fourier modes coincide. -/
theorem fourierCoeff_rieszRepresentative_neg (s : RieszExponent) (k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => (rieszRepresentative s x : ℂ)) (-k) =
      fourierCoeff (fun x : UnitAddCircle => (rieszRepresentative s x : ℂ)) k := by
  simp only [fourierCoeff, neg_neg, smul_eq_mul]
  rw [← integral_neg_eq_self
    (fun x : UnitAddCircle => fourier k x * (rieszRepresentative s x : ℂ))
    AddCircle.haarAddCircle]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp only [rieszRepresentative_neg, fourier_apply, smul_neg, neg_smul]

/-- Every Fourier coefficient of the Riesz representative is real. -/
theorem fourierCoeff_rieszRepresentative_im (s : RieszExponent) (k : ℤ) :
    (fourierCoeff (fun x : UnitAddCircle => (rieszRepresentative s x : ℂ)) k).im = 0 := by
  have hc : conj (fourierCoeff (fun x : UnitAddCircle => (rieszRepresentative s x : ℂ)) k) =
      fourierCoeff (fun x : UnitAddCircle => (rieszRepresentative s x : ℂ)) (-k) := by
    simp only [fourierCoeff, ← integral_conj, smul_eq_mul, map_mul, conj_ofReal,
      neg_neg, ← fourier_neg]
  rw [fourierCoeff_rieszRepresentative_neg] at hc
  have hi := congrArg Complex.im hc
  simp only [conj_im] at hi
  linarith

end Riesz1
