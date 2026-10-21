/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleFourierPairing
public import Riesz1.Bridges.ExplicitFormulasCentred

/-!
# Fourier comparison for finite sums with a common rotation

Parseval compares the square masses of finite sums of translates when
the original Fourier coefficients are dominated mode by mode. The same
offsets occur on both sides, so their Fourier factors are identical.
-/

public section

open MeasureTheory

namespace Riesz1

/-- Modewise Fourier domination survives any finite sum of translates
with a common rotation. No separation of the offsets is required. -/
theorem integral_sq_sum_translate_le_of_circleCoeff
    {ι : Type*} [Fintype ι] (a : ι → UnitAddCircle)
    (f g : UnitAddCircle → ℝ)
    (hf : MemLp (fun z => (f z : ℂ)) 2 volume)
    (hg : MemLp (fun z => (g z : ℂ)) 2 volume)
    (D : ℝ) (_hD : 0 ≤ D)
    (hc : ∀ k : ℤ, ‖circleCoeff f k‖^2 ≤ D*‖circleCoeff g k‖^2) :
    (∫ z : UnitAddCircle, (∑ i, f (z+a i))^2) ≤
      D*∫ z : UnitAddCircle, (∑ i, g (z+a i))^2 := by
  classical
  have shift (u : UnitAddCircle → ℝ)
      (hu : MemLp (fun z => (u z : ℂ)) 2 volume) (i : ι) :
      MemLp (fun z => (u (z+a i) : ℂ)) 2 volume :=
    hu.comp_measurePreserving (measurePreserving_add_right volume (a i))
  have sumLp (u : UnitAddCircle → ℝ)
      (hu : MemLp (fun z => (u z : ℂ)) 2 volume) :
      MemLp (fun z => ((∑ i, u (z+a i) : ℝ) : ℂ)) 2 volume := by
    simp_rw [Complex.ofReal_sum]
    exact memLp_finsetSum Finset.univ fun i _ => shift u hu i
  have coeff (u : UnitAddCircle → ℝ)
      (hu : MemLp (fun z => (u z : ℂ)) 2 volume) (k : ℤ) :
      circleCoeff (fun z => ∑ i, u (z+a i)) k =
        (∑ i, fourier (-k) (-a i))*circleCoeff u k := by
    unfold circleCoeff
    simp_rw [Complex.ofReal_sum]
    have he := congrFun (fourierCoeff.sum Finset.univ
      (fun i z => (u (z+a i) : ℂ)) (fun i _ => by
        rw [← volume_unitAddCircle_eq_haar]
        exact (shift u hu i).integrable one_le_two)) k
    have hs (i : ι) : fourierCoeff (fun z => (u (z+a i) : ℂ)) k =
        fourier (-k) (-a i)*fourierCoeff (fun z => (u z : ℂ)) k :=
      fourierCoeff_add_centre (fun z => (u z : ℂ)) (a i) k
    simpa only [Finset.sum_fn, hs, Finset.sum_mul] using he
  have hs := hasSum_norm_sq_circleCoeff (fun z => ∑ i, f (z+a i)) (sumLp f hf)
  have ht := hasSum_norm_sq_circleCoeff (fun z => ∑ i, g (z+a i)) (sumLp g hg)
  have hb (k : ℤ) :
      ‖circleCoeff (fun z => ∑ i, f (z+a i)) k‖^2 ≤
        D*‖circleCoeff (fun z => ∑ i, g (z+a i)) k‖^2 := by
    rw [coeff f hf, coeff g hg, norm_mul, norm_mul, mul_pow, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left (hc k)
      (sq_nonneg ‖∑ i, fourier (-k) (-a i)‖)]
  have h := hs.summable.tsum_le_tsum hb (ht.summable.mul_left D)
  rw [tsum_mul_left, hs.tsum_eq, ht.tsum_eq] at h
  simpa only [← pow_two] using h

end Riesz1
