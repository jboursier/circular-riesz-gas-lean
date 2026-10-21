/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Tactic

/-!
# Fourier coefficients under dilation of a circle

Normalized Haar coefficients are unchanged by pulling a length-`T` circle back to the
unit circle. Agreement of real lifts on the open central cell suffices, so endpoint
representative conventions have no effect. This is the pullback step of the admissibility
regularity lemma.
-/

public section

open MeasureTheory Set intervalIntegral

namespace Riesz1.CircleFourier

/-- Corresponding Fourier characters agree after dilation of their real lifts. -/
theorem fourier_dilation {T : ℝ} (hT : T ≠ 0) (k : ℤ) (t : ℝ) :
    fourier (-k) (t : UnitAddCircle) = fourier (-k) ((T * t : ℝ) : AddCircle T) := by
  simp only [fourier_coe_apply]
  congr 1
  push_cast
  field_simp [hT]

/-- Normalized coefficients are invariant under dilation. Values at the two endpoints
of the fundamental cell are immaterial. -/
theorem coeff_eq_of_scaled_lifts {T : ℝ} [hT : Fact (0 < T)]
    {f : AddCircle T → ℂ} {g : UnitAddCircle → ℂ}
    (hfg : ∀ t ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2),
      g (t : UnitAddCircle) = f ((T * t : ℝ) : AddCircle T)) (k : ℤ) :
    fourierCoeff g k = fourierCoeff f k := by
  rw [fourierCoeff_eq_intervalIntegral g k (-(1 / 2 : ℝ)),
    fourierCoeff_eq_intervalIntegral f k (-(T / 2))]
  simp only [div_one, one_smul]
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, show -(T / 2) + T = T / 2 by ring]
  have heq : (∫ t in (-(1 / 2 : ℝ))..(1 / 2), fourier (-k) (t : UnitAddCircle) •
      g (t : UnitAddCircle)) =
      ∫ t in (-(1 / 2 : ℝ))..(1 / 2),
        (fun u : ℝ => fourier (-k) (u : AddCircle T) • f (u : AddCircle T)) (T * t) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    dsimp only
    rw [hfg t ht, fourier_dilation hT.out.ne']
  rw [heq, intervalIntegral.integral_comp_mul_left (fun u : ℝ => fourier (-k) (u : AddCircle T) • f (u : AddCircle T)) hT.out.ne']
  simp only [one_div]
  congr 2
  ring

end Riesz1.CircleFourier
