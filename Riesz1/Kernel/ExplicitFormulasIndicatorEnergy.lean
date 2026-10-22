/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.CircleSobolevSq
public import Riesz1.Kernel.ExplicitFormulasIndicatorTransport

/-!
# The centred arc indicator and its Fourier coefficients

The centred arc indicator `ξ = 1_{(-a,a)} - 2a` on the circle, with its `L²` membership and its
Fourier coefficients `sin(2πka)/(πk)`. The transport coefficients of `ξ` are the explicit ones.
The energy identity is proved in `ExplicitFormulasIndicatorLimit`, by mollification.
-/

public section

open MeasureTheory Set Filter Topology
open scoped Real Interval

namespace Riesz1

/-- The centred arc indicator `1_{(-a,a)} - 2a` on the circle, with mean zero. -/
@[expose] noncomputable def centeredIndicatorArc (a : ℝ) (t : UnitAddCircle) : ℝ :=
  indicatorArc a t - 2 * a

/-- The Haar measure is the volume on the circle of length one. -/
lemma volume_eq_haar_circle : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

lemma integrable_indicatorArc (a : ℝ) :
    Integrable (fun t : UnitAddCircle => (indicatorArc a t : ℂ)) AddCircle.haarAddCircle := by
  rw [← volume_eq_haar_circle]
  exact (memLp_indicatorArc a).integrable one_le_two

lemma centeredIndicatorArc_eq (a : ℝ) :
    (fun t : UnitAddCircle => (centeredIndicatorArc a t : ℂ)) =
      fun t => (indicatorArc a t : ℂ) - ((2 * a : ℝ) : ℂ) := by
  funext t
  simp [centeredIndicatorArc]

lemma memLp_centeredIndicatorArc (a : ℝ) :
    MemLp (fun t : UnitAddCircle => (centeredIndicatorArc a t : ℂ)) 2 volume := by
  rw [centeredIndicatorArc_eq]
  exact (memLp_indicatorArc a).sub (memLp_const _)

/-- The Fourier coefficients of the centred arc indicator: zero at `k = 0`, and
`sin(2πka)/(πk)` for `k ≠ 0`. -/
lemma fourierCoeff_centeredIndicatorArc {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (k : ℤ) :
    fourierCoeff (fun t : UnitAddCircle => (centeredIndicatorArc a t : ℂ)) k =
      if k = 0 then 0 else ((Real.sin (2 * Real.pi * k * a) / (Real.pi * k) : ℝ) : ℂ) := by
  rw [centeredIndicatorArc_eq, fourierCoeff_sub_const (integrable_indicatorArc a),
    fourierCoeff_indicatorArc ha0 ha1, fourierCoeff_one]
  by_cases hk : k = 0
  · subst hk
    simp
  · simp [hk]

/-- The coefficients of the transport of the centred indicator are the explicit ones. -/
lemma transportCoeffs_centered (s : RieszExponent) (β a : ℝ) (hβ : 0 < β) (ha0 : 0 < a)
    (ha1 : a < 1 / 2) (k : ℤ) :
    transportCoeffs ⟨(β, s.val), hβ, s.2.1, s.2.2⟩ ⟨1, one_pos⟩
        ⟨centeredIndicatorArc a, memLp_centeredIndicatorArc a⟩ k =
      transportSeriesCoeff s.val β a k := by
  by_cases hk : k = 0
  · subst hk
    rw [transportSeriesCoeff_zero s.val s.2.1 β a]
    simp [transportCoeffs]
  · rw [transportSeriesCoeff_eq s β a hβ k hk]
    dsimp only [transportCoeffs, coeff]
    rw [fourierCoeff_centeredIndicatorArc ha0 ha1 k]
    simp only [hk, ↓reduceIte, div_one, Complex.ofReal_one]
    rfl

end Riesz1

end
