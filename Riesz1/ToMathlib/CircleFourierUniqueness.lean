/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Uniqueness from Fourier coefficients on a circle of arbitrary length

The Fourier basis uses probability Haar measure. The statements here use arclength.
The second result identifies real lifts locally wherever both representatives are continuous.
These facts support the representative-identification step.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace Riesz1.CircleFourier

/-- Equality of all Fourier coefficients determines an arclength-square-integrable function. -/
theorem ae_eq_of_coeff_eq {T : ℝ} [hT : Fact (0 < T)] {f g : AddCircle T → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (h : ∀ k : ℤ, fourierCoeff f k = fourierCoeff g k) : f =ᵐ[volume] g := by
  have hc : ENNReal.ofReal T ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hT.out)
  have hv : AddCircle.haarAddCircle = (ENNReal.ofReal T)⁻¹ •
      (volume : Measure (AddCircle T)) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, smul_smul,
      ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top, one_smul]
  have hf' : MemLp f 2 AddCircle.haarAddCircle := by
    rw [hv]
    exact hf.smul_measure (ENNReal.inv_ne_top.mpr hc)
  have hg' : MemLp g 2 AddCircle.haarAddCircle := by
    rw [hv]
    exact hg.smul_measure (ENNReal.inv_ne_top.mpr hc)
  have heq : fourierBasis.repr (hf'.toLp f) = fourierBasis.repr (hg'.toLp g) := by
    ext k
    rw [fourierBasis_repr, fourierBasis_repr,
      congrFun (fourierCoeff_congr_ae hf'.coeFn_toLp) k,
      congrFun (fourierCoeff_congr_ae hg'.coeFn_toLp) k]
    exact h k
  have heq' := fourierBasis.repr.injective heq
  have hae : f =ᵐ[AddCircle.haarAddCircle] g :=
    hf'.coeFn_toLp.symm.trans (heq' ▸ hg'.coeFn_toLp)
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  exact Measure.ae_smul_measure hae _

/-- On an open subset of one fundamental interval, continuous real lifts of a.e. equal
circle functions coincide pointwise. -/
theorem eqOn_lift_of_ae_eq {T a : ℝ} [Fact (0 < T)] {f g : AddCircle T → ℝ}
    (h : f =ᵐ[volume] g) {U : Set ℝ} (hU : IsOpen U) (hcell : U ⊆ Ioc a (a + T))
    (hf : ContinuousOn (fun x : ℝ => f (x : AddCircle T)) U)
    (hg : ContinuousOn (fun x : ℝ => g (x : AddCircle T)) U) :
    EqOn (fun x : ℝ => f (x : AddCircle T))
      (fun x : ℝ => g (x : AddCircle T)) U := by
  have hae := (AddCircle.measurePreserving_mk T a).quasiMeasurePreserving.ae_eq_comp h
  exact Measure.eqOn_open_of_ae_eq
    (ae_restrict_of_ae_restrict_of_subset hcell hae) hU hf hg

end Riesz1.CircleFourier
