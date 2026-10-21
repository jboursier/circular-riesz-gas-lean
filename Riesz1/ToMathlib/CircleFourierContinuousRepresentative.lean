/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Continuous representatives from summable Fourier coefficients

Absolute summability synthesizes a continuous Fourier series. Its `L²`
limit identifies it with the original function, without assuming pointwise
continuity of that function beforehand.
-/

public section

open MeasureTheory Filter

namespace Riesz1.CircleFourier

/-- Absolute summability gives a continuous representative of an `L²` function. -/
theorem exists_continuous_ae_eq_of_summable {T : ℝ} [Fact (0 < T)]
    {f : AddCircle T → ℂ} (hf : MemLp f 2 volume)
    (hs : Summable (fourierCoeff f)) :
    ∃ g : C(AddCircle T, ℂ), (g : AddCircle T → ℂ) =ᵐ[volume] f := by
  let u : ℤ → C(AddCircle T, ℂ) := fun k => fourierCoeff f k • fourier k
  have hu : Summable u := by
    apply Summable.of_norm
    simpa only [u, norm_smul, fourier_norm, mul_one] using hs.norm
  let g := ∑' k, u k
  have hH := hf.haarAddCircle
  have hL2 := hasSum_fourier_series_L2 (hH.toLp f)
  have hcoef (k : ℤ) : fourierCoeff (hH.toLp f) k = fourierCoeff f k :=
    congrFun (fourierCoeff_congr_ae hH.coeFn_toLp) k
  simp_rw [hcoef] at hL2
  have hg := (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ).hasSum hu.hasSum
  have heq : ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ g = hH.toLp f := by
    apply hg.unique
    convert hL2 using 1
    ext k
    simp only [u, map_smul]
    rfl
  refine ⟨g, ?_⟩
  have hae : (g : AddCircle T → ℂ) =ᵐ[AddCircle.haarAddCircle] f := by
    exact (ContinuousMap.coeFn_toLp AddCircle.haarAddCircle g).symm.trans
      (heq ▸ hH.coeFn_toLp)
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  exact Measure.ae_smul_measure hae _

/-- The real form of continuous Fourier synthesis. -/
theorem exists_continuous_real_ae_eq_of_summable {T : ℝ} [Fact (0 < T)]
    {f : AddCircle T → ℝ} (hf : MemLp (fun x => (f x : ℂ)) 2 volume)
    (hs : Summable (fourierCoeff (fun x => (f x : ℂ)))) :
    ∃ g : C(AddCircle T, ℝ), (g : AddCircle T → ℝ) =ᵐ[volume] f := by
  obtain ⟨g, hg⟩ := exists_continuous_ae_eq_of_summable hf hs
  refine ⟨⟨fun x => (g x).re, Complex.continuous_re.comp g.continuous⟩, ?_⟩
  filter_upwards [hg] with x hx
  exact congrArg Complex.re hx

end Riesz1.CircleFourier
