/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Distribution.Sobolev

/-!
# Global elliptic regularity for the Laplacian

The Fourier step of the interior H² regularity argument: a tempered distribution and
its Laplacian represented by square integrable functions have square
integrable first and second distributional derivatives. This does not
supply the localization or the initial local gradient estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution FourierTransform
open scoped SchwartzMap Laplacian LineDeriv

namespace Riesz1

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- The order two Bessel operator is the identity minus a scaled Laplacian.
The factor is forced by Mathlib's Fourier normalization. -/
theorem besselPotential_two_eq (u : 𝓢'(E, F)) :
    besselPotential E F 2 u =
      u - (((2 * Real.pi : ℝ) ^ 2)⁻¹) • (Δ u) := by
  have hsym : (fun x : E => (((1 + ‖x‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ) : ℂ)) =
      fun x => ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    norm_num
  rw [besselPotential, hsym, laplacian_eq_fourierMultiplierCLM, smul_smul]
  have hc : (((2 * Real.pi : ℝ) ^ 2)⁻¹) * (-(2 * Real.pi : ℝ) ^ 2) = -1 := by
    have hp : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
    field_simp
  rw [hc, neg_one_smul, sub_neg_eq_add]
  simp only [fourierMultiplierCLM_apply]
  have hs : (fun x : E => ((1 + ‖x‖ ^ 2 : ℝ) : ℂ)) =
      (fun _ : E => (1 : ℂ)) + (fun x : E => ((‖x‖ ^ 2 : ℝ) : ℂ)) := by
    ext x
    simp
  rw [hs, smulLeftCLM_add (by fun_prop) (by fun_prop)]
  simp

/-- Global gain of two derivatives from an `L²` Laplacian.
This is an internal analytic step of the interior H² regularity argument. -/
theorem memSobolev_two_of_laplacian {u : 𝓢'(E, F)}
    (hu : MemSobolev 0 2 u) (hΔ : MemSobolev 0 2 (Δ u)) :
    MemSobolev 2 2 u := by
  have h : MemSobolev 0 2 (besselPotential E F 2 u) := by
    rw [besselPotential_two_eq]
    have h := hu.sub (hΔ.smul (RCLike.ofReal (K := ℂ) ((2 * Real.pi : ℝ) ^ 2)⁻¹))
    simpa only [← RCLike.real_smul_eq_coe_smul (K := ℂ)] using h
  simpa using memSobolev_besselPotential_iff.mp h

/-- The global elliptic step produces actual `L²` representatives for all
first and second distributional directional derivatives. -/
theorem exists_l2_derivatives_of_laplacian {u : 𝓢'(E, F)}
    (hu : MemSobolev 0 2 u) (hΔ : MemSobolev 0 2 (Δ u)) (v w : E) :
    (∃ g : Lp F 2 (volume : Measure E), ∂_{v} u = (g : 𝓢'(E, F))) ∧
      (∃ h : Lp F 2 (volume : Measure E), ∂_{w} (∂_{v} u) = (h : 𝓢'(E, F))) := by
  have h2 := memSobolev_two_of_laplacian hu hΔ
  have h1 : MemSobolev 1 2 (∂_{v} u) := by
    convert h2.lineDerivOp (m := v) using 1
    norm_num
  have h0 : MemSobolev 0 2 (∂_{w} (∂_{v} u)) := by
    simpa using h1.lineDerivOp (m := w)
  exact ⟨memSobolev_zero_iff.mp (h1.mono (by norm_num)), memSobolev_zero_iff.mp h0⟩

end Riesz1
