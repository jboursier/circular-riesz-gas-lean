/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Second derivatives of functions of one linear form

For a real function `φ` of one variable, a continuous linear form `ℓ`, and a constant `a`, the
function `z ↦ φ (a + ℓ z)` has second derivative `φ'' (a + ℓ y) (ℓ U)^2` at `y` in the direction
`U`. This is `fderiv_fderiv_affine_comp`. The finite-sum version `fderiv_fderiv_sum_apply` splits
the second derivative of a sum of such functions, provided each summand is `C²` near `y`.

These are general calculus facts. The Hessians of the pair energies and of the cutoff forcing in
Lemma 5.2 are instances.
-/

@[expose] public section

open Filter Topology

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Hessian of `z ↦ φ (a + ℓ z)` at `y` in the direction `U` is `φ'' (a + ℓ y) (ℓ U)^2`,
where `φ` is `C²` at the point `a + ℓ y`. -/
theorem fderiv_fderiv_affine_comp (φ : ℝ → ℝ) (ℓ : E →L[ℝ] ℝ) (a : ℝ) (y U : E)
    (hφ : ContDiffAt ℝ 2 φ (a + ℓ y)) :
    fderiv ℝ (fderiv ℝ (fun z => φ (a + ℓ z))) y U U =
      deriv (deriv φ) (a + ℓ y) * (ℓ U) ^ 2 := by
  have hev : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 φ (a + ℓ z) := by
    have h1 : ∀ᶠ t in 𝓝 (a + ℓ y), ContDiffAt ℝ 2 φ t := hφ.eventually (by simp)
    have h2 : Tendsto (fun z => a + ℓ z) (𝓝 y) (𝓝 (a + ℓ y)) :=
      (continuous_const.add ℓ.continuous).tendsto y
    exact h2.eventually h1
  have hfd : ∀ᶠ z in 𝓝 y, HasFDerivAt (fun z => φ (a + ℓ z)) (deriv φ (a + ℓ z) • ℓ) z := by
    filter_upwards [hev] with z hz
    have hd : HasDerivAt φ (deriv φ (a + ℓ z)) (a + ℓ z) :=
      (hz.differentiableAt (by norm_num)).hasDerivAt
    have hl : HasFDerivAt (fun z => a + ℓ z) ℓ z := (ℓ.hasFDerivAt).const_add a
    exact HasDerivAt.comp_hasFDerivAt z hd hl
  have hgrad : fderiv ℝ (fun z => φ (a + ℓ z)) =ᶠ[𝓝 y] fun z => deriv φ (a + ℓ z) • ℓ := by
    filter_upwards [hfd] with z hz using hz.fderiv
  rw [Filter.EventuallyEq.fderiv_eq hgrad]
  have hc1 : ContDiffAt ℝ 1 (deriv φ) (a + ℓ y) := hφ.derivWithin (by norm_num)
  have hdd : HasDerivAt (deriv φ) (deriv (deriv φ) (a + ℓ y)) (a + ℓ y) :=
    (hc1.differentiableAt (by norm_num)).hasDerivAt
  have hl : HasFDerivAt (fun z => a + ℓ z) ℓ y := (ℓ.hasFDerivAt).const_add a
  have hh : HasFDerivAt (fun z => deriv φ (a + ℓ z)) (deriv (deriv φ) (a + ℓ y) • ℓ) y :=
    HasDerivAt.comp_hasFDerivAt (h₂ := deriv φ) (f := fun z => a + ℓ z) (f' := ℓ) y hdd hl
  have hs : HasFDerivAt (fun z => deriv φ (a + ℓ z) • ℓ)
      ((deriv (deriv φ) (a + ℓ y) • ℓ).smulRight ℓ) y := HasFDerivAt.smul_const hh ℓ
  rw [hs.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
  ring

/-- The second derivative of a finite sum is the sum of the second derivatives, provided every
summand is `C²` at all points near `y`. -/
theorem fderiv_fderiv_sum_apply {ι : Type*} (u : Finset ι) (A : ι → E → ℝ) (y U : E)
    (hA : ∀ᶠ z in 𝓝 y, ∀ i ∈ u, ContDiffAt ℝ 2 (A i) z) :
    fderiv ℝ (fderiv ℝ (fun z => ∑ i ∈ u, A i z)) y U U =
      ∑ i ∈ u, fderiv ℝ (fderiv ℝ (A i)) y U U := by
  have hd : ∀ᶠ z in 𝓝 y, ∀ i ∈ u, DifferentiableAt ℝ (A i) z := by
    filter_upwards [hA] with z hz i hi using (hz i hi).differentiableAt (by norm_num)
  have hsum : (fun z => ∑ i ∈ u, A i z) = ∑ i ∈ u, A i := by
    ext z
    simp [Finset.sum_apply]
  have hgrad : fderiv ℝ (fun z => ∑ i ∈ u, A i z) =ᶠ[𝓝 y]
      fun z => ∑ i ∈ u, fderiv ℝ (A i) z := by
    filter_upwards [hd] with z hz
    rw [hsum, fderiv_sum hz]
  rw [Filter.EventuallyEq.fderiv_eq hgrad]
  have hy : ∀ i ∈ u, ContDiffAt ℝ 2 (A i) y := fun i hi => hA.self_of_nhds i hi
  have hd2 : ∀ i ∈ u, DifferentiableAt ℝ (fderiv ℝ (A i)) y := fun i hi =>
    ((hy i hi).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfun : (fun z => ∑ i ∈ u, fderiv ℝ (A i) z) = ∑ i ∈ u, fderiv ℝ (A i) := by
    ext z
    simp [Finset.sum_apply]
  rw [hfun, fderiv_sum hd2]
  simp only [sum_apply]

/-- The second derivative of a sum of two functions is the sum of their second derivatives, provided
both are `C²` at all points near `y`. -/
theorem fderiv_fderiv_add_apply (f g : E → ℝ) (y U : E)
    (hf : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 f z) (hg : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 g z) :
    fderiv ℝ (fderiv ℝ (fun z => f z + g z)) y U U =
      fderiv ℝ (fderiv ℝ f) y U U + fderiv ℝ (fderiv ℝ g) y U U := by
  have hd : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ f z ∧ DifferentiableAt ℝ g z := by
    filter_upwards [hf, hg] with z hz1 hz2
    exact ⟨hz1.differentiableAt (by norm_num), hz2.differentiableAt (by norm_num)⟩
  have hgrad : fderiv ℝ (fun z => f z + g z) =ᶠ[𝓝 y] fun z => fderiv ℝ f z + fderiv ℝ g z := by
    filter_upwards [hd] with z hz
    exact fderiv_add hz.1 hz.2
  rw [Filter.EventuallyEq.fderiv_eq hgrad]
  have hf2 : ContDiffAt ℝ 2 f y := hf.self_of_nhds
  have hg2 : ContDiffAt ℝ 2 g y := hg.self_of_nhds
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ (fderiv ℝ g) y :=
    (hg2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [show (fun z => fderiv ℝ f z + fderiv ℝ g z) = fderiv ℝ f + fderiv ℝ g from rfl,
    fderiv_add hdf hdg]
  rfl

end Riesz1

end
