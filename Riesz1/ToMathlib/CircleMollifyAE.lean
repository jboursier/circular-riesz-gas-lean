/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleCoeffUniqueness
public import Riesz1.ToMathlib.MollifierPointwise.Circle

/-!
# Circular mollification depends only on the almost-everywhere class

The circular mollification `circleMollify ρ L h f` of `ℝ / Lℤ` integrates `f`
over the fundamental interval `(-L/2, L/2]`. Two `L²` functions on a circle with equal Fourier
coefficients agree almost everywhere, so their mollifications agree everywhere. This file records the
three steps: almost-everywhere equality on the fundamental interval, transfer from the circle to the
line, and equality of `L²` classes from equality of coefficients.
-/

@[expose] public section

open MeasureTheory Filter Set

namespace Riesz1

/-- Two real functions on the line that agree almost everywhere on the fundamental interval
`(-L/2, L/2]` have the same circular mollification. -/
theorem circleMollify_congr_of_ae_Ioc (ρ : ℝ → ℝ) (L h : ℝ) (hL : 0 < L) {f g : ℝ → ℝ}
    (hfg : ∀ᵐ y ∂volume, y ∈ Ioc (-(L / 2)) (L / 2) → f y = g y) :
    circleMollify ρ L h f = circleMollify ρ L h g := by
  have hle : -(L / 2) ≤ L / 2 := by linarith
  funext x
  unfold circleMollify
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hfg] with y hy hmem
  rw [Set.uIoc_of_le hle] at hmem
  simp only [hy hmem]

/-- Two functions on a circle of length `L` that agree almost everywhere agree almost everywhere
on the fundamental interval `(-L/2, L/2]`, after lifting to the line. -/
theorem ae_Ioc_of_ae_circle {L : Length} {f g : Circle L → ℝ} (h : f =ᵐ[arclength L] g) :
    ∀ᵐ y ∂volume, y ∈ Ioc (-(L.val / 2)) (L.val / 2) → f (y : Circle L) = g (y : Circle L) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hvol : arclength L = volume := rfl
  rw [hvol] at h
  have hae := (AddCircle.measurePreserving_mk L.val (-(L.val / 2))).quasiMeasurePreserving.ae_eq_comp h
  have hI : -(L.val / 2) + L.val = L.val / 2 := by ring
  rw [hI] at hae
  exact (ae_restrict_iff' measurableSet_Ioc).mp hae

/-- The circular mollification of a function on the circle of length `L` depends only on the class
of the function almost everywhere. -/
theorem circleMollify_congr_circle (ρ : ℝ → ℝ) (L : Length) (h : ℝ) {f g : Circle L → ℝ}
    (hfg : f =ᵐ[arclength L] g) :
    circleMollify ρ L.val h (fun t : ℝ => f (t : Circle L)) =
      circleMollify ρ L.val h (fun t : ℝ => g (t : Circle L)) :=
  circleMollify_congr_of_ae_Ioc ρ L.val h L.property (ae_Ioc_of_ae_circle hfg)

/-- Two `L²` real functions on a circle with equal Fourier coefficients agree almost everywhere.
This is the almost-everywhere step of `continuous_eq_of_coeff_eq`, which needs no continuity. -/
theorem ae_eq_of_coeff_eq_real {L : Length} {f g : Circle L → ℝ}
    (hf : MemLp (fun x => (f x : ℂ)) 2 (arclength L))
    (hg : MemLp (fun x => (g x : ℂ)) 2 (arclength L))
    (h : ∀ k : ℤ, coeff L ⟨fun x => (f x : ℂ), complexL2Integrable L _ hf⟩ k =
      coeff L ⟨fun x => (g x : ℂ), complexL2Integrable L _ hg⟩ k) :
    f =ᵐ[arclength L] g := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hvol : arclength L = volume := rfl
  have hfv : MemLp (fun x => (f x : ℂ)) 2 volume := by
    rw [← hvol]
    exact hf
  have hgv : MemLp (fun x => (g x : ℂ)) 2 volume := by
    rw [← hvol]
    exact hg
  have hae : (fun x => (f x : ℂ)) =ᵐ[volume] (fun x => (g x : ℂ)) :=
    CircleFourier.ae_eq_of_coeff_eq hfv hgv (fun k => h k)
  rw [hvol]
  filter_upwards [hae] with x hx
  exact Complex.ofReal_injective hx

end Riesz1

end
