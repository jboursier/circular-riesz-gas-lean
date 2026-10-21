/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroNearFarRegularity
public import Riesz1.ToMathlib.CircleCoeffUniqueness

/-!
# Identifying the quantitative and qualitative transport witnesses

The kernel bound and the cutoff regularity theorem construct transports
separately. Their continuity and Fourier coefficients force equality.
Consequently every transport witness in `MicroKernelBounds` gives the same
actual inverse representative and the same continuously differentiable far
pieces. This is an assembly step for Lemma 5.3.
-/

public section

open MeasureTheory Set

namespace Riesz1.Internal

/-- Continuous transport witnesses with the same Fourier coefficients agree
pointwise, including at the marks. -/
theorem regMicro_transport_unique (P : Parameters) (L : Length)
    (f ψ₁ ψ₂ : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (h₁ : Continuous ψ₁.val) (h₂ : Continuous ψ₂.val)
    (hc₁ : ∀ k : ℤ, coeff L
      ⟨fun x => (ψ₁.val x : ℂ), complexL2Integrable L _ ψ₁.property⟩ k = transportCoeffs P L f k)
    (hc₂ : ∀ k : ℤ, coeff L
      ⟨fun x => (ψ₂.val x : ℂ), complexL2Integrable L _ ψ₂.property⟩ k = transportCoeffs P L f k) :
    ψ₁ = ψ₂ := by
  apply Subtype.ext
  exact continuous_eq_of_coeff_eq h₁ h₂ ψ₁.property ψ₂.property
    (fun k => (hc₁ k).trans (hc₂ k).symm)

/-- The actual representative of any continuous transport with the right
coefficients has `C¹` far pieces. In particular this applies to the witness
whose quantitative bounds are supplied by `MicroKernelBounds`.
No derivative or value estimate is added as a hypothesis. -/
theorem regMicro_far_contDiff_of_transport (P : Parameters) (L : Length)
    (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (n : ℕ+) (a : Fin (n : ℕ) → ℝ) (α C₀ : ℝ)
    (hα0 : P.val.2-1 ≤ α) (hα1 : α < P.val.2/2) (hC₀ : 0 ≤ C₀)
    (hprim : PrimitiveRegularity L η P.val.2 B f)
    (hreg : TransportRegularity P L f n a α C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ)
    (r₀ h : ℝ) (hr : 0 < r₀) (hh : 0 < h) (hrL : 4*r₀ < L.val) (hhL : 8*h < L.val)
    (hsep : ∀ i j, i ≠ j → 8*h ≤ dist (a i : Circle L) (a j : Circle L))
    (ψ : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)})
    (hc : Continuous ψ.val)
    (hcoeff : ∀ k : ℤ, coeff L
      ⟨fun x => (ψ.val x : ℂ), complexL2Integrable L _ ψ.property⟩ k = transportCoeffs P L f k) :
    let m := (∫ y in Ioc (-(L.val/2)) (L.val/2), f.val (y : Circle L))/L.val
    let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
    let e := fun z : Circle L => m + inverseConvCircle P L q z - cltRegCircle hρ L hh f z
    (∀ᵐ x : ℝ ∂volume.restrict (Ioc (-(L.val/2)) (L.val/2)),
      e (x : Circle L) = f.val (x : Circle L) -
        circleMollify ρ L.val h (fun t => f.val (t : Circle L)) x) ∧
    (∀ j, ContDiff ℝ 1 (fun x : ℝ => microFarError L.val r₀ h a e j (x : Circle L))) ∧
    ContDiff ℝ 1 (fun x : ℝ => microFarRemainder L.val r₀ h a e (x : Circle L)) := by
  obtain ⟨ψ₀, hc₀, hcoeff₀, hb⟩ := reg_micro_near_far_representatives P L η B hη hB
    f n a α C₀ hα0 hα1 hC₀ hprim hreg ρ hρ r₀ h hr hh hrL hhL hsep
  have heq := regMicro_transport_unique P L f ψ₀ ψ hc₀ hc hcoeff₀ hcoeff
  subst ψ₀
  exact hb

end Riesz1.Internal
