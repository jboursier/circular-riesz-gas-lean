/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleMollifyBounds
public import Riesz1.ToMathlib.CircleMollifyL2
public import Riesz1.Kernel.AdmissibilityRegularityUniformBound

/-!
# The uniform supremum bound for the smoothed transport

The transport-supremum clause of Lemma 5.1. The constant
precedes every circle, input profile, mollifier and smoothing radius. Only the
primitive hypothesis (A1) is needed for this clause.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace Riesz1

/-- The transport-supremum clause of Lemma 5.1, generalized to every
positive circle length and smoothing radius, with one constant depending only
on `P`, `η` and `B`. The Fourier identity identifies the unsmoothed transport.
Its smoothed version is exactly the convolution `circleMollify`. -/
theorem regUniform_transport_sup (P : Parameters) (η B : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Length)
      (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}),
      PrimitiveRegularity L η P.val.2 B f →
      ∃ ψ : Circle L → ℝ, Continuous ψ ∧
        ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength L),
          (∀ k : ℤ, coeff L ⟨(fun x => (ψ x : ℂ)),
              complexL2Integrable L _ hψ⟩ k = transportCoeffs P L f k) ∧
          (∀ x, |ψ x| ≤ C) ∧
          ∀ (ρ : ℝ → ℝ), IsMollifier ρ → ∀ h : ℝ, 0 < h → ∀ x : ℝ,
            |circleMollify ρ L.val h (fun t : ℝ => ψ (t : Circle L)) x| ≤ C := by
  obtain ⟨M, hM, hb⟩ := exists_uniform_bounded_transport P η B hη hB
  refine ⟨M + 1, by linarith, fun L f hf => ?_⟩
  obtain ⟨ψ, hc, hψ, hsup, hcoeff⟩ := hb L f hf
  have hbound (x : Circle L) : |ψ x| ≤ M + 1 := (hsup x).trans (by linarith)
  refine ⟨ψ, hc, hψ, hcoeff, hbound, fun ρ hρ h hh x => ?_⟩
  have hcont := hc.comp (AddCircle.continuous_mk' L.val)
  have hper : Function.Periodic (fun t : ℝ => ψ (t : Circle L)) L.val := by
    intro t
    simp only [AddCircle.coe_add_period]
  exact Internal.circleMollify_abs_le hρ L.property hh hcont.locallyIntegrable hper
    (fun t => hbound _) x

/-- The same uniform bound on the actual smooth, mean-zero transport of the
regularized profile. Both smooth objects are identified pointwise with the
existing convolution. Their Fourier coefficients prove commutation. -/
theorem regUniform_smoothed_transport (P : Parameters) (η B : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Length)
      (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}),
      PrimitiveRegularity L η P.val.2 B f →
      ∃ ψ : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
        Continuous ψ.val ∧
        (∀ k : ℤ, coeff L ⟨(fun x => (ψ.val x : ℂ)),
          complexL2Integrable L _ ψ.property⟩ k = transportCoeffs P L f k) ∧
        ∀ (ρ : ℝ → ℝ), IsMollifier ρ → ∀ h : ℝ, 0 < h →
          ∃ g ψh : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
            (∀ x : ℝ, g.val (x : Circle L) =
              circleMollify ρ L.val h (fun t : ℝ => f.val (t : Circle L)) x) ∧
            (∀ x : ℝ, ψh.val (x : Circle L) =
              circleMollify ρ L.val h (fun t : ℝ => ψ.val (t : Circle L)) x) ∧
            ContDiff ℝ ∞ (fun t : ℝ => ψh.val (t : Circle L)) ∧
            (∀ k : ℤ, coeff L ⟨(fun x => (ψh.val x : ℂ)),
              complexL2Integrable L _ ψh.property⟩ k = transportCoeffs P L g k) ∧
            ∀ x : Circle L, |ψh.val x| ≤ C := by
  obtain ⟨C, hC, hb⟩ := regUniform_transport_sup P η B hη hB
  refine ⟨C, hC, fun L f hf => ?_⟩
  obtain ⟨ψ, hc, hψ, hcoeff, _, hsup⟩ := hb L f hf
  refine ⟨⟨ψ, hψ⟩, hc, hcoeff, fun ρ hρ h hh => ?_⟩
  obtain ⟨g, _, _, hgv, hgf⟩ := Internal.exists_circleMollify_L2 hρ L hh f
  obtain ⟨ψh, _, hψhs, hψhv, hψhf⟩ :=
    Internal.exists_circleMollify_L2 hρ L hh ⟨ψ, hψ⟩
  refine ⟨g, ψh, hgv, hψhv, hψhs, fun k => ?_, ?_⟩
  · rw [hψhf, hcoeff]
    by_cases hk : k = 0
    · simp only [transportCoeffs, hk, ite_true, zero_mul]
    · simp only [transportCoeffs, hk, ite_false]
      rw [hgf]
      ring
  · intro x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      rw [hψhv]
      exact hsup ρ hρ h hh x

end Riesz1
