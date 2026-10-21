/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.WeakOperations
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Complex tests for the local Schrödinger equation

The real test predicate from `WeakDerivatives` also allows complex
compact tests. This is needed to compare it with complex tempered
distributions in the interior H² regularity argument.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff Laplacian Topology
open scoped SchwartzMap

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The classical Laplacian has support inside the support of its argument. -/
theorem tsupport_laplacian_subset {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (φ : E → F) : tsupport (Δ φ) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro x hx
  by_contra hn
  have heq := InnerProductSpace.laplacian_congr_nhds
    (notMem_tsupport_iff_eventuallyEq.mp hn)
  have hzero : (Δ (0 : E → F)) x = 0 :=
    congrFun (InnerProductSpace.laplacian_const (E := E) (c := (0 : F))) x
  exact hx (heq.eq_of_nhds.trans hzero)

omit [MeasurableSpace E] [BorelSpace E] in
/-- A compact smooth test has continuous classical Laplacian. -/
theorem continuous_laplacian_of_compact_smooth {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) : Continuous (Δ φ) := by
  let s : 𝓢(E, ℝ) := hφc.toSchwartzMap hφ
  have heq : ((Δ s : 𝓢(E, ℝ)) : E → ℝ) = Δ φ := by
    funext x
    exact SchwartzMap.laplacian_apply s x
  rw [← heq]
  exact (Δ s : 𝓢(E, ℝ)).continuous

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Real tests encode the full complex distributional equation.
Every integral appearing in the real and imaginary decomposition is
integrable on the compact interior support. -/
theorem IsDistributionalSchrodingerSolution.test_complex {U : Set E}
    {W : E → ℝ} {lam : ℝ} {u : E → F}
    (hu : IsDistributionalSchrodingerSolution U W lam u)
    {ψ : E → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) :
    (∫ x, ψ x • ((W x + lam) • u x)) = ∫ x, (Δ ψ) x • u x := by
  have hr : ContDiff ℝ ∞ (Complex.reCLM ∘ ψ) := Complex.reCLM.contDiff.comp hψ
  have hi : ContDiff ℝ ∞ (Complex.imCLM ∘ ψ) := Complex.imCLM.contDiff.comp hψ
  have hrc : HasCompactSupport (Complex.reCLM ∘ ψ) := hψc.comp_left (map_zero _)
  have hic : HasCompactSupport (Complex.imCLM ∘ ψ) := hψc.comp_left (map_zero _)
  have hrU : tsupport (Complex.reCLM ∘ ψ) ⊆ U :=
    (tsupport_comp_subset (map_zero Complex.reCLM) ψ).trans hψU
  have hiU : tsupport (Complex.imCLM ∘ ψ) ⊆ U :=
    (tsupport_comp_subset (map_zero Complex.imCLM) ψ).trans hψU
  have hΔr : Δ (Complex.reCLM ∘ ψ) = Complex.reCLM ∘ (Δ ψ) := by
    funext x
    exact (hψ.contDiffAt.of_le (by simp)).laplacian_CLM_comp_left
  have hΔi : Δ (Complex.imCLM ∘ ψ) = Complex.imCLM ∘ (Δ ψ) := by
    funext x
    exact (hψ.contDiffAt.of_le (by simp)).laplacian_CLM_comp_left
  have hΔrc : HasCompactSupport (Δ (Complex.reCLM ∘ ψ)) :=
    hrc.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset _)
  have hΔic : HasCompactSupport (Δ (Complex.imCLM ∘ ψ)) :=
    hic.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset _)
  have hdrc := continuous_laplacian_of_compact_smooth hr hrc
  have hdic := continuous_laplacian_of_compact_smooth hi hic
  have hAr := integrable_smul_of_compact_interior hu.2.1 hr.continuous hrc hrU
  have hAi := integrable_smul_of_compact_interior hu.2.1 hi.continuous hic hiU
  have hBr := integrable_smul_of_compact_interior hu.1 hdrc hΔrc
    ((tsupport_laplacian_subset _).trans hrU)
  have hBi := integrable_smul_of_compact_interior hu.1 hdic hΔic
    ((tsupport_laplacian_subset _).trans hiU)
  have hsplit (z : ℂ) (a : F) : z • a = z.re • a + Complex.I • (z.im • a) := by
    conv_lhs => rw [← Complex.re_add_im z]
    simp only [add_smul, mul_smul]
    rw [smul_comm (z.im : ℂ) Complex.I]
    rfl
  have hleft : (fun x => ψ x • ((W x + lam) • u x)) =
      (fun x => (ψ x).re • ((W x + lam) • u x) +
        Complex.I • ((ψ x).im • ((W x + lam) • u x))) := by
    funext x
    exact hsplit (ψ x) _
  have hright : (fun x => (Δ ψ) x • u x) =
      (fun x => ((Δ ψ) x).re • u x + Complex.I • (((Δ ψ) x).im • u x)) := by
    funext x
    exact hsplit ((Δ ψ) x) _
  rw [hleft, hright]
  simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply] at hAr hAi
  have hAi' : Integrable (fun x => Complex.I • ((ψ x).im • ((W x + lam) • u x))) :=
    hAi.smul Complex.I
  have her := hu.2.2 _ hr hrc hrU
  have hei := hu.2.2 _ hi hic hiU
  rw [hΔr] at her hBr
  rw [hΔi] at hei hBi
  simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply] at her hei hBr hBi
  have hBi' : Integrable (fun x => Complex.I • (((Δ ψ) x).im • u x)) := hBi.smul Complex.I
  rw [integral_add hAr hAi', integral_smul, her, hei,
    integral_add hBr hBi', integral_smul]

end Riesz1
