/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.Global
public import Riesz1.ToMathlib.EllipticRegularity.WeakDerivatives

/-!
# From global Fourier regularity to explicit local weak derivatives

This connects the global Fourier step of the interior H² regularity argument to the
local weak derivative predicates used by that argument. It does not assume
classical differentiability of a representative of an L² class.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap Laplacian LineDeriv ContDiff

namespace Riesz1

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [InnerProductSpace ℂ F] [CompleteSpace F] in
/-- A global L² representative is locally L² on every domain. -/
theorem locallySquareIntegrableOn_of_memLp {u : E → F}
    (hu : MemLp u 2 volume) (U : Set E) : LocallySquareIntegrableOn U u := by
  intro K _ _
  exact hu.restrict K

/-- The distributional derivative of L² classes satisfies the real test
identity of the local weak derivative definition, also for complex values. -/
theorem hasWeakDirectionalDerivativeOn_of_tempered {u g : Lp F 2 (volume : Measure E)}
    {v : E} (h : ∂_{v} (u : 𝓢'(E, F)) = (g : 𝓢'(E, F))) (U : Set E) :
    HasWeakDirectionalDerivativeOn U u g v := by
  refine ⟨((Lp.memLp u).locallyIntegrable (by norm_num)).locallyIntegrableOn U,
    ((Lp.memLp g).locallyIntegrable (by norm_num)).locallyIntegrableOn U, ?_⟩
  intro φ hφ hφc _
  let ψ : 𝓢(E, ℂ) :=
    (hφc.comp_left (show Complex.ofRealCLM 0 = 0 from map_zero _)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hφ)
  have heq := congrArg (fun T : 𝓢'(E, F) => T ψ) h
  have hd (x : E) : (∂_{v} ψ) x = (fderiv ℝ φ x v : ℂ) := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change fderiv ℝ (Complex.ofRealCLM ∘ φ) x v = _
    rw [fderiv_comp x Complex.ofRealCLM.differentiableAt
      (hφ.differentiable (by norm_num) x), Complex.ofRealCLM.fderiv]
    rfl
  simp only [TemperedDistribution.lineDerivOp_apply_apply,
    Lp.toTemperedDistribution_apply] at heq
  have hleft : (∫ x, ψ x • g x) = ∫ x, φ x • g x := by
    congr 1
  rw [hleft] at heq
  have hright : (∫ x, (- ∂_{v} ψ) x • u x) =
      - ∫ x, fderiv ℝ φ x v • u x := by
    simp only [neg_apply, hd, neg_smul, integral_neg]
    rfl
  exact heq.symm.trans hright

/-- Global L² control of a distribution and its Laplacian produces the
actual first and second weak derivative representatives in `IsLocalH2`.
This is the global step of the interior H² regularity argument, without localization. -/
theorem isLocalH2_of_tempered_laplacian (u f : Lp F 2 (volume : Measure E))
    (hΔ : Δ (u : 𝓢'(E, F)) = (f : 𝓢'(E, F))) (U : Set E) :
    IsLocalH2 U (u : E → F) := by
  have hu : MemSobolev 0 2 (u : 𝓢'(E, F)) := memSobolev_zero_iff.mpr ⟨u, rfl⟩
  have hf : MemSobolev 0 2 (Δ (u : 𝓢'(E, F))) :=
    memSobolev_zero_iff.mpr ⟨f, hΔ⟩
  let e := stdOrthonormalBasis ℝ E
  have hd (i : Fin (Module.finrank ℝ E)) :
      ∃ g : Lp F 2 (volume : Measure E), ∂_{e i} (u : 𝓢'(E, F)) = (g : 𝓢'(E, F)) :=
    (exists_l2_derivatives_of_laplacian hu hf (e i) (e i)).1
  choose g hg using hd
  have hdd (i j : Fin (Module.finrank ℝ E)) :
      ∃ h : Lp F 2 (volume : Measure E), ∂_{e j} (g i : 𝓢'(E, F)) = (h : 𝓢'(E, F)) := by
    obtain ⟨h, hh⟩ := (exists_l2_derivatives_of_laplacian hu hf (e i) (e j)).2
    exact ⟨h, by simpa only [hg i] using hh⟩
  choose h hh using hdd
  refine ⟨locallySquareIntegrableOn_of_memLp (Lp.memLp u) U,
    (fun i => (g i : E → F)), (fun i j => (h i j : E → F)), ?_⟩
  intro i
  refine ⟨locallySquareIntegrableOn_of_memLp (Lp.memLp (g i)) U,
    hasWeakDirectionalDerivativeOn_of_tempered (hg i) U, ?_⟩
  intro j
  exact ⟨locallySquareIntegrableOn_of_memLp (Lp.memLp (h i j)) U,
    hasWeakDirectionalDerivativeOn_of_tempered (hh i j) U⟩

end Riesz1
