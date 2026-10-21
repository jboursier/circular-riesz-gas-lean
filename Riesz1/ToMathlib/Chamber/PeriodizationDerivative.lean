/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Chamber.Periodization
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Directional derivatives of compact periodizations

Local finiteness permits differentiating the periodization as a finite
sum on a neighborhood of every point, including the periodic seam.
-/

@[expose] public section

noncomputable section

open Set Function Filter Topology
open scoped ContDiff

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Periodicity of the whole function implies periodicity of its Fréchet derivative. -/
theorem fderiv_periodic_vector {v : E} {f : E → ℝ}
    (hf : ∀ (k : ℤ) x, f (x + (k : ℝ) • v) = f x) (k : ℤ) (x : E) :
    fderiv ℝ f (x + (k : ℝ) • v) = fderiv ℝ f x := by
  rw [← fderiv_comp_add_right ((k : ℝ) • v)]
  congr 1
  funext y
  exact hf k y

/-- Directional differentiation commutes with compact periodization. -/
theorem fderiv_vectorPeriodize_apply {v : E} (hv : v ≠ 0) {f : E → ℝ}
    (hf : Differentiable ℝ f) (hs : HasCompactSupport f) (x w : E) :
    fderiv ℝ (vectorPeriodize v hv f hs) x w =
      vectorPeriodize v hv (fun y => fderiv ℝ f y w) (hs.fderiv_apply ℝ w) x := by
  classical
  let g := fun k : ℤ => fun y : E => f (y + (k : ℝ) • v)
  have hd (k : ℤ) : HasFDerivAt (g k) (fderiv ℝ f (x + (k : ℝ) • v)) x := by
    simpa only [g, Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      (hf (x + (k : ℝ) • v)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).add_const ((k : ℝ) • v))
  obtain ⟨U, hUx, hU⟩ := (locallyFinite_vector_translates hv hs).closure x
  let s := hU.toFinset
  have hloc : vectorPeriodize v hv f hs =ᶠ[𝓝 x] fun y => ∑ k ∈ s, g k y := by
    filter_upwards [hUx] with y hy
    apply finsum_eq_sum_of_support_subset
    intro k hk
    exact hU.mem_toFinset.mpr ⟨y, subset_closure hk, hy⟩
  have hdx := (HasFDerivAt.fun_sum (u := s) (fun k _ => hd k)).congr_of_eventuallyEq hloc
  rw [hdx.fderiv, sum_apply]
  symm
  apply finsum_eq_sum_of_support_subset
  intro k hk
  apply hU.mem_toFinset.mpr
  refine ⟨x, ?_, mem_of_mem_nhds hUx⟩
  by_contra hx
  have hz : fderiv ℝ (g k) x = 0 := fderiv_of_notMem_tsupport ℝ hx
  rw [(hd k).fderiv] at hz
  exact hk (congrArg (fun A : E →L[ℝ] ℝ => A w) hz)

end Riesz1

end
