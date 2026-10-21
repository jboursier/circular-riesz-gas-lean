/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# Level sets of linear functionals are Haar-null

For a finite-dimensional real normed space `E` with an additive Haar measure `μ`, and a nonzero
continuous linear functional `L : E →L[ℝ] ℝ`, every level set `{z | L z = c}` is `μ`-null. The level
set is a proper affine hyperplane, and Mathlib's `addHaar_affineSubspace` gives the claim.

This is used for the exceptional set of the almost-everywhere derivative bound of Lemma 5.2,
where the cutoff is differentiable off finitely many affine hyperplanes.
-/

@[expose] public section

open MeasureTheory

namespace Riesz1

/-- **Level sets of nonzero linear functionals are null.** For every nonzero continuous linear
functional `L` on a finite-dimensional real normed space and every real `c`, the set
`{z | L z = c}` has measure zero for every additive Haar measure. -/
theorem addHaar_linear_level_set_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (L : E →L[ℝ] ℝ) (hL : L ≠ 0) (c : ℝ) :
    μ {z : E | L z = c} = 0 := by
  obtain ⟨v, hv⟩ : ∃ v : E, L v ≠ 0 := by
    by_contra h
    push Not at h
    exact hL (ContinuousLinearMap.ext fun w => h w)
  set p : E := (c / L v) • v with hp
  have hLp : L p = c := by
    rw [hp, map_smul, smul_eq_mul]
    field_simp
  set s : AffineSubspace ℝ E := AffineSubspace.mk' p (LinearMap.ker (L : E →ₗ[ℝ] ℝ)) with hs_def
  have hset : {z : E | L z = c} = (s : Set E) := by
    ext z
    rw [SetLike.mem_coe, hs_def, AffineSubspace.mem_mk', vsub_eq_sub,
      LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hLp, Set.mem_ofPred_eq,
      sub_eq_zero]
  have hne : s ≠ ⊤ := by
    intro htop
    have hmem : v + p ∈ s := by
      rw [htop]
      exact AffineSubspace.mem_top ℝ E _
    rw [hs_def, AffineSubspace.mem_mk', vsub_eq_sub, add_sub_cancel_right,
      LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hmem
    exact hv hmem
  rw [hset]
  exact Measure.addHaar_affineSubspace μ s hne

end Riesz1

end
