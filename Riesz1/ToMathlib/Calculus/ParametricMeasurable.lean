/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Measurability of parametric Fréchet derivatives

Let `g a : E → F` be a family of functions indexed by a measurable space `α` with measure `μ`,
where `E` is a finite-dimensional real normed space. Suppose that each `a ↦ g a w` is a.e.
strongly measurable and that `g a` is differentiable for almost every `a`. Then the Fréchet
derivative `a ↦ fderiv ℝ (g a) w` is a.e. strongly measurable as a map into `E →L[ℝ] F`.

The proof has three steps. Directional derivatives are limits of difference quotients, so
`a ↦ fderiv ℝ (g a) w v` is a.e. strongly measurable for every vector `v`
(`Riesz1.aestronglyMeasurable_fderiv_apply`). A continuous linear map on a finite-dimensional
space is the sum of its values on a basis, weighted by coordinate functionals, which gives the
measurability of the map itself (`Riesz1.aestronglyMeasurable_of_apply_clm`). Combining the two
gives `Riesz1.aestronglyMeasurable_fderiv`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace Riesz1

variable {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The directional Fréchet derivative `a ↦ fderiv ℝ (g a) w v` is a.e. strongly measurable. It is
the a.e. limit of the difference quotients `(t_n)⁻¹ • (g a (w + t_n • v) - g a w)` with
`t_n = 1 / (n + 1)`. -/
theorem aestronglyMeasurable_fderiv_apply {g : α → E → F}
    (hg : ∀ w : E, AEStronglyMeasurable (fun a => g a w) μ)
    (hdiff : ∀ᵐ a ∂μ, Differentiable ℝ (g a)) (w v : E) :
    AEStronglyMeasurable (fun a => fderiv ℝ (g a) w v) μ := by
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ht_lim : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto t atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨ht_lim, Eventually.of_forall fun n => ?_⟩
    exact Set.mem_compl_singleton_iff.2 (one_div_ne_zero (by positivity))
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n a => (t n)⁻¹ • (g a (w + t n • v) - g a w))
    (fun n => ((hg (w + t n • v)).sub (hg w)).const_smul _) ?_
  filter_upwards [hdiff] with a ha
  have hline : HasDerivAt (fun s : ℝ => g a (w + s • v)) (fderiv ℝ (g a) w v) 0 := by
    have h1 : HasFDerivAt (g a) (fderiv ℝ (g a) w) (w + (0 : ℝ) • v) := by
      rw [zero_smul, add_zero]
      exact (ha w).hasFDerivAt
    have h2 : HasDerivAt (fun s : ℝ => w + s • v) v 0 := by
      simpa using HasDerivAt.const_add w (HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) v)
    exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) h1 h2
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 hline
  simp only [zero_add, zero_smul, add_zero] at hslope
  exact hslope.comp ht

/-- A map into `E →L[ℝ] F`, with `E` finite-dimensional, is a.e. strongly measurable as soon as
its values on every vector are. -/
theorem aestronglyMeasurable_of_apply_clm [FiniteDimensional ℝ E] {Λ : α → E →L[ℝ] F}
    (h : ∀ v : E, AEStronglyMeasurable (fun a => Λ a v) μ) :
    AEStronglyMeasurable Λ μ := by
  let b := Module.finBasis ℝ E
  have hdec : Λ = fun a => ∑ i, (LinearMap.toContinuousLinearMap (b.coord i)).smulRight (Λ a (b i)) := by
    funext a
    ext v
    calc Λ a v = Λ a (∑ i, b.repr v i • b i) := by rw [b.sum_repr v]
      _ = ∑ i, b.repr v i • Λ a (b i) := by rw [map_sum]; simp only [map_smul]
      _ = (∑ i, (LinearMap.toContinuousLinearMap (b.coord i)).smulRight (Λ a (b i))) v := by
          simp [Module.Basis.coord_apply]
  rw [hdec, ← Finset.sum_fn]
  refine Finset.aestronglyMeasurable_sum _ fun i _ => ?_
  exact (ContinuousLinearMap.smulRightL ℝ E F (LinearMap.toContinuousLinearMap (b.coord i))).continuous.comp_aestronglyMeasurable (h (b i))

/-- The Fréchet derivative `a ↦ fderiv ℝ (g a) w` of an a.e. differentiable parametric family is
a.e. strongly measurable, as a map into `E →L[ℝ] F`, when `E` is finite-dimensional. -/
theorem aestronglyMeasurable_fderiv [FiniteDimensional ℝ E] {g : α → E → F}
    (hg : ∀ w : E, AEStronglyMeasurable (fun a => g a w) μ)
    (hdiff : ∀ᵐ a ∂μ, Differentiable ℝ (g a)) (w : E) :
    AEStronglyMeasurable (fun a => fderiv ℝ (g a) w) μ :=
  aestronglyMeasurable_of_apply_clm fun v => aestronglyMeasurable_fderiv_apply hg hdiff w v

end Riesz1

end
