/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BLEuclidean

/-!
# Poincaré from Euclidean Brascamp–Lieb

The inverse Hessian energy is bounded by `κ⁻¹` times the gradient energy.
This gives the Euclidean ingredient for the
entire weighted Sobolev completion.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace Riesz1

/-- Poincaré on a bounded open convex domain with `D²V ≥ κ I`, for every
element of its weighted Sobolev completion. -/
theorem poincare_euclidean_H1 (hPL : External.PrekopaLeindler) {d : ℕ} (hd : 0 < d)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : Bornology.IsBounded U) (ho : IsOpen U)
    (hne : U.Nonempty) (hc : Convex ℝ U)
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiffOn ℝ 2 V U) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    {F : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hFG : WeightedSobolev.IsWeightedH1 ((volume.restrict U).tilted (fun x => -V x)) U F G) :
    (∫ x, (F x - ∫ y, F y ∂((volume.restrict U).tilted (fun x => -V x))) ^ 2
        ∂((volume.restrict U).tilted (fun x => -V x))) ≤
      κ⁻¹ * ∫ x, ‖G x‖ ^ 2 ∂((volume.restrict U).tilted (fun x => -V x)) := by
  let ν := (volume.restrict U).tilted (fun x => -V x)
  have : IsProbabilityMeasure ν := bl_convex_isProbabilityMeasure hU hc ho hne hV hκ hb
  have hνU : ∀ᵐ x ∂ν, x ∈ U :=
    (tilted_absolutelyContinuous _ _).ae_le (ae_restrict_mem ho.measurableSet)
  refine (bl_euclidean_H1 hPL hd hU ho hne hc hV hκ hb hFG).trans ?_
  rw [← integral_const_mul]
  apply integral_mono_ae (integrable_energy_field hκ hb hνU hFG.memLp_grad)
    (hFG.memLp_grad.norm.integrable_sq.const_mul _)
  filter_upwards [hνU] with x hx
  simpa only [div_eq_mul_inv, mul_comm] using
    (bl_variational_energy_bounds (fderiv ℝ (fderiv ℝ V) x) (G x) hκ (hb x hx)).2

end Riesz1

end
