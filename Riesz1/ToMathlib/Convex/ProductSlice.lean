/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Null boundary slices of an open convex set in a product

Let `Q` be an open convex set in `E × F`, and let `z` be a point of the projection `Prod.fst '' Q`.
The slice `{y | (z, y) ∈ closure Q \ Q}` of the boundary of `Q` over `z` is a null set for every
Haar measure on `F`. Here the slice lies in the frontier of the fiber `{y | (z, y) ∈ Q}`, which is
a convex open set, and convex sets have null frontiers.

This is used to show that the zero extension of a density on `Q` is differentiable, with the
expected derivative, at almost every fiber point.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- For an open convex set `Q` in `E × F` and a point `z` of its projection, the set of `y` with
`(z, y)` in the boundary of `Q` is null for every Haar measure on `F`. -/
theorem measure_slice_closure_diff_eq_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    {Q : Set (E × F)} (hQo : IsOpen Q) (hQc : Convex ℝ Q) {z : E}
    (hz : z ∈ Prod.fst '' Q) :
    μ {y : F | (z, y) ∈ closure Q \ Q} = 0 := by
  obtain ⟨⟨z', y1⟩, hq1, hz1⟩ := hz
  obtain rfl : z' = z := hz1
  -- The fiber over `z` is a convex open set containing `y1`.
  set Fz : Set F := {y : F | (z', y) ∈ Q} with hFz_def
  have hFo : IsOpen Fz := hQo.preimage (by fun_prop)
  have hFc : Convex ℝ Fz := by
    intro x hx y hy a b ha hb hab
    show (z', a • x + b • y) ∈ Q
    have hcomb : (z', a • x + b • y) = a • (z', x) + b • (z', y) := by
      ext
      · simp [← add_smul, hab]
      · simp
    rw [hcomb]
    exact hQc hx hy ha hb hab
  -- The boundary slice lies in the frontier of the fiber.
  have hsub : {y : F | (z', y) ∈ closure Q \ Q} ⊆ frontier Fz := by
    intro y hy
    obtain ⟨hcl, hnot⟩ := hy
    have hmem : y ∈ closure Fz := by
      have hcurve : Tendsto (fun t : ℝ => (1 - t) • y + t • y1) (𝓝[>] 0) (𝓝 y) := by
        have hc : Continuous (fun t : ℝ => (1 - t) • y + t • y1) := by fun_prop
        have h := hc.tendsto 0
        simp only [sub_zero, one_smul, zero_smul, add_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      apply mem_closure_of_tendsto hcurve
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      -- The point `(z', (1 - t) • y + t • y1)` lies on the open segment from `(z', y1)` to
      -- `(z', y)`, hence in the interior of `Q`, which is `Q`.
      have hx : (z', y1) ∈ interior Q := by rwa [hQo.interior_eq]
      have hseg := hQc.openSegment_interior_closure_subset_interior hx hcl
      have hpt : (z', (1 - t) • y + t • y1) = t • (z', y1) + (1 - t) • (z', y) := by
        ext
        · simp [← add_smul]
        · simp [add_comm]
      have hin : t • (z', y1) + (1 - t) • (z', y) ∈ interior Q :=
        hseg ⟨t, 1 - t, ht.1, by linarith [ht.2], by ring, rfl⟩
      rw [hQo.interior_eq] at hin
      rw [← hpt] at hin
      exact hin
    refine ⟨hmem, ?_⟩
    rw [hFo.interior_eq]
    exact fun h => hnot h
  exact measure_mono_null hsub (Convex.addHaar_frontier μ hFc)

end Riesz1

end
