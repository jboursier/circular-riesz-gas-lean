/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Null boundary sections of open convex sets

For an open convex set `Q` in a product `E × EuclideanSpace ℝ (Fin n)` and a point `z` whose
fiber is nonempty, the set of exterior points `y` with `(z, y)` on the frontier of `Q` has
Lebesgue measure zero. The fiber of `Q` over `z` is open and convex, and this section lies in
its frontier.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology Filter

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fiber of an open convex set over a point is open and convex. -/
theorem isOpen_convex_fiber_prod {n : ℕ} {Q : Set (E × EuclideanSpace ℝ (Fin n))}
    (hQo : IsOpen Q) (hQc : Convex ℝ Q) (z : E) :
    IsOpen {y : EuclideanSpace ℝ (Fin n) | (z, y) ∈ Q} ∧
      Convex ℝ {y : EuclideanSpace ℝ (Fin n) | (z, y) ∈ Q} := by
  refine ⟨hQo.preimage (by fun_prop), ?_⟩
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  have h := hQc hy₁ hy₂ ha hb hab
  have hz : a • z + b • z = z := by
    rw [← add_smul, hab, one_smul]
  have heq : a • (z, y₁) + b • (z, y₂) = (z, a • y₁ + b • y₂) := by
    ext
    · simp [hz]
    · simp
  show (z, a • y₁ + b • y₂) ∈ Q
  rw [← heq]
  exact h

/-- The exterior section of the frontier of an open convex set has Lebesgue measure zero,
over every point whose fiber is nonempty. -/
theorem volume_section_frontier_eq_zero {n : ℕ} {Q : Set (E × EuclideanSpace ℝ (Fin n))}
    (hQo : IsOpen Q) (hQc : Convex ℝ Q) {z : E} (hz : ∃ y, (z, y) ∈ Q) :
    volume {y : EuclideanSpace ℝ (Fin n) | (z, y) ∈ frontier Q} = 0 := by
  obtain ⟨hsec_open, hsec_convex⟩ := isOpen_convex_fiber_prod hQo hQc z
  obtain ⟨y', hy'⟩ := hz
  have hsub : {y : EuclideanSpace ℝ (Fin n) | (z, y) ∈ frontier Q} ⊆
      frontier {y : EuclideanSpace ℝ (Fin n) | (z, y) ∈ Q} := by
    intro y hy
    have hcl : (z, y) ∈ closure Q := frontier_subset_closure hy
    have hnot : (z, y) ∉ Q := fun hi => hy.2 (by rw [hQo.interior_eq]; exact hi)
    -- The points `(z, t • y' + (1 - t) • y)` lie in `Q` for `t ∈ (0, 1]`.
    have hline : ∀ t : ℝ, 0 < t → t ≤ 1 →
        t • y' + (1 - t) • y ∈ {y : EuclideanSpace ℝ (Fin n) | (z, y) ∈ Q} := by
      intro t ht0 ht1
      have hcomb := hQc.combo_interior_closure_mem_interior (x := (z, y')) (y := (z, y))
        (a := t) (b := 1 - t) (by rw [hQo.interior_eq]; exact hy') hcl ht0 (by linarith)
        (by ring)
      rw [hQo.interior_eq] at hcomb
      have heq : t • (z, y') + (1 - t) • (z, y) = (z, t • y' + (1 - t) • y) := by
        ext
        · simp only [Prod.smul_fst, Prod.fst_add]
          rw [← add_smul, add_sub_cancel, one_smul]
        · simp
      show (z, t • y' + (1 - t) • y) ∈ Q
      rw [← heq]
      exact hcomb
    rw [frontier, hsec_open.interior_eq]
    refine ⟨?_, hnot⟩
    -- `y` lies in the closure of the fiber, as the limit of the points above.
    have hc : Continuous fun t : ℝ => t • y' + (1 - t) • y := by fun_prop
    have hlim : Tendsto (fun t : ℝ => t • y' + (1 - t) • y) (𝓝[>] (0 : ℝ)) (𝓝 y) := by
      have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    refine mem_closure_of_tendsto (f := fun t : ℝ => t • y' + (1 - t) • y)
      (b := 𝓝[>] (0 : ℝ)) hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hline t ht.1 ht.2.le
  have hfr : volume (frontier {y : EuclideanSpace ℝ (Fin n) | (z, y) ∈ Q}) = 0 :=
    hsec_convex.addHaar_frontier volume
  exact measure_mono_null hsub hfr

end Riesz1

end
end
