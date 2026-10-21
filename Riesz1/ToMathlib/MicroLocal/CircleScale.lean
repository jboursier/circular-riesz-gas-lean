/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Arclength under a circle rescaling

Metric and measure identities for the canonical rescaling of a circle.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- A real interval of length at most `R` projects to a circle set of
diameter at most `R`, including intervals longer than a circumference. -/
theorem circle_interval_diameter (L a b R : ℝ) (hR : b - a ≤ R) :
    ∀ u ∈ (fun x : ℝ => (x : AddCircle L)) '' Set.Icc a b,
      ∀ v ∈ (fun x : ℝ => (x : AddCircle L)) '' Set.Icc a b, dist u v ≤ R := by
  rintro u ⟨x, hx, rfl⟩ v ⟨y, hy, rfl⟩
  calc
    dist (x : AddCircle L) (y : AddCircle L) ≤ |x - y| := by
      rw [dist_eq_norm, ← AddCircle.coe_sub]
      exact QuotientAddGroup.norm_mk_le_norm
    _ ≤ R := abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩

/-- Closed arcs are Borel, including singleton arcs and the whole circle. -/
theorem measurableSet_circle_interval (L a b : ℝ) :
    MeasurableSet ((fun x : ℝ => (x : AddCircle L)) '' Set.Icc a b) :=
  (isCompact_Icc.image (AddCircle.continuous_mk' L)).isClosed.measurableSet

/-- Canonical rescaling from the unit circle multiplies distances by `L`. -/
theorem circleScale_dist (L : ℝ) [hL : Fact (0 < L)] (u v : UnitAddCircle) :
    dist (AddCircle.equivAddCircle 1 L one_ne_zero hL.out.ne' u)
      (AddCircle.equivAddCircle 1 L one_ne_zero hL.out.ne' v) = L * dist u v := by
  induction u using Quotient.inductionOn with | h u =>
  induction v using Quotient.inductionOn with | h v =>
  simp only [dist_eq_norm, ← AddCircle.coe_sub,
    AddCircle.equivAddCircle_apply_mk, inv_one, one_mul]
  rw [AddCircle.norm_eq' L hL.out, UnitAddCircle.norm_eq]
  rw [show L⁻¹ * (u * L - v * L) = u - v by field_simp [hL.out.ne']]

/-- Normalized arclength is preserved by the canonical circle rescaling. -/
theorem map_circleScale_volume (L : ℝ) [hL : Fact (0 < L)] :
    (volume : Measure UnitAddCircle).map
      (AddCircle.equivAddCircle 1 L one_ne_zero hL.out.ne') =
        (ENNReal.ofReal L)⁻¹ • (volume : Measure (AddCircle L)) := by
  let e := AddCircle.equivAddCircle 1 L one_ne_zero hL.out.ne'
  have he : Continuous e := AddCircle.continuous_equivAddCircle ..
  have hei : Continuous e.symm := (AddCircle.homeomorphAddCircle 1 L
    one_ne_zero hL.out.ne').continuous_symm
  let : Measure.IsAddHaarMeasure ((volume : Measure UnitAddCircle).map e) :=
    e.isAddHaarMeasure_map volume he hei
  let : IsProbabilityMeasure ((volume : Measure UnitAddCircle).map e) :=
    ⟨by rw [Measure.map_apply_of_aemeasurable he.measurable.aemeasurable MeasurableSet.univ]; simp⟩
  have h := Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure
    ((volume : Measure UnitAddCircle).map e) (AddCircle.haarAddCircle : Measure (AddCircle L))
  rw [h, AddCircle.volume_eq_smul_haarAddCircle, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hL.out) ENNReal.ofReal_ne_top,
    one_smul]

/-- Lower integrals acquire the reciprocal circumference under rescaling. -/
theorem lintegral_circleScale (L : ℝ) [hL : Fact (0 < L)]
    (F : AddCircle L → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u : UnitAddCircle, F (AddCircle.equivAddCircle 1 L one_ne_zero hL.out.ne' u)) =
      (ENNReal.ofReal L)⁻¹ * ∫⁻ u, F u := by
  rw [← lintegral_map hF (AddCircle.continuous_equivAddCircle ..).measurable,
    map_circleScale_volume, lintegral_smul_measure]
  rfl

end Riesz1

end
