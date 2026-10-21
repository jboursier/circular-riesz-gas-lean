/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Transport of tilted measures through orthonormal coordinates

A measure identity for the Euclidean-coordinate step. Measurable equivalences commute with exponential tilting,
including the normalization in its definition.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The exponential tilt is the usual normalization of its unnormalized
density, whenever the latter has a positive finite integral. -/
theorem poincare_tilted_eq_normalized {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (V : α → ℝ)
    (hV : Integrable (fun x => Real.exp (V x)) μ)
    (hZ : 0 < ∫ x, Real.exp (V x) ∂μ) :
    μ.tilted V = (∫⁻ x, ENNReal.ofReal (Real.exp (V x)) ∂μ)⁻¹ •
      μ.withDensity (fun x => ENNReal.ofReal (Real.exp (V x))) := by
  have hn := ofReal_integral_eq_lintegral_ofReal hV
    (Filter.Eventually.of_forall fun x => (Real.exp_pos (V x)).le)
  rw [← hn, Measure.tilted, ← withDensity_smul' _ _
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hZ).ne')]
  congr 1
  funext x
  rw [ENNReal.ofReal_div_of_pos hZ]
  simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- A measurable equivalence commutes with exponential tilting. -/
theorem poincare_map_tilted {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (V : β → ℝ) :
    (μ.tilted (fun x => V (e x))).map e = (μ.map e).tilted V := by
  have hnorm : ∫ x, Real.exp (V (e x)) ∂μ = ∫ y, Real.exp (V y) ∂μ.map e :=
    (integral_map_equiv e (fun y => Real.exp (V y))).symm
  ext s hs
  rw [Measure.map_apply e.measurable hs, Measure.tilted, Measure.tilted,
    withDensity_apply _ (e.measurable hs), withDensity_apply _ hs, hnorm,
    ← lintegral_indicator (e.measurable hs), ← lintegral_indicator hs,
    lintegral_map_equiv]
  exact lintegral_congr fun x => by
    by_cases hx : e x ∈ s <;> simp [hx]

/-- Isometric Euclidean coordinates transport the normalized exponential
density on an open set to the normalized density on its image. -/
theorem poincare_isometry_tilted {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (e : E ≃ₗᵢ[ℝ] F) {U : Set F} (hU : IsOpen U) (V : F → ℝ) :
    (((volume : Measure E).restrict (e ⁻¹' U)).tilted (fun x => V (e x))).map e =
      ((volume : Measure F).restrict U).tilted V := by
  let em : E ≃ᵐ F := e.toHomeomorph.toMeasurableEquiv
  have hmap : ((volume : Measure E).restrict (e ⁻¹' U)).map em =
      (volume : Measure F).restrict U :=
    (e.measurePreserving.restrict_preimage hU.measurableSet).map_eq
  change (((volume : Measure E).restrict (e ⁻¹' U)).tilted (fun x => V (em x))).map em = _
  rw [poincare_map_tilted, hmap]

end Riesz1

end
