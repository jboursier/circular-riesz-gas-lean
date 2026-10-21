/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Poincare.Isometry
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Linear changes of variables for normalized exponential densities

A constant Jacobian cancels from the exponential tilt. No particular
normalization of the two additive Haar measures is required.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Riesz1

/-- A probability exponential tilt certifies that its defining weight
has a finite positive integral. -/
theorem normalization_of_probability_tilted {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (V : α → ℝ) [IsProbabilityMeasure (μ.tilted V)] :
    Integrable (fun x => Real.exp (V x)) μ ∧ 0 < ∫ x, Real.exp (V x) ∂μ := by
  have hn : μ.tilted V ≠ 0 := by
    intro hz
    have h := measure_univ (μ := μ.tilted V)
    rw [hz] at h
    simp at h
  have hi : Integrable (fun x => Real.exp (V x)) μ := by
    by_contra hi
    exact hn (tilted_of_not_integrable hi)
  have : NeZero μ := ⟨fun hz => hn (by rw [hz, tilted_zero_measure])⟩
  exact ⟨hi, integral_exp_pos hi⟩

/-- Multiplication of the reference measure by a finite positive scalar
does not change an exponential tilt. -/
theorem tilted_nnreal_smul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (V : α → ℝ) {c : ℝ≥0} (hc : 0 < c) :
    ((c : ℝ≥0∞) • μ).tilted V = μ.tilted V := by
  rw [Measure.tilted, Measure.tilted, integral_smul_measure,
    withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.coe_ne_top]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.coe_toReal]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul c.coe_nonneg]
  congr 1
  have hc0 : (c : ℝ) ≠ 0 := (show (0 : ℝ) < c from hc).ne'
  by_cases hi : (∫ x, Real.exp (V x) ∂μ) = 0
  · simp [hi]
  · field_simp

/-- An invertible linear chart transports a normalized exponential
density, including its positive constant Jacobian. -/
theorem linearEquiv_map_tilted {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (e : E ≃L[ℝ] F) (U : Set F) (V : F → ℝ) :
    (((volume : Measure E).restrict (e ⁻¹' U)).tilted (fun x => V (e x))).map e =
      ((volume : Measure F).restrict U).tilted V := by
  let em := e.toHomeomorph.toMeasurableEquiv
  have he : ((volume : Measure E).restrict (e ⁻¹' U)).map e =
      ((volume : Measure E).map e).restrict U :=
    (MeasurableEmbedding.restrict_map e.toHomeomorph.measurableEmbedding _ U).symm
  have hh : ((volume : Measure E).map e) =
      (((volume : Measure E).map e).addHaarScalarFactor (volume : Measure F) : ℝ≥0∞) •
        (volume : Measure F) :=
    Measure.isAddLeftInvariant_eq_smul _ _
  have hc : 0 < ((volume : Measure E).map e).addHaarScalarFactor (volume : Measure F) :=
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  change (((volume : Measure E).restrict (e ⁻¹' U)).tilted (fun x => V (em x))).map em = _
  rw [poincare_map_tilted]
  change ((((volume : Measure E).restrict (e ⁻¹' U)).map e).tilted V) = _
  rw [he, hh, Measure.restrict_smul, tilted_nnreal_smul _ _ hc]

end Riesz1

end
