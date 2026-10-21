/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Splitting a variance along a square integrable comparison

For a probability measure `μ` and square integrable real functions `F` and `T`, the variance of
`F` splits as

`Var F = 2 Cov(F, T) - Var T + Var (F - T)`,

where `Var G = ∫ (G - ∫ G)²` and `Cov(F, T) = ∫ (F - ∫ F)(T - ∫ T)`. This is the first display of
Proposition 5.6, stated for an arbitrary probability measure. The proof is the
pointwise identity `(F - a)² = 2 (F - a)(T - b) - (T - b)² + ((F - T) - (a - b))²` with the means
`a = ∫ F` and `b = ∫ T`, followed by linearity of the integral.

The main result is `Riesz1.variance_split_of_memLp`.
-/

@[expose] public section

open MeasureTheory

namespace Riesz1

/-- The variance of `F` splits along a square integrable comparison `T`: `Var F = 2 Cov(F, T) -
Var T + Var(F - T)` for a probability measure. -/
theorem variance_split_of_memLp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {F T : α → ℝ} (hF : MemLp F 2 μ) (hT : MemLp T 2 μ) :
    ∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ =
      2 * ∫ x, (F x - ∫ y, F y ∂μ) * (T x - ∫ y, T y ∂μ) ∂μ -
        ∫ x, (T x - ∫ y, T y ∂μ) ^ 2 ∂μ +
        ∫ x, ((F x - T x) - ∫ y, (F y - T y) ∂μ) ^ 2 ∂μ := by
  set a := ∫ y, F y ∂μ with ha
  set b := ∫ y, T y ∂μ with hb
  have hFint : Integrable F μ := hF.integrable one_le_two
  have hTint : Integrable T μ := hT.integrable one_le_two
  have hdiff : ∫ y, (F y - T y) ∂μ = a - b := integral_sub hFint hTint
  -- The centered functions are square integrable.
  have hU : MemLp (fun x => T x - b) 2 μ := hT.sub (memLp_const b)
  have hFa : MemLp (fun x => F x - a) 2 μ := hF.sub (memLp_const a)
  have hV : MemLp (fun x => (F x - T x) - (a - b)) 2 μ := (hF.sub hT).sub (memLp_const _)
  -- Pointwise: the square of `F - a` is `2 (F - a)(T - b) - (T - b)² + V²`.
  have hpt : ∀ x, (F x - a) ^ 2 =
      2 * ((F x - a) * (T x - b)) - (T x - b) ^ 2 + ((F x - T x) - (a - b)) ^ 2 :=
    fun x => by ring
  have hprod1 : Integrable (fun x => (F x - a) * (T x - b)) μ :=
    hFa.integrable_mul hU
  have hsq1 : Integrable (fun x => (T x - b) ^ 2) μ :=
    (hU.integrable_mul hU).congr (Filter.Eventually.of_forall fun x => by simp [sq])
  have hsq2 : Integrable (fun x => ((F x - T x) - (a - b)) ^ 2) μ :=
    (hV.integrable_mul hV).congr (Filter.Eventually.of_forall fun x => by simp [sq])
  have h2 : Integrable (fun x => 2 * ((F x - a) * (T x - b))) μ := hprod1.const_mul 2
  have h1 : Integrable (fun x => 2 * ((F x - a) * (T x - b)) - (T x - b) ^ 2) μ :=
    h2.sub hsq1
  rw [hdiff]
  calc ∫ x, (F x - a) ^ 2 ∂μ
      = ∫ x, (2 * ((F x - a) * (T x - b)) - (T x - b) ^ 2 +
          ((F x - T x) - (a - b)) ^ 2) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ x, (2 * ((F x - a) * (T x - b)) - (T x - b) ^ 2) ∂μ +
          ∫ x, ((F x - T x) - (a - b)) ^ 2 ∂μ := integral_add h1 hsq2
    _ = 2 * ∫ x, (F x - a) * (T x - b) ∂μ - ∫ x, (T x - b) ^ 2 ∂μ +
          ∫ x, ((F x - T x) - (a - b)) ^ 2 ∂μ := by
        rw [integral_sub h2 hsq1, integral_const_mul]

end Riesz1

end
