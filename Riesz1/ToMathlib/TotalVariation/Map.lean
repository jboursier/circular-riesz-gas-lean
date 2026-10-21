/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
public import Riesz1.ToMathlib.TotalVariation.Event

/-!
# Total variation does not increase under push-forward

For finite measures `μ ν` on `Ω` and a measurable map `f : Ω → Ω'`, the event distance of the
push-forward measures is at most that of `μ` and `ν`:
`etvDist (μ.map f) (ν.map f) ≤ etvDist μ ν`.

The proof takes a Hahn set `S'` for the push-forward pair. The preimage `S = f⁻¹' S'` is a
measurable set, and the Hahn formula evaluates the push-forward distance on `S` and `Sᶜ`.
The two-set bound of `Event.lean` then controls that expression by `etvDist μ ν`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Push-forward contraction: for finite measures `μ ν` on `Ω` and a measurable map
`f : Ω → Ω'`, the event distance of `μ.map f` and `ν.map f` is at most `etvDist μ ν`. -/
theorem etvDist_map_le_etvDist {Ω' : Type*} [MeasurableSpace Ω'] (μ ν : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : Ω → Ω'} (hf : Measurable f) :
    etvDist (μ.map f) (ν.map f) ≤ etvDist μ ν := by
  obtain ⟨S', hS'⟩ := exists_isHahnDecomposition (μ.map f) (ν.map f)
  -- Pull the Hahn set back to `Ω`, where its masses are the masses of `μ` and `ν`.
  set S := f ⁻¹' S' with hSdef
  have hS : MeasurableSet S := hf hS'.measurableSet
  have hcompl : f ⁻¹' S'ᶜ = Sᶜ := Set.preimage_compl
  have e1 : (μ.map f).real S' = μ.real S := map_measureReal_apply hf hS'.measurableSet
  have e2 : (ν.map f).real S' = ν.real S := map_measureReal_apply hf hS'.measurableSet
  have e3 : (μ.map f).real S'ᶜ = μ.real Sᶜ := by
    rw [map_measureReal_apply hf hS'.measurableSet.compl, hcompl]
  have e4 : (ν.map f).real S'ᶜ = ν.real Sᶜ := by
    rw [map_measureReal_apply hf hS'.measurableSet.compl, hcompl]
  -- The Hahn formula for the push-forward pair, with its masses rewritten on `Ω`.
  have htv : tvDist (μ.map f) (ν.map f) = ν.real S - μ.real S + (μ.real Sᶜ - ν.real Sᶜ) := by
    rw [hS'.tvDist_eq, e1, e2, e3, e4]
  -- The real discrepancies `x` on `S` and `y` on `Sᶜ`.
  have hle : tvDist (μ.map f) (ν.map f) ≤ |μ.real S - ν.real S| + |μ.real Sᶜ - ν.real Sᶜ| := by
    rw [htv]
    linarith [neg_le_abs (μ.real S - ν.real S), le_abs_self (μ.real Sᶜ - ν.real Sᶜ)]
  have hbound := enorm_measureReal_sub_add_enorm_compl_le_etvDist μ ν hS
  rw [← ofReal_tvDist]
  calc ENNReal.ofReal (tvDist (μ.map f) (ν.map f))
      ≤ ENNReal.ofReal (|μ.real S - ν.real S| + |μ.real Sᶜ - ν.real Sᶜ|) :=
        ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal |μ.real S - ν.real S| + ENNReal.ofReal |μ.real Sᶜ - ν.real Sᶜ| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ = ‖μ.real S - ν.real S‖ₑ + ‖μ.real Sᶜ - ν.real Sᶜ‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    _ ≤ etvDist μ ν := hbound

end Riesz1
