/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ForcingComparison
public import Riesz1.Frozen.External.Pinsker
public import Riesz1.ToMathlib.TotalVariation.Event

/-!
# Bridge: total variation and Mathlib's event distance `etvDist`

The total variation distance is `totalVariation μ ν = (etvDist μ ν).toReal / 2`, a
real number. Pinsker's inequality `Riesz1.External.Pinsker` is stated in `ℝ≥0∞` with
`etvDist μ ν / 2`.

Main results:
* `ofReal_totalVariation_eq_etvDist_div_two`: for probability measures, the nonnegative real
  `totalVariation μ ν` is `etvDist μ ν / 2` in `ℝ≥0∞`.
* `totalVariation_sq_le_two_klDiv`: Pinsker's inequality in `ℝ`, for probability measures
  whose relative entropy `klDiv μ ν` is finite.
-/

public section

open MeasureTheory

universe u

namespace Riesz1

/-- For probability measures, `ENNReal.ofReal (totalVariation μ ν) = etvDist μ ν / 2`. The event
distance is at most `2`, so it is finite, and `ENNReal.ofReal` undoes its `toReal`. -/
theorem ofReal_totalVariation_eq_etvDist_div_two {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (totalVariation μ ν) = etvDist μ ν / 2 := by
  have hne : etvDist μ ν ≠ ⊤ := ne_top_of_le_ne_top (by simp) (etvDist_le_two μ ν)
  unfold totalVariation
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_toReal hne,
    ENNReal.ofReal_ofNat]

/-- Pinsker's inequality in `ℝ`: for probability measures `μ` and `ν` whose relative
entropy `klDiv μ ν` is finite, `totalVariation μ ν ^ 2 ≤ 2 * (klDiv μ ν).toReal`. The finiteness
hypothesis is needed. If `klDiv μ ν = ⊤`, then `toReal` is `0` while `totalVariation` can be
positive: for two Dirac masses `μ = δ₀`, `ν = δ₁`, the entropy is `⊤` and `totalVariation μ ν = 1`. -/
theorem totalVariation_sq_le_two_klDiv (hP : Riesz1.External.Pinsker.{u}) {Ω : Type u}
    [MeasurableSpace Ω] (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfin : InformationTheory.klDiv μ ν ≠ ⊤) :
    totalVariation μ ν ^ 2 ≤ 2 * (InformationTheory.klDiv μ ν).toReal := by
  have hP' := hP Ω μ ν ‹IsProbabilityMeasure μ› ‹IsProbabilityMeasure ν›
  rw [← ofReal_totalVariation_eq_etvDist_div_two μ ν] at hP'
  have hTV : 0 ≤ totalVariation μ ν := by
    unfold totalVariation
    positivity
  have key : ENNReal.ofReal (totalVariation μ ν ^ 2) ≤
      ENNReal.ofReal (2 * (InformationTheory.klDiv μ ν).toReal) := by
    rw [ENNReal.ofReal_pow hTV, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_toReal hfin, ENNReal.ofReal_ofNat]
    exact hP'
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp key

end Riesz1

end
