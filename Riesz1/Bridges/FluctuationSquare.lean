/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Gibbs.FluctuationMoments

/-!
# Bridge: square integrability of the fluctuation under the Gibbs law

The paper states that `Fluct_N[f]` is square integrable and has mean zero. The mean is
`integral_fluctuation_eq_zero` and the linear statistic is `memLp_linearStatistic`. This file
adds the square integrability of the fluctuation itself. The fluctuation is the linear statistic
minus the constant `N ∫ f`, and a constant is square integrable on a probability space.

Main result: `memLp_fluctuation`.
-/

public section

open MeasureTheory

namespace Riesz1

/-- The fluctuation `Fluct_N[f]` of a square integrable function `f` on the unit circle is square
integrable under the Gibbs law. The Gibbs law is a probability measure, by
`modelWellDefined`, so the constant `N ∫ f` is square integrable. -/
theorem memLp_fluctuation (P : Parameters) (N : ℕ+) {f : UnitAddCircle → ℝ}
    (hf : MemLp f 2 volume) :
    MemLp (fun X : Configuration N => fluctuation ⟨f, hf.integrable one_le_two⟩ X) 2
      (gibbsMeasure P N) := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  exact (memLp_linearStatistic P N hf).sub (memLp_const _)

end Riesz1

end
