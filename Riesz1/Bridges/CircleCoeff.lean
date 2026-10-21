/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.Coeff
public import Riesz1.ToMathlib.HeatKernel.Operators

/-!
# Bridge: the Fourier coefficient on the unit circle

The object `circleCoeff`
of `Riesz1/ToMathlib/HeatKernel/Operators.lean` is the Fourier coefficient of a real function on
`UnitAddCircle`. The `coeff` of `Riesz1/Frozen/Coeff.lean` is the same object at length `L`,
here at `L = 1`.

The `unitLength` of `Riesz1/Frozen/UnitLength.lean` is not imported. `Riesz1.unitLength` is also
declared in `Operators.lean`, and the two declarations cannot share an import closure. The length
`1` is written as `⟨1, one_pos⟩`, which is `unitLength` by definition.

Main result: `circleCoeff_eq_coeff`.
-/

public section

open MeasureTheory

namespace Riesz1

/-- For an integrable real function `f` on the unit circle, the Fourier coefficient `circleCoeff f k`
is `coeff` at length one. The two definitions unfold to the same `fourierCoeff`, and the
instances `Fact (0 < 1)` agree by proof irrelevance. -/
theorem circleCoeff_eq_coeff (f : UnitAddCircle → ℝ)
    (hf : Integrable (fun x : UnitAddCircle => (f x : ℂ)) volume) (k : ℤ) :
    circleCoeff f k = coeff ⟨1, one_pos⟩ ⟨fun x => (f x : ℂ), hf⟩ k :=
  rfl

end Riesz1

end
