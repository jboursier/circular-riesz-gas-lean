/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Prékopa–Leindler inequality: `Riesz1.External.PrekopaLeindler`

The Prékopa–Leindler inequality.
Bobkov–Ledoux, From Brunn–Minkowski to Brascamp–Lieb and to logarithmic
Sobolev inequalities, GAFA 10 (2000), equation (1.1), p. 1028, at t = s = 1/2.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1.External

/-- Midpoint Prékopa–Leindler for bounded nonnegative Borel functions of bounded support.
Integrability is concluded before using the real integrals. -/
def PrekopaLeindler : Prop :=
  ∀ (d : ℕ), 0 < d →
    ∀ (u v w : EuclideanSpace ℝ (Fin d) → ℝ),
      Measurable u → Measurable v → Measurable w →
      (∀ x, 0 ≤ u x) → (∀ x, 0 ≤ v x) → (∀ x, 0 ≤ w x) →
      Bornology.IsBounded (Set.range u) → Bornology.IsBounded (Set.range v) →
      Bornology.IsBounded (Set.range w) →
      Bornology.IsBounded (Function.support u) →
      Bornology.IsBounded (Function.support v) →
      Bornology.IsBounded (Function.support w) →
      (∀ x y, Real.sqrt (u x * v y) ≤ w ((1 / 2 : ℝ) • (x + y))) →
      ∃ (_ : Integrable u volume) (_ : Integrable v volume)
        (_ : Integrable w volume),
        Real.sqrt ((∫ x, u x) * ∫ x, v x) ≤ ∫ x, w x

end Riesz1.External

end
end
