/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Bakry–Émery criterion: `Riesz1.External.BakryEmery`

The Bakry–Émery criterion. Bakry–Émery, Diffusions hypercontractives (1985):

* Proposition 3, formula (4b), p. 187.
* Corollary 2, formula (23), p. 199.
* Proposition 4, pp. 192–196.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Riesz1.External

/-- Smooth Bakry–Émery, with normalization and integrability concluded.
Entropy is `-∫ negMulLog(q²) + negMulLog(∫ q²)`, including the zero test. -/
def BakryEmery : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (w : ℝ), 0 < w →
    ∀ (V : EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ ∞ V →
      (∀ x h, w⁻¹ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x h) h) →
      ∃ (_ : Integrable (fun x => Real.exp (-V x)) volume),
        0 < (∫ x, Real.exp (-V x)) ∧
        let ν : Measure (EuclideanSpace ℝ (Fin d)) :=
          volume.withDensity (fun x =>
            ENNReal.ofReal (Real.exp (-V x) / ∫ y, Real.exp (-V y)))
        IsProbabilityMeasure ν ∧
          ∀ (q : EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ ∞ q →
            Bornology.IsBounded (Set.range q) →
            Bornology.IsBounded (Set.range (gradient q)) →
            ∃ (_ : Integrable (fun x => q x ^ 2) ν)
              (_ : Integrable (fun x => Real.negMulLog (q x ^ 2)) ν)
              (_ : Integrable (fun x => ‖gradient q x‖ ^ 2) ν),
              -(∫ x, Real.negMulLog (q x ^ 2) ∂ν) +
                  Real.negMulLog (∫ x, q x ^ 2 ∂ν) ≤
                2 * w * ∫ x, ‖gradient q x‖ ^ 2 ∂ν

end Riesz1.External

end
end
