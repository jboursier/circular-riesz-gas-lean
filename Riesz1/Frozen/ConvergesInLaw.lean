/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.Tactic

/-!
# Convergence in law: `Riesz1.ConvergesInLaw`

Weak convergence of probability laws against bounded continuous functions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Weak convergence of probability laws against bounded continuous functions. -/
def ConvergesInLaw (laws : ℕ → Measure ℝ) (limit : Measure ℝ) : Prop :=
  (∀ n, IsProbabilityMeasure (laws n)) ∧ IsProbabilityMeasure limit ∧
    ∀ f : ℝ →ᵇ ℝ,
      Tendsto (fun n => ∫ x, f x ∂laws n) atTop (𝓝 (∫ x, f x ∂limit))


end Riesz1

end
end
