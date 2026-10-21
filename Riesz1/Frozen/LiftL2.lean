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
public import Riesz1.Frozen.Length
public import Riesz1.Frozen.Circle
public import Riesz1.Frozen.CentralRep
public import Riesz1.Frozen.Arclength

/-!
# Lifting L² functions to the circle: `Riesz1.liftL2`

L² functions on the line restrict to the central circle representative.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- L² functions on the line restrict to the central circle representative. -/
theorem liftL2 (L : Length) (g : ℝ → ℂ) (hg : MemLp g 2 volume) :
    MemLp (fun x => g (centralRep L x)) 2 (arclength L) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have h := (hg.restrict (Set.Ioc (-L.val / 2) (-L.val / 2 + L.val))).memLp_liftIoc
  have hne : ∀ᵐ x : Circle L, x ≠ ((-L.val / 2 : ℝ) : Circle L) := by
    rw [ae_iff, show {x : Circle L | ¬x ≠ ((-L.val / 2 : ℝ) : Circle L)} =
      {((-L.val / 2 : ℝ) : Circle L)} from Set.ext fun _ => not_not]
    rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
    simp [L.property.le]
  apply h.ae_eq
  filter_upwards [hne] with x hx
  exact AddCircle.liftIoc_eq_liftIco_of_ne hx

end Riesz1

end
end
