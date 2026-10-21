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
public import Riesz1.Frozen.Parameters
public import Riesz1.Frozen.Length
public import Riesz1.Frozen.Circle
public import Riesz1.Frozen.Arclength
public import Riesz1.Frozen.Coeff
public import Riesz1.Frozen.TransportCoeffs
public import Riesz1.Frozen.ComplexL2Integrable

/-!
# Regularity of the transport: `Riesz1.TransportRegularity`

(A2)–(A3) of Assumption 1.1, via an L² representative of the transport,
smooth off distinct marks. Derivatives are taken on real lifts.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- (A2)–(A3) of Assumption 1.1, via an L² representative of the transport,
smooth off distinct marks. Derivatives are taken on real lifts. -/
def TransportRegularity (P : Parameters) (L : Length) (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (p : ℕ+) (marks : Fin (p : ℕ) → ℝ) (alpha C : ℝ) : Prop := by
  haveI : Fact (0 < L.val) := ⟨L.property⟩
  exact
  Function.Injective (fun j => (marks j : Circle L)) ∧
  ∃ psi : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
    (∀ k, coeff L ⟨(fun x => (psi.val x : ℂ)), complexL2Integrable L _ psi.property⟩ k = transportCoeffs P L f k) ∧
    let lift := fun x : ℝ => psi.val (x : Circle L)
    ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
      ContDiffAt ℝ 2 lift x ∧
      |deriv (deriv lift) x| ≤ C *
        ((if dist (x : Circle L) 0 ≤ 1 then
            ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - alpha) else 0) +
         (if 1 ≤ dist (x : Circle L) 0 then dist (x : Circle L) 0 ^ (-3 + P.val.2) else 0))


end Riesz1

end
end
