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
public import Riesz1.Frozen.UnitLength
public import Riesz1.Frozen.Profile
public import Riesz1.Frozen.CompactProfile
public import Riesz1.Frozen.PeriodizedProfile
public import Riesz1.Frozen.ObservationLength
public import Riesz1.Frozen.PrimitiveRegularity
public import Riesz1.Frozen.TransportRegularity
public import Riesz1.Frozen.Scales
public import Riesz1.Frozen.TestData
public import Riesz1.Frozen.PeriodizedProfileL2

/-!
# Admissible profiles: `Riesz1.Admissible`

Fixed profile at either macroscopic or shrinking scales, with uniform A1–A4 data.
See Assumption 1.1 of the paper.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Fixed profile at either macroscopic or shrinking scales, with uniform A1–A4 data.
See Assumption 1.1 of the paper. -/
def Admissible (P : Parameters) (p : Profile) (ell : Scales) (alpha : ℝ) (d : TestData) : Prop :=
  P.val.2 - 1 ≤ alpha ∧ alpha < P.val.2 / 2 ∧
  0 < d.1 ∧ d.1 < P.val.2 ∧ 0 < d.2.1 ∧ 0 < d.2.2.1 ∧
    (((∀ N, (ell N).val = 1) ∧
      PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩ ∧
      TransportRegularity P unitLength ⟨p.val, p.property⟩ d.2.2.2.1 d.2.2.2.2 alpha d.2.2.1) ∨
     (CompactProfile p ∧
      Tendsto (fun n : ℕ => (ell ⟨n + 1, Nat.succ_pos n⟩).val) atTop (𝓝 0) ∧
      ∀ N, let L := observationLength (ell N)
        PrimitiveRegularity L d.1 P.val.2 d.2.1 ⟨periodizedProfile p L, periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P L ⟨periodizedProfile p L, periodizedProfileL2 p (ell N)⟩ d.2.2.2.1 d.2.2.2.2 alpha d.2.2.1))


end Riesz1

end
end
