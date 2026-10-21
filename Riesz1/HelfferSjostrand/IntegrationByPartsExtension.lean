/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.Neumann

/-!
# Internal extension from the periodic smooth core

The continuity step in the proof of the integration by parts identity. This helper
extends a smooth-core variational identity to the completion. It does
not assert the smooth integration by parts identity for `hsLangevin`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1.Internal

variable {N : ℕ+} (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]

/-- An identity against every smooth lift extends to every Sobolev jet.
The smooth identity is an explicit hypothesis of this internal helper. -/
theorem hsNeumannGraph_mem_of_smooth (f : HsSobolev μ) (a : Lp ℝ 2 μ)
    (h : ∀ φ : hsSmoothCore N, hsDirichletForm μ f (hsSobolevOfSmooth μ φ) =
      inner ℝ a (hsSobolevValue μ (hsSobolevOfSmooth μ φ))) :
    (f, a) ∈ hsNeumannGraph μ := by
  have heq : hsDirichletForm μ f = fun g => inner ℝ a (hsSobolevValue μ g) :=
    (denseRange_hsSobolevOfSmooth μ).equalizer (continuous_hsDirichletForm μ f)
      (continuous_const.inner (hsSobolevValue μ).continuous) (funext h)
  exact fun g => congrFun heq g

end Riesz1.Internal

end
