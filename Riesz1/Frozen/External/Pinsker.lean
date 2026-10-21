/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Pinsker's inequality: `Riesz1.External.Pinsker`

Pinsker's inequality. Ané et al., Sur les inégalités de Sobolev logarithmiques,
author version compiled 27 September 2002, Theorem 8.2.7, p. 133.
Total variation norm (8.2), p. 131 (zbMATH01633816).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1.External

/-- Pinsker's inequality with the event-supremum distance and its coefficient 2.
Mathlib's `etvDist` is the full variation norm, hence the division by 2. -/
def Pinsker : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ ν : Measure Ω),
    IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      (etvDist μ ν / 2) ^ 2 ≤ 2 * InformationTheory.klDiv μ ν

end Riesz1.External

end
end
