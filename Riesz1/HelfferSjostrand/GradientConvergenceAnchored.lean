/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.AnchoredIntegrationByParts
public import Riesz1.HelfferSjostrand.VectorEnergyAnchored

/-! # The scalar energy identity for anchored tests

The anchored first energy assertion in the proof of Proposition 3.1,
on the anchored law.
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Riesz1

/-- The scalar energy identity on every compact interior anchored test. -/
theorem anchoredGradient_scalar_energy {n : ℕ} {c : ℝ}
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) (f : anchoredTestSubmodule n) :
    (∫ y, ‖gradient (f : AnchoredEuclidean n → ℝ) y‖ ^ 2 ∂anchoredMeasureE χ) =
      ∫ y, (f : AnchoredEuclidean n → ℝ) y * anchoredLangevinExpr χ f y ∂anchoredMeasureE χ := by
  have hμ := isProbabilityMeasure_anchoredMeasureE χ hc
  have h := anchoredIntegrationByParts χ hc f.property.1 f.property.2.1 f.property.2.2
    (isAnchoredH1_of_testFunction χ f f.property.1 f.property.2.1 inferInstance)
  simpa only [real_inner_self_eq_norm_sq, mul_comm] using h.symm

end Riesz1
