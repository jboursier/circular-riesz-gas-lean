/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BoundaryCoreTests
public import Riesz1.HelfferSjostrand.VectorEnergySobolev

/-!
# The two presentations of the source form core agree

The source-test subspace used by the scalar core criterion is exactly
the range of the test-submodule Sobolev map.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

/-- The scalar boundary core uses exactly the test map. -/
theorem hsSourceTestSobolev_eq_range {N : ℕ+} (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    hsSourceTestSobolev μ = (hsTestSobolev μ).range := by
  ext v
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨⟨f.toFun, f.smooth, f.periodic, f.boundarySupport⟩, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨⟨f.val, f.property.1, f.property.2.1, f.property.2.2⟩, rfl⟩

end Riesz1
