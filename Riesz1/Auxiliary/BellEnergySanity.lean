/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.BellEnergyDefs
public import Riesz1.Auxiliary.BellRandomSum

/-!
# Two-particle block geometry

The two gaps are the block and its complement. This is the boundary geometry
used to check the two singular endpoints in Lemma B.1.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

lemma bell_block_two_complement (X : Configuration 2) :
    blockLength X 1 1 = 2 - blockLength X 0 1 := by
  convert bell_block_complement X 0 (k := 1) (by norm_num) using 1 <;> norm_num

end Riesz1

end
