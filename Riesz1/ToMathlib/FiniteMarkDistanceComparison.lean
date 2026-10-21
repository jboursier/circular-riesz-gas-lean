/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.FiniteMarkDistance
public import Mathlib.Tactic

/-! # Comparing power envelopes for finite marked sets in two metric spaces -/

public section

namespace Riesz1

/-- A comparison of all marked distances compares their capped negative powers.
The finite-cardinality factor avoids any requirement that marked points be separated. -/
theorem cappedMarkDistance_rpow_le_of_dist_le {X Y ι : Type*}
    [MetricSpace X] [PseudoMetricSpace Y] [Fintype ι] [Nonempty ι]
    (marks : ι → X) (marks' : ι → Y) (x : X) (y : Y)
    (hx : ∀ j, x ≠ marks j) {e : ℝ} (he : e ≤ 0)
    (hd : ∀ j, dist x (marks j) ≤ dist y (marks' j)) :
    cappedMarkDistance marks' y ^ e ≤
      ((Fintype.card ι : ℝ) + 1) * cappedMarkDistance marks x ^ e := by
  have hr := cappedMarkDistance_pos marks x hx
  have hterm (j : ι) : dist y (marks' j) ^ e ≤ cappedMarkDistance marks x ^ e :=
    Real.rpow_le_rpow_of_nonpos hr ((cappedMarkDistance_le_dist marks x j).trans (hd j)) he
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have h1 := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr
    (cappedMarkDistance_le_one marks x) he
  exact (cappedMarkDistance_rpow_le_one_add_sum marks' y e).trans (by nlinarith)

end Riesz1
