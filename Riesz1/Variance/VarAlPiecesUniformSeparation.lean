/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircDist

/-!
# A boundary check for scale-uniform mark separation

The fixed marks `0` and `2` can have arbitrarily small positive circular
separation when the circumference varies in `(2, 5/2]`. Thus the
sequence-dependent separation argument in Proposition 5.9 cannot
simply be quantified before all scale sequences. This is a check on that
proposed proof route, not a counterexample to the loop variance claim.
-/

public section

namespace Riesz1.Internal

/-- Distinct fixed real marks need not have a positive separation uniform
over observation circles, even when their lengths lie in a compact interval. -/
theorem varAlPiecesUniform_arbitrarily_close_marks {δ : ℝ} (hδ : 0 < δ) :
    ∃ L : ℝ, 2 < L ∧ L ≤ 5 / 2 ∧ 0 < circDist L 2 ∧ circDist L 2 < δ := by
  let e := min (δ / 2) (1 / 2)
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have hehalf : e ≤ 1 / 2 := min_le_right _ _
  have heδ : e < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hL : 0 < 2 + e := by linarith
  have hd : circDist (2 + e) 2 = e := by
    have hp := circDist_add_int_mul hL (-e) 1
    have hh : |(-e : ℝ)| ≤ (2 + e) / 2 := by rw [abs_neg, abs_of_pos he]; linarith
    rw [show -e + (1 : ℤ) * (2 + e) = 2 by norm_num] at hp
    rw [hp, circDist_eq_abs hL hh, abs_neg, abs_of_pos he]
  exact ⟨2 + e, by linarith, by linarith, by rwa [hd], by rwa [hd]⟩

end Riesz1.Internal
