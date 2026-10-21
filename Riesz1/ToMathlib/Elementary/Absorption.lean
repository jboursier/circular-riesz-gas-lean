/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sublinear absorption

A nonnegative number `M` with `M ≤ A M^u + B M^v`, where `u, v < 1`, is bounded by a constant
depending only on `A`, `B`, `u`, `v`. The same holds under `M ≤ M^u + A`. The proofs compare `M`
with the threshold above which each power term is at most a fixed fraction of `M`.

This is part of Lemma 4.5 of the paper.
-/

public section

namespace Riesz1

/-- If `c > 0`, `M > 0`, `u < 1` and `c^(1/(1-u)) < M`, then `c M^u < M`. -/
lemma mul_rpow_lt_of_root_lt {c M u : ℝ} (hc : 0 < c) (hM : 0 < M) (hu : u < 1)
    (hlt : c ^ (1 / (1 - u)) < M) : c * M ^ u < M := by
  have hpos : 0 < 1 - u := by linarith
  have hroot : (c ^ (1 / (1 - u))) ^ (1 - u) = c := by
    rw [one_div]
    exact Real.rpow_inv_rpow hc.le hpos.ne'
  -- The threshold `c^(1/(1-u))` lies below `M`, so `c` lies below `M^(1-u)`.
  have hlt' : c < M ^ (1 - u) :=
    calc c = (c ^ (1 / (1 - u))) ^ (1 - u) := hroot.symm
      _ < M ^ (1 - u) := Real.rpow_lt_rpow (Real.rpow_nonneg hc.le _) hlt hpos
  have hprod : M ^ (1 - u) * M ^ u = M := by
    rw [← Real.rpow_add hM, sub_add_cancel, Real.rpow_one]
  calc c * M ^ u < M ^ (1 - u) * M ^ u := mul_lt_mul_of_pos_right hlt' (Real.rpow_pos_of_pos hM u)
    _ = M := hprod

/-- Sublinear absorption with two powers (Lemma 4.5). -/
theorem le_max_of_le_add_rpow (M A B u v : ℝ) (hM : 0 ≤ M) (hA : 0 < A) (hB : 0 < B)
    (hu1 : u < 1) (hv1 : v < 1)
    (h : M ≤ A * M ^ u + B * M ^ v) :
    M ≤ max ((4 * A) ^ (1 / (1 - u))) ((4 * B) ^ (1 / (1 - v))) := by
  rcases hM.eq_or_lt with rfl | hMpos
  · exact le_max_of_le_left (by positivity)
  by_contra hcon
  replace hcon := not_le.1 hcon
  have hX : (4 * A) ^ (1 / (1 - u)) < M := lt_of_le_of_lt (le_max_left _ _) hcon
  have hY : (4 * B) ^ (1 / (1 - v)) < M := lt_of_le_of_lt (le_max_right _ _) hcon
  -- Each power term is below `M / 4`, so the right side of `h` is below `M / 2`.
  have h1 := mul_rpow_lt_of_root_lt (by positivity) hMpos hu1 hX
  have h2 := mul_rpow_lt_of_root_lt (by positivity) hMpos hv1 hY
  linarith

/-- Sublinear absorption with one power (Lemma 4.5). -/
theorem le_max_of_le_rpow_add (M A u : ℝ) (hM : 0 ≤ M)
    (hu1 : u < 1) (h : M ≤ M ^ u + A) : M ≤ max (2 ^ (1 / (1 - u))) (2 * A) := by
  rcases hM.eq_or_lt with rfl | hMpos
  · exact le_max_of_le_left (by positivity)
  by_contra hcon
  replace hcon := not_le.1 hcon
  have hX : (2 : ℝ) ^ (1 / (1 - u)) < M := lt_of_le_of_lt (le_max_left _ _) hcon
  have hY : 2 * A < M := lt_of_le_of_lt (le_max_right _ _) hcon
  -- The power term is below `M / 2`, and so is the constant term.
  have h1 := mul_rpow_lt_of_root_lt (c := 2) (by norm_num) hMpos hu1 hX
  linarith

end Riesz1
