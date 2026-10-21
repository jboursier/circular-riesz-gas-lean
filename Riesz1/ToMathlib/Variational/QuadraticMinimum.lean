/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Uniqueness of a minimum from a positive quadratic remainder -/

public section

namespace Riesz1.Internal

theorem minimizer_iff_of_square_difference {A : Type*} [AddCommGroup A]
    (F Q : A → ℝ) (u : A) (hF : ∀ w, F w = F u + Q (w - u))
    (hQ : ∀ w, 0 ≤ Q w) (hzero : ∀ w, Q w ≤ 0 → w = 0) (x : A) :
    (∀ w, F x ≤ F w) ↔ x = u := by
  constructor
  · intro hmin
    have hm := hmin u
    rw [hF x] at hm
    exact sub_eq_zero.mp (hzero (x - u) (by linarith only [hm]))
  · intro hx
    subst x
    intro w
    rw [hF w]
    exact le_add_of_nonneg_right (hQ (w - u))

theorem quadratic_pairing_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (u w : E) (lu lw : ℝ)
    (hu : B u u = lu) (hw : B u w = lw) (hs : B w u = B u w) :
    B w w - 2 * lw = -lu + B (w - u) (w - u) := by
  simp only [map_sub, sub_apply]
  rw [hs, hw, hu]
  ring

end Riesz1.Internal
