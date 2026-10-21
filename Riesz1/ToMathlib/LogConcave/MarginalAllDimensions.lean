/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LogConcave.MarginalConcave
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Continuous log-concave marginals, including zero-dimensional fibers -/

public section

open MeasureTheory Set

namespace Riesz1

/-- The continuous marginal theorem including the direct zero-dimensional case. -/
theorem marginal_concaveOn_log_all_dimensions (hPL : External.PrekopaLeindler)
    (d : ℕ) (F : ℝ × EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : Measurable F) (hpos : ∀ p, 0 ≤ F p)
    (hbounded : Bornology.IsBounded (Set.range F))
    (hsupport : Bornology.IsBounded (Function.support F))
    (hlog : ConcaveOn ℝ (Function.support F) (fun p => Real.log (F p)))
    (s : Set ℝ) (hs : Convex ℝ s)
    (hpositive : ∀ x ∈ s, 0 < ∫ z, F (x, z))
    (hcontinuous : ContinuousOn (fun x => ∫ z, F (x, z)) s) :
    ConcaveOn ℝ s (fun x => Real.log (∫ z, F (x, z))) := by
  cases d with
  | zero =>
    simp_rw [volume_euclideanSpace_eq_dirac, integral_dirac] at hpositive ⊢
    refine ⟨hs, ?_⟩
    intro x hx y hy a b ha hb hab
    have h := hlog.2 ((hpositive x hx).ne') ((hpositive y hy).ne') ha hb hab
    simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero] using h
  | succ d =>
    exact marginal_concaveOn_log_of_continuous hPL (d + 1) (by omega) F hF hpos
      hbounded hsupport hlog s hs hpositive hcontinuous

end Riesz1

end
