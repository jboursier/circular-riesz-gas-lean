/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HolderSingularIntegral
public import Riesz1.Frozen.PrimitiveRegularity

/-!
# The continuous singular integral of the admissible primitive

Analytic step: the Hölder bound in (A1) gives an absolutely
convergent, continuous singular integral on every observation circle, bounded independently
of its length. Identifying this integral with the Fourier-defined transport is a separate
step, not asserted here.
-/

public section

open MeasureTheory

namespace Riesz1

/-- A Hölder function on a circle has the same bound on residuals along real translations.
The quotient map can only decrease distances. -/
theorem holderBound_residual_le {L : Length} {r B : ℝ} {f : Circle L → ℝ}
    (hf : HolderBound L r B f) (hr : 0 ≤ r) (hB : 0 ≤ B) (x : Circle L) (u : ℝ) :
    |f x - f (x - (u : Circle L))| ≤ B * |u| ^ r := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hd : dist x (x - (u : Circle L)) ≤ |u| := by
    rw [dist_eq_norm, sub_sub_cancel]
    exact le_trans (QuotientAddGroup.norm_mk_le_norm (m := u)) (le_of_eq (Real.norm_eq_abs u))
  exact (hf.2.2 x (x - (u : Circle L))).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hd hr) hB)

/-- The residual also has a bound at large translation distances. -/
theorem holderBound_residual_le_two {L : Length} {r B : ℝ} {f : Circle L → ℝ}
    (hf : HolderBound L r B f) (x : Circle L) (u : ℝ) :
    |f x - f (x - (u : Circle L))| ≤ 2 * B := by
  calc |f x - f (x - (u : Circle L))|
      ≤ |f x| + |f (x - (u : Circle L))| := abs_sub _ _
    _ ≤ B + B := add_le_add (hf.2.1 _) (hf.2.1 _)
    _ = 2 * B := by ring

/-- Absolute convergence, continuity and a uniform bound for the unnormalized singular
integral of the primitive. With `τ = 1 - s` and `r = 1 - s + η` this is the continuity
construction. -/
theorem holderBound_singular_integral {L : Length} {τ r B : ℝ} {f : Circle L → ℝ}
    (hf : HolderBound L r B f) (hτ : 0 < τ) (hr : τ < r) (hB : 0 ≤ B) :
    (∀ x : Circle L, Integrable (fun u : ℝ =>
      (f x - f (x - (u : Circle L))) * |u| ^ (-(1 + τ)))) ∧
    Continuous (fun x : Circle L => ∫ u : ℝ,
      (f x - f (x - (u : Circle L))) * |u| ^ (-(1 + τ))) ∧
    ∀ x : Circle L, |∫ u : ℝ,
      (f x - f (x - (u : Circle L))) * |u| ^ (-(1 + τ))| ≤
        ∫ u : ℝ, holderSingularEnvelope τ r B u := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hm (x : Circle L) : Measurable (fun u : ℝ => f x - f (x - (u : Circle L))) :=
    (continuous_const.sub (hf.1.comp (continuous_const.sub (AddCircle.continuous_mk' L.val)))).measurable
  have hc (u : ℝ) : Continuous (fun x : Circle L => f x - f (x - (u : Circle L))) :=
    hf.1.sub (hf.1.comp (continuous_id.sub continuous_const))
  have hs := holderBound_residual_le hf (by linarith : 0 ≤ r) hB
  have hl := holderBound_residual_le_two hf
  exact ⟨integrable_singular_residual hτ hr hB hm hs hl,
    continuous_singular_residual_integral hτ hr hB hm hc hs hl,
    abs_singular_residual_integral_le hτ hB hr hs hl⟩

end Riesz1
