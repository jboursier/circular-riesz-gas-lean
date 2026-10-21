/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Mollifying bounded Lipschitz functions

For every `ε > 0` there is a smooth bump `ψ` with `ψ ≥ 0`, `∫ ψ = 1`, and `ψ = 0` outside
`(-ε, ε)`. Convolving a bounded Lipschitz function `g` with `ψ` gives a `C¹` function `h`.
This `h` keeps the bound of `g`, has derivative bounded by the Lipschitz constant of `g`, and
stays within `L ε` of `g`. This is the approximation step that reduces bounded Lipschitz tests
to the `C¹` test class of `Riesz1.BLTest`.
-/

public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace Riesz1

/-- For every `ε > 0` there is a smooth nonnegative bump `ψ` of total mass one that vanishes
outside `(-ε, ε)`. -/
lemma exists_mollifier {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ (∀ t, 0 ≤ ψ t) ∧
      ∫ t, ψ t = 1 ∧ ∀ t, ε ≤ |t| → ψ t = 0 := by
  let bump : ContDiffBump (0 : ℝ) :=
    { rIn := ε / 2, rOut := ε, rIn_pos := half_pos hε, rIn_lt_rOut := half_lt_self hε }
  refine ⟨bump.normed volume, bump.contDiff_normed, bump.hasCompactSupport_normed,
    bump.nonneg_normed, bump.integral_normed, fun t ht => ?_⟩
  rw [bump.normed_def, bump.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact ht), zero_div]

/-- Convolving a bounded Lipschitz function `g` with the bump `ψ` of radius `ε` gives a `C¹`
function `h`. The function `h` is bounded by the same bound `M` as `g`, has derivative bounded
by the Lipschitz constant `L`, and satisfies `|h x - g x| ≤ L ε` for every `x`. -/
lemma exists_mollified {g : ℝ → ℝ} {M : ℝ} {L : ℝ≥0} {ε : ℝ} (hε : 0 < ε)
    (hM : ∀ x, |g x| ≤ M) (hL : LipschitzWith L g) :
    ∃ h : ℝ → ℝ, ContDiff ℝ 1 h ∧ (∀ x, |h x| ≤ M) ∧ (∀ x, |deriv h x| ≤ L) ∧
      ∀ x, |h x - g x| ≤ L * ε := by
  obtain ⟨ψ, hψ, hψc, hψ0, hψ1, hψz⟩ := exists_mollifier hε
  have hgc : Continuous g := hL.continuous
  have hψi : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hψc
  -- The convolution `h x = ∫ t, ψ t * g (x - t)` is the mollification of `g`.
  set h : ℝ → ℝ := convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume with hh
  have hform : ∀ x, h x = ∫ t, ψ t * g (x - t) := fun x => by
    simp [hh, convolution_def]
  have hcd : ContDiff ℝ 1 h :=
    hψc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hψ hgc.locallyIntegrable
  -- Each integrand is dominated by the integrable function `ψ t * M`.
  have hbound : ∀ x t, ‖ψ t * g (x - t)‖ ≤ ψ t * M := by
    intro x t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 t)]
    exact mul_le_mul_of_nonneg_left (hM _) (hψ0 t)
  have hint : ∀ x, Integrable (fun t => ψ t * g (x - t)) := fun x =>
    Integrable.mono' (hψi.mul_const M)
      (hψ.continuous.mul (hgc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
      (ae_of_all _ (hbound x))
  -- Bound on `h`: the mass of `ψ` is one.
  have hbdd : ∀ x, |h x| ≤ M := by
    intro x
    rw [hform, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hψi.mul_const M) (ae_of_all _ (hbound x))).trans_eq ?_
    rw [integral_mul_const, hψ1, one_mul]
  -- Lipschitz bound on `h`, with the same constant as `g`.
  have hlip : LipschitzWith L h := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, hform, hform, ← integral_sub (hint x) (hint y)]
    have hb : ∀ t, ‖ψ t * g (x - t) - ψ t * g (y - t)‖ ≤ ψ t * ((L : ℝ) * dist x y) := by
      intro t
      rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 t)]
      refine mul_le_mul_of_nonneg_left ?_ (hψ0 t)
      calc |g (x - t) - g (y - t)| = dist (g (x - t)) (g (y - t)) := (Real.dist_eq _ _).symm
        _ ≤ L * dist (x - t) (y - t) := hL.dist_le_mul _ _
        _ = L * dist x y := by rw [dist_sub_right]
    refine (norm_integral_le_of_norm_le (hψi.mul_const _) (ae_of_all _ hb)).trans_eq ?_
    rw [integral_mul_const, hψ1, one_mul]
  -- The derivative of a Lipschitz function is bounded by its Lipschitz constant.
  have hderiv : ∀ x, |deriv h x| ≤ L := fun x => by
    rw [← Real.norm_eq_abs]
    exact norm_deriv_le_of_lipschitz hlip
  -- Approximation: `h x - g x = ∫ t, ψ t * (g (x - t) - g x)`, and the integrand is small
  -- because `ψ t = 0` unless `|t| < ε`.
  have happrox : ∀ x, |h x - g x| ≤ L * ε := by
    intro x
    have hgx : ∫ t, ψ t * g x = g x := by rw [integral_mul_const, hψ1, one_mul]
    rw [hform, ← hgx, ← integral_sub (hint x) (hψi.mul_const (g x)), ← Real.norm_eq_abs]
    have hb : ∀ t, ‖ψ t * g (x - t) - ψ t * g x‖ ≤ ψ t * ((L : ℝ) * ε) := by
      intro t
      rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 t)]
      by_cases ht : ε ≤ |t|
      · simp [hψz t ht]
      · refine mul_le_mul_of_nonneg_left ?_ (hψ0 t)
        calc |g (x - t) - g x| = dist (g (x - t)) (g x) := (Real.dist_eq _ _).symm
          _ ≤ L * dist (x - t) x := hL.dist_le_mul _ _
          _ = L * |t| := by rw [Real.dist_eq, sub_sub_cancel_left, abs_neg]
          _ ≤ L * ε := mul_le_mul_of_nonneg_left (not_le.mp ht).le (NNReal.coe_nonneg L)
    refine (norm_integral_le_of_norm_le (hψi.mul_const _) (ae_of_all _ hb)).trans_eq ?_
    rw [integral_mul_const, hψ1, one_mul]
  exact ⟨h, hcd, hbdd, hderiv, happrox⟩

end Riesz1
