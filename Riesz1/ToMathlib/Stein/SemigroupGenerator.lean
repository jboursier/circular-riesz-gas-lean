/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Stein.Semigroup

/-!
# The generator of the Gaussian averaging semigroup

For `σ > 0`, `f` continuously differentiable with `|f| ≤ 1` and `|f'| ≤ 1`, and `t > 0`, the
time derivative of the Gaussian averaging `P_t f (x) = gaussianAveraging σ t f x` satisfies
`∂_t P_t f = σ² ∂_{xx} P_t f - x ∂_x P_t f`. This file differentiates under the Gaussian integral
in the time variable, and matches the result with the spatial formulas of `Semigroup.lean`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace Riesz1

/-- The time derivative of `σ √(1 - e^{-2s})` at `s > 0`. -/
lemma semigroup_hasDerivAt_scale (σ : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s : ℝ => σ * √(1 - rexp (-2 * s)))
      (σ * (rexp (-2 * s) / √(1 - rexp (-2 * s)))) s := by
  have hlt : rexp (-2 * s) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hpos : 0 < √(1 - rexp (-2 * s)) := Real.sqrt_pos.2 (sub_pos.2 hlt)
  have h1 : HasDerivAt (fun s : ℝ => rexp (-2 * s)) (rexp (-2 * s) * (-2)) s := by
    have h := ((hasDerivAt_id' s).const_mul (-2 : ℝ)).exp
    exact h.congr_deriv (by ring)
  have h2 : HasDerivAt (fun s : ℝ => 1 - rexp (-2 * s)) (-(rexp (-2 * s) * (-2))) s :=
    h1.const_sub 1
  have h3 := h2.sqrt (sub_pos.2 hlt).ne'
  refine (h3.const_mul σ).congr_deriv ?_
  field_simp

/-- The ratio `e^{-2s} / √(1 - e^{-2s})` is nonnegative and at most `1 / √(1 - e^{-t})` for
`s > t / 2`. -/
lemma semigroup_ratio_bound {t s : ℝ} (ht : 0 < t) (hs : t / 2 < s) :
    0 ≤ rexp (-2 * s) / √(1 - rexp (-2 * s)) ∧
      rexp (-2 * s) / √(1 - rexp (-2 * s)) ≤ 1 / √(1 - rexp (-t)) := by
  have hp1 : rexp (-2 * s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hlt : rexp (-t) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hpt : rexp (-2 * s) ≤ rexp (-t) := Real.exp_le_exp.2 (by linarith)
  have hpos : 0 < √(1 - rexp (-t)) := Real.sqrt_pos.2 (sub_pos.2 hlt)
  have hq : √(1 - rexp (-t)) ≤ √(1 - rexp (-2 * s)) := Real.sqrt_le_sqrt (by linarith)
  have hqpos : 0 < √(1 - rexp (-2 * s)) := lt_of_lt_of_le hpos hq
  refine ⟨div_nonneg (Real.exp_pos _).le hqpos.le, ?_⟩
  calc rexp (-2 * s) / √(1 - rexp (-2 * s)) ≤ 1 / √(1 - rexp (-2 * s)) :=
        div_le_div_of_nonneg_right hp1 hqpos.le
    _ ≤ 1 / √(1 - rexp (-t)) := one_div_le_one_div_of_le hpos hq

/-- The time derivative of the Gaussian averaging, for `t > 0`, as a Gaussian integral. -/
theorem gaussianAveraging_hasDerivAt_t {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hfb : ∀ y, |f y| ≤ 1) (hf' : ∀ y, |deriv f y| ≤ 1) (x : ℝ) :
    HasDerivAt (fun s => gaussianAveraging σ s f x)
      (∫ z, deriv f (rexp (-t) * x + σ * √(1 - rexp (-2 * t)) * z) *
        (-rexp (-t) * x + σ * (rexp (-2 * t) / √(1 - rexp (-2 * t))) * z)
          ∂(gaussianReal 0 1)) t := by
  have hfc : Continuous f := hf.continuous
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hdfc : Continuous (deriv f) := hf.continuous_deriv_one
  -- The points of the ball of radius `t / 2` around `t` satisfy `t / 2 < s`.
  have hball : ∀ s ∈ Metric.ball t (t / 2), t / 2 < s := by
    intro s hs
    have h := Metric.mem_ball.1 hs
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.1]
  -- The derivative of the integrand in `s`, for each Gaussian point `z`.
  have hdiffz : ∀ z s : ℝ, 0 < s → HasDerivAt
      (fun s => f (rexp (-s) * x + σ * √(1 - rexp (-2 * s)) * z))
      (deriv f (rexp (-s) * x + σ * √(1 - rexp (-2 * s)) * z) *
        (-rexp (-s) * x + σ * (rexp (-2 * s) / √(1 - rexp (-2 * s))) * z)) s := by
    intro z s hs
    have hA : HasDerivAt (fun s : ℝ => rexp (-s) * x) (-rexp (-s) * x) s := by
      have h := ((hasDerivAt_neg s).exp).mul_const x
      exact h.congr_deriv (by ring)
    have hB : HasDerivAt (fun s : ℝ => σ * √(1 - rexp (-2 * s)) * z)
        (σ * (rexp (-2 * s) / √(1 - rexp (-2 * s))) * z) s :=
      (semigroup_hasDerivAt_scale σ hs).mul_const z
    exact (hfd _).hasDerivAt.comp s (hA.add hB)
  -- The uniform bound of the integrand's derivative on the ball.
  have hbd : ∀ z s : ℝ, s ∈ Metric.ball t (t / 2) →
      ‖deriv f (rexp (-s) * x + σ * √(1 - rexp (-2 * s)) * z) *
        (-rexp (-s) * x + σ * (rexp (-2 * s) / √(1 - rexp (-2 * s))) * z)‖
        ≤ |x| + σ * (1 / √(1 - rexp (-t))) * |z| := by
    intro z s hs
    have hs' := hball s hs
    obtain ⟨hg0, hg1⟩ := semigroup_ratio_bound ht hs'
    have he0 : 0 < rexp (-s) := Real.exp_pos _
    have he1 : rexp (-s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hE : |-rexp (-s) * x + σ * (rexp (-2 * s) / √(1 - rexp (-2 * s))) * z|
        ≤ |x| + σ * (1 / √(1 - rexp (-t))) * |z| := by
      calc |-rexp (-s) * x + σ * (rexp (-2 * s) / √(1 - rexp (-2 * s))) * z|
          ≤ |-rexp (-s) * x| + |σ * (rexp (-2 * s) / √(1 - rexp (-2 * s))) * z| :=
            abs_add_le _ _
        _ = rexp (-s) * |x| + σ * (rexp (-2 * s) / √(1 - rexp (-2 * s))) * |z| := by
            simp only [abs_mul, abs_neg, abs_of_pos he0, abs_of_pos hσ, abs_of_nonneg hg0]
        _ ≤ |x| + σ * (1 / √(1 - rexp (-t))) * |z| :=
            add_le_add (mul_le_of_le_one_left (abs_nonneg x) he1)
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg1 hσ.le) (abs_nonneg z))
    rw [Real.norm_eq_abs, abs_mul]
    calc _ ≤ 1 * (|x| + σ * (1 / √(1 - rexp (-t))) * |z|) :=
          mul_le_mul (hf' _) hE (abs_nonneg _) zero_le_one
      _ = |x| + σ * (1 / √(1 - rexp (-t))) * |z| := one_mul _
  have hmain := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 1)
    (F := fun s z => f (rexp (-s) * x + σ * √(1 - rexp (-2 * s)) * z))
    (F' := fun s z => deriv f (rexp (-s) * x + σ * √(1 - rexp (-2 * s)) * z) *
      (-rexp (-s) * x + σ * (rexp (-2 * s) / √(1 - rexp (-2 * s))) * z))
    (x₀ := t) (s := Metric.ball t (t / 2))
    (bound := fun z => |x| + σ * (1 / √(1 - rexp (-t))) * |z|)
    (Metric.ball_mem_nhds t (half_pos ht))
    (Eventually.of_forall fun s => (hfc.comp (continuous_const.add
      (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (semigroup_integrable_comp hfc hfb (rexp (-t) * x) (σ * √(1 - rexp (-2 * t))))
    ((hdfc.comp (continuous_const.add (continuous_const.mul continuous_id))).mul
      (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
    (Eventually.of_forall fun z s hs => hbd z s hs)
    ((integrable_const _).add (stein_integrable_abs_std.const_mul _))
    (Eventually.of_forall fun z s hs => hdiffz z s (by linarith [hball s hs, half_pos ht]))).2
  exact hmain

/-- The generator identity `∂_t P_t f = σ² ∂_{xx} P_t f - x ∂_x P_t f` for `t > 0`. -/
theorem gaussianAveraging_generator {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hfb : ∀ y, |f y| ≤ 1) (hf' : ∀ y, |deriv f y| ≤ 1) (x : ℝ) :
    deriv (fun s => gaussianAveraging σ s f x) t
      = σ ^ 2 * deriv (deriv (gaussianAveraging σ t f)) x
        - x * deriv (gaussianAveraging σ t f) x := by
  have hsp := gaussianAveraging_spatial hσ ht hf hfb hf'
  rw [(gaussianAveraging_hasDerivAt_t hσ ht hf hfb hf' x).deriv, hsp.2.2 x, hsp.2.1 x]
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hdfc : Continuous (deriv f) := hf.continuous_deriv_one
  -- Split the integrand into its two Gaussian moments.
  have hsplit : ∫ z, deriv f (rexp (-t) * x + σ * √(1 - rexp (-2 * t)) * z) *
      (-rexp (-t) * x + σ * (rexp (-2 * t) / √(1 - rexp (-2 * t))) * z) ∂(gaussianReal 0 1)
      = (-(rexp (-t) * x)) * ∫ z, deriv f (rexp (-t) * x + σ * √(1 - rexp (-2 * t)) * z)
          ∂(gaussianReal 0 1)
        + (σ * (rexp (-2 * t) / √(1 - rexp (-2 * t)))) * ∫ z,
          z * deriv f (rexp (-t) * x + σ * √(1 - rexp (-2 * t)) * z) ∂(gaussianReal 0 1) := by
    have e : (fun z : ℝ => deriv f (rexp (-t) * x + σ * √(1 - rexp (-2 * t)) * z) *
        (-rexp (-t) * x + σ * (rexp (-2 * t) / √(1 - rexp (-2 * t))) * z))
        = fun z => (-(rexp (-t) * x)) * deriv f (rexp (-t) * x + σ * √(1 - rexp (-2 * t)) * z)
          + (σ * (rexp (-2 * t) / √(1 - rexp (-2 * t))))
            * (z * deriv f (rexp (-t) * x + σ * √(1 - rexp (-2 * t)) * z)) := by
      funext z
      ring
    rw [e, integral_add ((semigroup_integrable_comp hdfc hf' _ _).const_mul _)
      ((stein_integrable_mul_id hdfc hf' _ _).const_mul _), integral_const_mul, integral_const_mul]
  rw [hsplit]
  field_simp
  ring

end Riesz1
