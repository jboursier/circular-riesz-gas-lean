/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Stein.Formula
public import Riesz1.ToMathlib.Stein.RossInterpolation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Ross's estimates for the bounded standard Stein solution

Absolute continuity and an almost everywhere bound on the derivative give a Lipschitz test
function. Interval averages reduce its estimates to continuously differentiable tests.
The Gaussian interpolation estimates then bound the integrating-factor solution and its derivative.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped Interval

namespace Riesz1
namespace Internal

/-- The smooth standard Stein estimates, with derivative bound one. -/
lemma ross_smooth_bounds {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hf' : ∀ y, |deriv f y| ≤ 1) (x : ℝ) :
    |steinSolution 1 f x| ≤ 1 ∧ |deriv (steinSolution 1 f) x| ≤ √(2 / π) := by
  have hd : Differentiable ℝ (rossInterpolant 1 f) := fun y =>
    (ross_hasDerivAt_solution hf zero_lt_one hf' y).2.differentiableAt
  have he := stein_eq_formula zero_lt_one hf.continuous
    (A := |f 0|) (B := 1) (fun y => by
      have h := ross_lipschitz hf hf' y 0
      rw [sub_zero] at h
      linarith [abs_sub_abs_le_abs_sub (f y) (f 0)]) hd
    ⟨1, fun _ => ross_abs_solution_le hf'⟩ (fun y => ross_ode (x := y) hf zero_lt_one hf')
  rw [← he]
  exact ⟨ross_abs_solution_le hf', by simpa using ross_abs_deriv_solution_le hf zero_lt_one hf'⟩

/-- An almost everywhere bound on the derivative of an absolutely continuous test is Lipschitz. -/
lemma ross_lipschitz_of_ac {h : ℝ → ℝ} (hAC : ∀ a b, AbsolutelyContinuousOnInterval h a b)
    {L : ℝ} (hd : ∀ᵐ x, |deriv h x| ≤ L) (x y : ℝ) :
    |h x - h y| ≤ L * |x - y| := by
  rw [← (hAC y x).integral_deriv_eq_sub, ← Real.norm_eq_abs]
  have hb : ∀ᵐ t, t ∈ Ι y x → ‖deriv h t‖ ≤ L := by
    filter_upwards [hd] with t ht _
    simpa [Real.norm_eq_abs] using ht
  simpa [Real.dist_eq, abs_sub_comm] using
    intervalIntegral.norm_integral_le_of_norm_le_const_ae hb

/-- Interval averages of a Lipschitz test are continuously differentiable and retain its bound. -/
lemma ross_interval_average {h : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hl : ∀ x y, |h x - h y| ≤ L * |x - y|) {ε : ℝ} (hε : 0 < ε) :
    let H := fun x => (∫ t in x..x + ε, h t) / ε
    ContDiff ℝ 1 H ∧ (∀ x, |deriv H x| ≤ L) ∧ (∀ x, |H x - h x| ≤ L * ε) := by
  have hc : Continuous h := (LipschitzWith.of_dist_le_mul (K := ⟨L, hL⟩)
    (fun x y => by
      change |h x - h y| ≤ L * |x - y|
      exact hl x y)).continuous
  let F := fun x => ∫ t in (0 : ℝ)..x, h t
  have hF : ∀ x, HasDerivAt F (h x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he : (fun x => (∫ t in x..x + ε, h t) / ε) =
      fun x => (F (x + ε) - F x) / ε := by
    funext x
    congr 1
    have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable 0 x) (hc.intervalIntegrable x (x + ε))
    dsimp [F]
    linarith
  have hd : ∀ x, HasDerivAt (fun x => (∫ t in x..x + ε, h t) / ε)
      ((h (x + ε) - h x) / ε) x := by
    intro x
    rw [he]
    have hin : HasDerivAt (fun y : ℝ => y + ε) 1 x := (hasDerivAt_id' x).add_const ε
    have hshift : HasDerivAt (fun y => F (y + ε)) (h (x + ε) * 1) x :=
      HasDerivAt.comp (h₂ := F) (h₂' := h (x + ε)) (h := fun y : ℝ => y + ε) x
        (hF (x + ε)) hin
    have hd0 : HasDerivAt (fun y => (F (y + ε) - F y) / ε)
        ((h (x + ε) * 1 - h x) / ε) x :=
      (hshift.sub (hF x)).div_const ε
    simpa only [mul_one] using hd0
  refine ⟨contDiff_one_iff_deriv.2 ⟨fun x => (hd x).differentiableAt, ?_⟩, ?_, ?_⟩
  · have he' : deriv (fun x => (∫ t in x..x + ε, h t) / ε) =
        fun x => (h (x + ε) - h x) / ε := funext fun x => (hd x).deriv
    rw [he']
    fun_prop
  · intro x
    rw [(hd x).deriv, abs_div, abs_of_pos hε, div_le_iff₀ hε]
    simpa [abs_of_pos hε] using hl (x + ε) x
  · intro x
    have hb : ∀ t ∈ Ι x (x + ε), ‖h t - h x‖ ≤ L * ε := by
      intro t ht
      rw [uIoc_of_le (by linarith)] at ht
      obtain ⟨ht1, ht2⟩ := ht
      rw [Real.norm_eq_abs]
      refine (hl t x).trans ?_
      rw [abs_of_nonneg (by linarith : 0 ≤ t - x)]
      exact mul_le_mul_of_nonneg_left (by linarith) hL
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
    have hs : (∫ t in x..x + ε, h t - h x) = (∫ t in x..x + ε, h t) - ε * h x := by
      rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
        intervalIntegral.integral_const]
      simp [smul_eq_mul]
    rw [hs, Real.norm_eq_abs, show x + ε - x = ε by ring,
      abs_of_pos hε] at hi
    have he' : (∫ t in x..x + ε, h t) / ε - h x =
        ((∫ t in x..x + ε, h t) - ε * h x) / ε := by field_simp
    rw [he', abs_div, abs_of_pos hε, div_le_iff₀ hε]
    nlinarith [hi]

/-- A Lipschitz test has at most linear growth. -/
lemma ross_growth {h : ℝ → ℝ} {L : ℝ}
    (hl : ∀ x y, |h x - h y| ≤ L * |x - y|) (x : ℝ) :
    |h x| ≤ |h 0| + L * |x| := by
  have ht := hl x 0
  rw [sub_zero] at ht
  linarith [abs_sub_abs_le_abs_sub (h x) (h 0)]

/-- Uniform perturbations of a Lipschitz test give pointwise small changes in its solution. -/
lemma ross_formula_stability {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {A B C D δ : ℝ} (hfb : ∀ y, |f y| ≤ A + B * |y|)
    (hgb : ∀ y, |g y| ≤ C + D * |y|) (hfg : ∀ y, |f y - g y| ≤ δ) (x : ℝ) :
    |steinSolution 1 f x - steinSolution 1 g x| ≤
      rexp (x ^ 2 / 2) * (∫ y in Iic x, rexp (-(y ^ 2) / 2)) * (2 * δ) := by
  have hiF : Integrable f (gaussianReal 0 1) :=
    ((integrable_const A).add (stein_integrable_abs_std.const_mul B)).mono'
      hf.aestronglyMeasurable (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hfb y)
  have hiG : Integrable g (gaussianReal 0 1) :=
    ((integrable_const C).add (stein_integrable_abs_std.const_mul D)).mono'
      hg.aestronglyMeasurable (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hgb y)
  let cf := ∫ z, f z ∂(gaussianReal 0 1)
  let cg := ∫ z, g z ∂(gaussianReal 0 1)
  have hc : |cf - cg| ≤ δ := by
    dsimp [cf, cg]
    rw [← integral_sub hiF hiG, ← Real.norm_eq_abs]
    simpa using norm_integral_le_of_norm_le_const
      (μ := gaussianReal 0 1) (f := fun y => f y - g y) (C := δ)
      (Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hfg y)
  have hiF' := stein_integrable_weight zero_lt_one (hf.sub (continuous_const (y := cf)))
    (A := A + |cf|) (B := B) (fun y => by
      change |f y - cf| ≤ A + |cf| + B * |y|
      linarith [hfb y, abs_sub (f y) cf])
  have hiG' := stein_integrable_weight zero_lt_one (hg.sub (continuous_const (y := cg)))
    (A := C + |cg|) (B := D) (fun y => by
      change |g y - cg| ≤ C + |cg| + D * |y|
      linarith [hgb y, abs_sub (g y) cg])
  simp only [one_pow, mul_one, Pi.sub_apply] at hiF' hiG'
  have hiW : Integrable (fun y : ℝ => rexp (-(y ^ 2) / 2)) := by
    convert integrable_exp_neg_mul_sq (by norm_num : 0 < (1 : ℝ) / 2) using 1
    ext y
    congr 1
    ring
  have hb : ∀ y, ‖rexp (-(y ^ 2) / 2) * (f y - cf) -
      rexp (-(y ^ 2) / 2) * (g y - cg)‖ ≤ rexp (-(y ^ 2) / 2) * (2 * δ) := by
    intro y
    rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    have he : f y - cf - (g y - cg) = (f y - g y) - (cf - cg) := by ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith [hfg y, hc])
  have hI := norm_integral_le_of_norm_le (μ := volume.restrict (Iic x))
    ((hiW.mul_const (2 * δ)).integrableOn) (Eventually.of_forall hb)
  rw [integral_sub hiF'.integrableOn hiG'.integrableOn, integral_mul_const,
    Real.norm_eq_abs] at hI
  dsimp [cf, cg] at hI
  simp only [steinSolution, one_pow, mul_one, inv_one, one_mul]
  rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hI (Real.exp_nonneg (x ^ 2 / 2))

/-- The integrating-factor solution of a test with Lipschitz constant one has the standard bounds. -/
lemma ross_unit_formula_bounds {h : ℝ → ℝ}
    (hl : ∀ x y, |h x - h y| ≤ |x - y|) (x : ℝ) :
    |steinSolution 1 h x| ≤ 1 ∧ |deriv (steinSolution 1 h) x| ≤ √(2 / π) := by
  have hl' : ∀ x y, |h x - h y| ≤ 1 * |x - y| := by simpa using hl
  have hc : Continuous h := (LipschitzWith.of_dist_le_mul (K := 1)
    (fun a b => by simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hl a b)).continuous
  let ε := fun n : ℕ => (1 : ℝ) / (n + 1)
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let H := fun n x => (∫ t in x..x + ε n, h t) / ε n
  have hH := fun n => ross_interval_average zero_le_one hl' (hε n)
  have hHb : ∀ n y, |H n y| ≤ |h 0| + ε n + 1 * |y| := by
    intro n y
    have hb := (hH n).2.2 y
    have hg := ross_growth hl' y
    dsimp [H] at *
    linarith [abs_sub_abs_le_abs_sub (H n y) (h y)]
  have hsol : Tendsto (fun n => steinSolution 1 (H n) x) atTop (𝓝 (steinSolution 1 h x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb := fun n => ross_formula_stability (hH n).1.continuous hc (hHb n)
      (ross_growth hl') (fun y => by simpa [H] using (hH n).2.2 y) x
    refine squeeze_zero' (g := fun n =>
      (rexp (x ^ 2 / 2) * ∫ y in Iic x, rexp (-(y ^ 2) / 2)) * (2 * ε n))
      (Eventually.of_forall fun n => norm_nonneg _) ?_ ?_
    · exact Eventually.of_forall fun n => by simpa [Real.norm_eq_abs] using hb n
    · simpa using (hεlim.const_mul 2).const_mul
        (rexp (x ^ 2 / 2) * ∫ y in Iic x, rexp (-(y ^ 2) / 2))
  have htest : Tendsto (fun n => H n x) atTop (𝓝 (h x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
      (Eventually.of_forall fun n => by simpa [Real.norm_eq_abs, H] using (hH n).2.2 x) hεlim
  have hiH : ∀ n, Integrable (H n) (gaussianReal 0 1) := fun n =>
    ((integrable_const (|h 0| + ε n)).add (stein_integrable_abs_std.const_mul 1)).mono'
      (hH n).1.continuous.aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hHb n y)
  have hih : Integrable h (gaussianReal 0 1) :=
    ((integrable_const |h 0|).add (stein_integrable_abs_std.const_mul 1)).mono'
      hc.aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact ross_growth hl' y)
  have hcLim : Tendsto (fun n => ∫ z, H n z ∂(gaussianReal 0 1)) atTop
      (𝓝 (∫ z, h z ∂(gaussianReal 0 1))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hεlim
    refine Eventually.of_forall fun n => ?_
    rw [← integral_sub (hiH n) hih]
    simpa using norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
      (f := fun z => H n z - h z) (C := ε n)
      (Eventually.of_forall fun z => by
        simpa [Real.norm_eq_abs, H] using (hH n).2.2 z)
  have hd : deriv (steinSolution 1 h) x =
      x * steinSolution 1 h x + h x - ∫ z, h z ∂(gaussianReal 0 1) := by
    simpa using (stein_hasDerivAt_formula zero_lt_one hc (ross_growth hl') x).deriv
  have hdH : ∀ n, deriv (steinSolution 1 (H n)) x =
      x * steinSolution 1 (H n) x + H n x - ∫ z, H n z ∂(gaussianReal 0 1) := by
    intro n
    simpa using (stein_hasDerivAt_formula zero_lt_one (hH n).1.continuous (hHb n) x).deriv
  have hdLim : Tendsto (fun n => deriv (steinSolution 1 (H n)) x) atTop
      (𝓝 (deriv (steinSolution 1 h) x)) := by
    simp_rw [hdH, hd]
    exact ((hsol.const_mul x).add htest).sub hcLim
  exact ⟨le_of_tendsto' hsol.abs (fun n => (ross_smooth_bounds (hH n).1
      (fun y => (hH n).2.1 y) x).1),
    le_of_tendsto' hdLim.abs (fun n => (ross_smooth_bounds (hH n).1
      (fun y => (hH n).2.1 y) x).2)⟩

/-- The integrating-factor solution obeys the Lipschitz Stein estimates at arbitrary scale. -/
lemma ross_formula_bounds {h : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hl : ∀ x y, |h x - h y| ≤ L * |x - y|) (x : ℝ) :
    |steinSolution 1 h x| ≤ L ∧ |deriv (steinSolution 1 h) x| ≤ √(2 / π) * L := by
  have hc : Continuous h := (LipschitzWith.of_dist_le_mul (K := ⟨L, hL⟩)
    (fun a b => by
      change |h a - h b| ≤ L * |a - b|
      exact hl a b)).continuous
  rcases hL.eq_or_lt with h0 | hpos
  · have he : h = fun _ => h 0 := by
      funext y
      have ht := hl y 0
      rw [← h0, zero_mul] at ht
      exact sub_eq_zero.mp (abs_nonpos_iff.mp ht)
    have hs : steinSolution 1 h = fun _ => 0 := by
      rw [he]
      funext y
      simp [steinSolution]
    rw [hs, ← h0]
    simp
  · have hn : ∀ a b, |L⁻¹ * h a - L⁻¹ * h b| ≤ |a - b| := by
      intro a b
      rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hpos)]
      calc L⁻¹ * |h a - h b| ≤ L⁻¹ * (L * |a - b|) :=
          mul_le_mul_of_nonneg_left (hl a b) (inv_nonneg.2 hL)
        _ = |a - b| := by field_simp
    have hb := ross_unit_formula_bounds hn x
    rw [stein_solution_const_mul] at hb
    have hdiff := (stein_hasDerivAt_formula zero_lt_one hc (ross_growth hl) x).differentiableAt
    rw [deriv_const_mul _ hdiff, abs_mul, abs_mul,
      abs_of_pos (inv_pos.2 hpos)] at hb
    have h1 := mul_le_mul_of_nonneg_left hb.1 hL
    have h2 := mul_le_mul_of_nonneg_left hb.2 hL
    have hcL : L * L⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
    rw [← mul_assoc, hcL, one_mul] at h1 h2
    exact ⟨by simpa using h1, by simpa [mul_comm] using h2⟩

end Internal

/-- Ross's Lemma 2.5, part 2, in the form controlling a bounded solution and its first derivative.
An absolutely continuous test with almost everywhere derivative bounded by `L` has standard
Stein bounds `2L` and `√(2/π)L`. No boundedness or continuous differentiability of the test is needed. -/
theorem ross_lemma_2_5_part_2 (h : ℝ → ℝ)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval h a b) (L : ℝ) (hL : 0 ≤ L)
    (hd : ∀ᵐ x, |deriv h x| ≤ L) (v : ℝ → ℝ) (hv : Differentiable ℝ v)
    (hvb : ∃ C, ∀ x, |v x| ≤ C)
    (he : ∀ x, deriv v x - x * v x = h x - ∫ z, h z ∂(gaussianReal 0 1)) :
    (∀ x, |v x| ≤ 2 * L) ∧ (∀ x, |deriv v x| ≤ √(2 / π) * L) := by
  have hl := Internal.ross_lipschitz_of_ac hAC hd
  have hc : Continuous h := (LipschitzWith.of_dist_le_mul (K := ⟨L, hL⟩)
    (fun a b => by
      change |h a - h b| ≤ L * |a - b|
      exact hl a b)).continuous
  have hf := Internal.stein_eq_formula zero_lt_one hc (Internal.ross_growth hl) hv hvb
    (fun x => by simpa using he x)
  rw [hf]
  exact ⟨fun x => (Internal.ross_formula_bounds hL hl x).1.trans (by linarith),
    fun x => (Internal.ross_formula_bounds hL hl x).2⟩

end Riesz1
