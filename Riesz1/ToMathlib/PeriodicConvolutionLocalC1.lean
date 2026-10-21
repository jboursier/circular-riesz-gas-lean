/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PeriodicConvolutionRegularity
public import Riesz1.ToMathlib.ContDiffIntegralLocalOne

/-!
# Continuous derivatives of locally regular periodic convolutions

The near kernel is integrable. Its derivative falls on the locally `C¹`
input. The far kernel is `C¹`. Its derivative falls on the kernel. Both
resulting integrals are continuous by domination. This strengthens the
differentiability criterion to `C¹` regularity.
-/

public section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

namespace Riesz1.PeriodicConvolution

/-- A periodic convolution is locally `C¹` wherever the input is locally
`C¹` and the kernel is `C¹` away from its singular lattice. -/
theorem contDiffAt_of_contDiffOn {q K : ℝ → ℝ} {L c r : ℝ}
    (hL : 0 < L) (hr : 0 < r)
    (hqp : Function.Periodic q L) (hKp : Function.Periodic K L)
    (hqm : Measurable q) (hKm : Measurable K)
    (hqi : LocallyIntegrable q volume) (hKi : LocallyIntegrable K volume)
    (hq : ContDiffOn ℝ 1 q (Ioo (c - r) (c + r)))
    (hK : ∀ t : ℝ, t ≠ 0 → |t| < L → ContDiffAt ℝ 1 K t) :
    ContDiffAt ℝ 1
        (fun x => ∫ y in Ioc (-(L / 2)) (L / 2), q y * K (x - y)) c := by
  let a := min (r / 4) (L / 16)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have har : a ≤ r / 4 := min_le_left _ _
  have haL : a ≤ L / 16 := min_le_right _ _
  let χ : ℝ → ℝ := fun t => evenUnitCutoff (t / a)
  let N : ℝ → ℝ := fun t => K t * (1 - χ t)
  let F : ℝ → ℝ := fun t => K t * χ t
  have hχ : ContDiff ℝ ∞ χ := evenUnitCutoff_contDiff.comp (contDiff_id.div_const a)
  have hχzero (t : ℝ) (ht : |t| ≤ a / 2) : χ t = 0 := by
    apply evenUnitCutoff_eq_zero
    rw [abs_div, abs_of_pos ha, div_le_iff₀ ha]
    linarith
  have hχone (t : ℝ) (ht : a ≤ |t|) : χ t = 1 := by
    apply evenUnitCutoff_eq_one
    rw [abs_div, abs_of_pos ha, le_div_iff₀ ha]
    simpa using ht
  have hNs : Function.support N ⊆ Ioc (-a) a := by
    intro t ht
    have habs : |t| < a := by
      by_contra h
      have h1 := hχone t (le_of_not_gt h)
      exact ht (by dsimp [N]; rw [h1, sub_self, mul_zero])
    exact ⟨(abs_lt.mp habs).1, (abs_lt.mp habs).2.le⟩
  have hNi : IntegrableOn N (Ioc (-a) a) := by
    exact ((hKi.integrableOn_isCompact isCompact_Icc).mul_continuousOn
      (continuous_const.sub hχ.continuous).continuousOn isCompact_Icc).mono_set
        Ioc_subset_Icc_self
  have hFs (t : ℝ) (ht : t ∈ Ioo (-L) L) : ContDiffAt ℝ 1 F t := by
    by_cases ht0 : t = 0
    · subst ht0
      have hev : F =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) := by
        filter_upwards [Ioo_mem_nhds (by linarith : -a / 2 < (0 : ℝ))
          (by linarith : (0 : ℝ) < a / 2)] with u hu
        dsimp [F]
        rw [hχzero u (abs_le.mpr ⟨by linarith [hu.1], hu.2.le⟩), mul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · exact (hK t ht0 (abs_lt.mpr ht)).mul ((hχ.of_le (by simp)).contDiffAt)
  have hFc : ContinuousOn F (Icc (-(3 * L / 4)) (3 * L / 4)) := by
    intro t ht
    exact (hFs t ⟨by linarith [ht.1], by linarith [ht.2]⟩).continuousAt.continuousWithinAt
  have hFd : ContinuousOn (deriv F) (Icc (-(3 * L / 4)) (3 * L / 4)) := by
    intro t ht
    exact ((hFs t ⟨by linarith [ht.1], by linarith [ht.2]⟩).derivWithin
      (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hFc
  obtain ⟨B₁, hB₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hFd
  have hQ : Icc (c - 2 * a) (c + 2 * a) ⊆ Ioo (c - r) (c + r) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hq.continuousOn.mono hQ)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hq.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hQ)
  have hnear (x : ℝ) (hx : x ∈ ball c a) (t : ℝ) (ht : t ∈ Ioc (-a) a) :
      x - t ∈ Icc (c - 2 * a) (c + 2 * a) := by
    have hx' : |x - c| < a := by simpa only [mem_ball, Real.dist_eq] using hx
    obtain ⟨hx0, hx1⟩ := abs_lt.mp hx'
    constructor <;> linarith [ht.1, ht.2]
  have hfar (x : ℝ) (hx : x ∈ ball c a) (y : ℝ)
      (hy : y ∈ Ioc (c - L / 2) (c + L / 2)) :
      x - y ∈ Icc (-(3 * L / 4)) (3 * L / 4) := by
    have hx' : |x - c| < a := by simpa only [mem_ball, Real.dist_eq] using hx
    obtain ⟨hx0, hx1⟩ := abs_lt.mp hx'
    constructor <;> linarith [hy.1, hy.2]
  have hqi' : IntegrableOn q (Ioc (c-L/2) (c+L/2)) :=
    (hqi.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hnI (x : ℝ) (hx : x ∈ ball c a) :
      IntegrableOn (fun t => q (x-t)*N t) (Ioc (-a) a) := by
    refine (hNi.norm.const_mul A).mono'
      (((hqm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable).mul
        hNi.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [Real.norm_eq_abs] using hA _ (hnear x hx t ht)) (norm_nonneg _)
  have hfI (x : ℝ) (hx : x ∈ ball c a) :
      IntegrableOn (fun y => q y*F (x-y)) (Ioc (c-L/2) (c+L/2)) := by
    refine (hqi'.norm.const_mul B₀).mono'
      (hqi'.aestronglyMeasurable.mul
        ((hKm.mul hχ.continuous.measurable).comp
          (measurable_const.sub measurable_id)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [norm_mul, Real.norm_eq_abs (F (x-y))]
    have hb : |F (x-y)| ≤ B₀ := by
      simpa only [Real.norm_eq_abs] using hB₀ _ (hfar x hx y hy)
    nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (q y))]
  have hqC (x : ℝ) (hx : x ∈ ball c a) (t : ℝ) (ht : t ∈ Ioc (-a) a) :
      ContDiffAt ℝ 1 q (x-t) :=
    (hq _ (hQ (hnear x hx t ht))).contDiffAt
      (isOpen_Ioo.mem_nhds (hQ (hnear x hx t ht)))
  have hFC (x : ℝ) (hx : x ∈ ball c a) (y : ℝ) (hy : y ∈ Ioc (c-L/2) (c+L/2)) :
      ContDiffAt ℝ 1 F (x-y) :=
    hFs _ ⟨by linarith [(hfar x hx y hy).1], by linarith [(hfar x hx y hy).2]⟩
  have hnC : ContDiffOn ℝ 1 (fun x => ∫ t in Ioc (-a) a, q (x-t)*N t) (ball c a) := by
    apply contDiffOn_integral_one_of_dominated (F' := fun x t => deriv q (x-t)*N t)
      (b := fun t => M*‖N t‖) isOpen_ball hnI
    · intro x _
      exact (((measurable_deriv q).comp (measurable_const.sub measurable_id)).aestronglyMeasurable).mul
        hNi.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      intro x hx
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [Real.norm_eq_abs] using hM _ (hnear x hx t ht)) (norm_nonneg _)
    · exact hNi.norm.const_mul M
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      intro x hx
      exact ((hqC x hx t ht).differentiableAt (by norm_num)).hasDerivAt.comp_sub_const x t |>.mul_const (N t)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      intro x hx
      have hcont : ContinuousAt (fun z : ℝ => deriv q (z-t)) x :=
        ((hqC x hx t ht).derivWithin (m := 0) (by norm_num)).continuousAt.comp
          (f := fun z : ℝ => z-t) (x := x)
          (by fun_prop : ContinuousAt (fun z : ℝ => z-t) x)
      exact (hcont.mul continuousAt_const).continuousWithinAt
  have hfC : ContDiffOn ℝ 1 (fun x => ∫ y in Ioc (c-L/2) (c+L/2), q y*F (x-y))
      (ball c a) := by
    apply contDiffOn_integral_one_of_dominated (F' := fun x y => q y*deriv F (x-y))
      (b := fun y => B₁*‖q y‖) isOpen_ball hfI
    · intro x _
      exact hqi'.aestronglyMeasurable.mul
        (((measurable_deriv F).comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      intro x hx
      rw [norm_mul, Real.norm_eq_abs (deriv F (x-y))]
      have hb : |deriv F (x-y)| ≤ B₁ := by
        simpa only [Real.norm_eq_abs] using hB₁ _ (hfar x hx y hy)
      nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (q y))]
    · exact hqi'.norm.const_mul B₁
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      intro x hx
      exact (((hFC x hx y hy).differentiableAt (by norm_num)).hasDerivAt.comp_sub_const x y).const_mul (q y)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      intro x hx
      have hcont : ContinuousAt (fun z : ℝ => deriv F (z-y)) x :=
        ((hFC x hx y hy).derivWithin (m := 0) (by norm_num)).continuousAt.comp
          (f := fun z : ℝ => z-y) (x := x)
          (by fun_prop : ContinuousAt (fun z : ℝ => z-y) x)
      exact (continuousAt_const.mul hcont).continuousWithinAt
  have heq : (fun x => ∫ y in Ioc (-(L/2)) (L/2), q y*K (x-y)) =ᶠ[𝓝 c]
      (fun x => (∫ t in Ioc (-a) a, q (x-t)*N t) +
        ∫ y in Ioc (c-L/2) (c+L/2), q y*F (x-y)) := by
    filter_upwards [ball_mem_nhds c ha] with x hx
    have hlocal : IntegrableOn (fun y => q y*N (x-y)) (Ioc (c-L/2) (c+L/2)) := by
      have hs : Function.support (fun t => q (x-t)*N t) ⊆ Ioc (-a) a := by
        intro t ht
        exact hNs (Function.mem_support.mpr (mul_ne_zero_iff.mp ht).2)
      have hg : Integrable (fun t => q (x-t)*N t) volume :=
        (integrableOn_iff_integrable_of_support_subset hs).mp (hnI x hx)
      simpa only [sub_sub_cancel] using (hg.comp_sub_left x).integrableOn
    rw [integral_window_eq hL hqp hKp c x]
    have hsplit : ∀ t, K t = N t+F t := fun t => by dsimp [N, F]; ring
    simp_rw [hsplit, mul_add]
    rw [integral_add hlocal (hfI x hx), integral_near_eq hL ha.le ?_ hNs]
    have hx' : |x-c| < a := by simpa only [mem_ball, Real.dist_eq] using hx
    linarith
  exact ((hnC.add hfC c (mem_ball_self ha)).contDiffAt (ball_mem_nhds c ha)).congr_of_eventuallyEq heq

end Riesz1.PeriodicConvolution
