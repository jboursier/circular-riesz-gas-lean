/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PeriodicConvolutionSplit
public import Riesz1.ToMathlib.EvenScaledCutoff
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Differentiability of periodic convolutions away from input singularities

A locally integrable periodic kernel that is `C¹` off its singular lattice can
be convolved pointwise with an integrable periodic input wherever the input is
locally `C¹`. The near/far split supplies both absolute integrability and a
classical derivative. No principal value of the kernel derivative is required.
-/

public section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

namespace Riesz1
namespace PeriodicConvolution

/-- Local `C¹` regularity of the input suffices for pointwise absolute
integrability and differentiability of a periodic singular convolution. -/
theorem differentiableAt_of_contDiffOn {q K : ℝ → ℝ} {L c r : ℝ}
    (hL : 0 < L) (hr : 0 < r)
    (hqp : Function.Periodic q L) (hKp : Function.Periodic K L)
    (hqm : Measurable q) (hKm : Measurable K)
    (hqi : LocallyIntegrable q volume) (hKi : LocallyIntegrable K volume)
    (hq : ContDiffOn ℝ 1 q (Ioo (c - r) (c + r)))
    (hK : ∀ t : ℝ, t ≠ 0 → |t| < L → ContDiffAt ℝ 1 K t) :
    IntegrableOn (fun y => q y * K (c - y)) (Ioc (-(L / 2)) (L / 2)) ∧
      DifferentiableAt ℝ
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
  obtain ⟨hi, hd⟩ := hasDerivAt_split (q := q) (K := K) (N := N) (F := F)
    (a := a) (c := c) (ε := a) (A := A) (B := max B₀ B₁) (M := M)
    hL ha.le ha (by linarith) hqp hKp hqm
    ((hqi.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self)
    hNi hNs (hKm.mul hχ.continuous.measurable)
    (fun t => by dsimp [N, F]; ring)
    (fun x hx t ht => by simpa only [Real.norm_eq_abs] using hA _ (hnear x hx t ht))
    (fun x hx t ht => ⟨
      (hq _ (hQ (hnear x hx t ht))).contDiffAt
        (isOpen_Ioo.mem_nhds (hQ (hnear x hx t ht))) |>.differentiableAt (by norm_num),
      by simpa only [Real.norm_eq_abs] using hM _ (hnear x hx t ht)⟩)
    (fun x hx y hy => by
      have hb : |F (x - y)| ≤ B₀ := by
        simpa only [Real.norm_eq_abs] using hB₀ _ (hfar x hx y hy)
      exact hb.trans (le_max_left _ _))
    (fun x hx y hy => ⟨
      (hFs _ ⟨by linarith [(hfar x hx y hy).1],
        by linarith [(hfar x hx y hy).2]⟩).differentiableAt (by norm_num),
      by
        have hb : |deriv F (x - y)| ≤ B₁ := by
          simpa only [Real.norm_eq_abs] using hB₁ _ (hfar x hx y hy)
        exact hb.trans (le_max_right _ _)⟩)
  exact ⟨hi, hd.differentiableAt⟩

end PeriodicConvolution
end Riesz1
