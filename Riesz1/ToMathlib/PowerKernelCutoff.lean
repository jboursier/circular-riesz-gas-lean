/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EvenScaledCutoff
public import Riesz1.ToMathlib.MollifierPointwise.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Quantitative near/far cutoffs of power kernels

A smooth cutoff suppresses the singularity without losing the far derivative
power. The near part has the explicit integrable power mass. These facts
apply to the inverse kernel and the integrable error kernel in the proof of
Lemma 5.3.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1.PowerKernelCutoff

/-- Multiplication by a smooth function that vanishes in a neighborhood of
zero removes the kernel's singularity there. -/
theorem contDiffAt_far {K χ : ℝ → ℝ} {a T : ℝ} (ha : 0 < a)
    (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ t, |t| ≤ a / 2 → χ t = 0)
    (hK : ∀ t, t ≠ 0 → |t| < T → ContDiffAt ℝ 1 K t)
    {t : ℝ} (ht : |t| < T) : ContDiffAt ℝ 1 (fun u => K u * χ u) t := by
  by_cases ht0 : t = 0
  · subst ht0
    have he : (fun u => K u * χ u) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [Ioo_mem_nhds (by linarith : -a / 2 < (0 : ℝ))
        (by linarith : (0 : ℝ) < a / 2)] with u hu
      rw [hzero u (abs_le.mpr ⟨by linarith [hu.1], hu.2.le⟩), mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (hK t ht0 ht).mul ((hχ.of_le (by simp)).contDiffAt)

/-- If `K` has powers `d^e` and `d^(e-1)` in size and derivative, the far
cutoff has derivative bounded by `D(1+B)d^(e-1)` outside `a/2`, and zero
inside. The factor is independent of the cutoff radius. -/
theorem abs_deriv_far_le {K χ : ℝ → ℝ} {a T D B e t : ℝ}
    (ha : 0 < a) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hχ : ContDiff ℝ ∞ χ) (hχbound : ∀ u, 0 ≤ χ u ∧ χ u ≤ 1)
    (hzero : ∀ u, |u| ≤ a / 2 → χ u = 0)
    (hderiv : ∀ u, |deriv χ u| ≤ B / a)
    (hout : ∀ u, a < |u| → deriv χ u = 0)
    (hK : ∀ u, u ≠ 0 → |u| < T → ContDiffAt ℝ 1 K u)
    (hsize : ∀ u, u ≠ 0 → |u| < T → |K u| ≤ D * |u| ^ e)
    (hgrad : ∀ u, u ≠ 0 → |u| < T → |deriv K u| ≤ D * |u| ^ (e - 1))
    (ht : |t| < T) :
    |deriv (fun u => K u * χ u) t| ≤
      D * (1 + B) * (Ici (a / 2)).indicator (fun d : ℝ => d ^ (e - 1)) |t| := by
  by_cases hnear : |t| < a / 2
  · have he : (fun u => K u * χ u) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [(continuous_abs.tendsto t).eventually
        (eventually_lt_nhds hnear)] with u hu
      rw [hzero u hu.le, mul_zero]
    rw [he.deriv_eq, deriv_const, abs_zero,
      indicator_of_notMem (show |t| ∉ Ici (a / 2) from not_le.mpr hnear), mul_zero]
  · have ht0 : t ≠ 0 := by
      intro ht0
      rw [ht0, abs_zero] at hnear
      exact hnear (by positivity)
    have htpos : 0 < |t| := abs_pos.mpr ht0
    have hdK := (hK t ht0 ht).differentiableAt (by norm_num)
    have hdχ := hχ.differentiable (by simp) t
    rw [indicator_of_mem (show |t| ∈ Ici (a / 2) from le_of_not_gt hnear),
      deriv_fun_mul hdK hdχ]
    have hone : |deriv K t| * |χ t| ≤ D * |t| ^ (e - 1) := by
      rw [abs_of_nonneg (hχbound t).1]
      exact (mul_le_mul_of_nonneg_right (hgrad t ht0 ht) (hχbound t).1).trans
        (mul_le_of_le_one_right (mul_nonneg hD (Real.rpow_nonneg htpos.le _)) (hχbound t).2)
    have htwo : |K t| * |deriv χ t| ≤ D * B * |t| ^ (e - 1) := by
      by_cases hta : |t| ≤ a
      · have hpow : |t| ^ e / a ≤ |t| ^ (e - 1) := by
          have he : |t| ^ e = |t| ^ (e - 1) * |t| := by
            calc _ = |t| ^ (e - 1 + 1) := by congr 1; ring
              _ = _ := by rw [Real.rpow_add htpos, Real.rpow_one]
          rw [he]
          exact (div_le_iff₀ ha).mpr
            (by nlinarith [Real.rpow_nonneg htpos.le (e - 1)])
        calc _ ≤ (D * |t| ^ e) * (B / a) :=
              mul_le_mul (hsize t ht0 ht) (hderiv t) (abs_nonneg _) (by positivity)
          _ = D * B * (|t| ^ e / a) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow (mul_nonneg hD hB)
      · rw [hout t (lt_of_not_ge hta), abs_zero, mul_zero]
        positivity
    exact (abs_add_le _ _).trans (by simpa only [abs_mul] using
      (add_le_add hone htwo).trans_eq (by ring))

/-- The near kernel's absolute mass is bounded by the explicit integrable
power mass. Only a size estimate almost everywhere is needed. -/
theorem integral_abs_near_le {K χ : ℝ → ℝ} {a D s : ℝ}
    (ha : 0 < a) (hD : 0 ≤ D) (hs : s < 1)
    (hK : IntegrableOn K (Icc (-a) a))
    (hχ : Continuous χ) (hχbound : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (hsize : ∀ᵐ t : ℝ ∂(volume.restrict (Icc (-a) a)), |K t| ≤ D * |t| ^ (-s)) :
    IntegrableOn (fun t => K t * (1 - χ t)) (Icc (-a) a) ∧
    (∫ t in Icc (-a) a, |K t * (1 - χ t)|) ≤ D * (2 * a ^ (1 - s) / (1 - s)) := by
  have hi : IntegrableOn (fun t => K t * (1 - χ t)) (Icc (-a) a) :=
    hK.mul_continuousOn ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).sub hχ).continuousOn
      isCompact_Icc
  refine ⟨hi, ?_⟩
  calc _ ≤ ∫ t in Icc (-a) a, D * |t| ^ (-s) := by
        apply integral_mono_ae hi.abs ((integrableOn_abs_rpow (by linarith) ha.le).const_mul D)
        filter_upwards [hsize] with t ht
        rw [abs_mul, abs_of_nonneg (by linarith [(hχbound t).2] : 0 ≤ 1 - χ t)]
        exact (mul_le_mul_of_nonneg_right ht (by linarith [(hχbound t).2])).trans
          (mul_le_of_le_one_right (mul_nonneg hD (Real.rpow_nonneg (abs_nonneg t) _))
            (by linarith [(hχbound t).1]))
    _ = _ := by rw [integral_const_mul, integral_abs_rpow_symm hs ha.le]

end Riesz1.PowerKernelCutoff
