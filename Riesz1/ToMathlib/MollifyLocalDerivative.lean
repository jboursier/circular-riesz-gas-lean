/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.Line

/-!
# Transferring derivatives on a nonsingular convolution window

Local smoothness suffices to transfer a derivative to the input. The input
can be singular elsewhere, as in the transport tails of Lemma 5.1.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1

/-- A bound on a window containing the kernel support bounds the convolution. -/
theorem mollifyLine_abs_le_of_local {ρ f : ℝ → ℝ} (hρ : IsMollifier ρ)
    {h x B : ℝ} (hh : 0 < h) (_hB : 0 ≤ B)
    (hm : AEStronglyMeasurable f volume)
    (hf : ∀ y : ℝ, |y - x| < h → |f y| ≤ B) :
    Integrable (fun u => f (x - u) * scaledMollifier ρ h u) ∧
      |mollifyLine ρ h f x| ≤ B := by
  have hκi : Integrable (scaledMollifier ρ h) :=
    (contDiff_scaledMollifier hρ).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_scaledMollifier hρ hh)
  have hbound : ∀ u : ℝ, ‖f (x - u) * scaledMollifier ρ h u‖ ≤ B * scaledMollifier ρ h u := by
    intro u
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (scaledMollifier_nonneg hρ hh u)]
    by_cases hu : scaledMollifier ρ h u = 0
    · simp only [hu, mul_zero, le_refl]
    · have hu' : |u| < h / 2 := lt_of_not_ge (fun hh' => hu (scaledMollifier_eq_zero hρ hh hh'))
      apply mul_le_mul_of_nonneg_right _ (scaledMollifier_nonneg hρ hh u)
      apply hf
      rw [show x - u - x = -u by ring, abs_neg]
      linarith
  have hi : Integrable (fun u => f (x - u) * scaledMollifier ρ h u) := by
    apply (hκi.const_mul B).mono'
      ((hm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left_of_right_invariant volume x)).mul
        (contDiff_scaledMollifier hρ).continuous.aestronglyMeasurable)
    exact ae_of_all _ hbound
  refine ⟨hi, ?_⟩
  rw [mollifyLine_eq, ← Real.norm_eq_abs]
  calc _ ≤ ∫ u, B * scaledMollifier ρ h u :=
        norm_integral_le_of_norm_le (hκi.const_mul B) (ae_of_all _ hbound)
    _ = B := by rw [integral_const_mul, integral_scaledMollifier hρ hh, mul_one]

/-- Differentiation can be transferred on one window, with a local bound.
No differentiability is required at any point outside that window. -/
theorem hasDerivAt_mollifyLine_of_local {ρ f : ℝ → ℝ} (hρ : IsMollifier ρ)
    {h x B : ℝ} (hh : 0 < h) (hf : LocallyIntegrable f volume)
    (hd : ∀ y : ℝ, |y - x| < h → DifferentiableAt ℝ f y)
    (hb : ∀ y : ℝ, |y - x| < h → |deriv f y| ≤ B) :
    HasDerivAt (mollifyLine ρ h f)
      (∫ u, deriv f (x - u) * scaledMollifier ρ h u) x := by
  have hκc : Continuous (scaledMollifier ρ h) := (contDiff_scaledMollifier hρ).continuous
  have hκi : Integrable (scaledMollifier ρ h) := hκc.integrable_of_hasCompactSupport
    (hasCompactSupport_scaledMollifier hρ hh)
  have hint : Integrable (fun u => f (x - u) * scaledMollifier ρ h u) := by
    simpa only [sub_sub_cancel] using (integrable_mul_scaled_sub hρ hh hf x).comp_sub_left x
  have hmeas (x' : ℝ) : AEStronglyMeasurable
      (fun u => f (x' - u) * scaledMollifier ρ h u) volume :=
    (hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant volume x')).mul hκc.aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable
      (fun u => deriv f (x - u) * scaledMollifier ρ h u) volume :=
    (((measurable_deriv f).comp (measurable_const.sub measurable_id)).mul hκc.measurable).aestronglyMeasurable
  have hwindow (u y : ℝ) (hu : scaledMollifier ρ h u ≠ 0) (hy : y ∈ Metric.ball x (h / 4)) :
      |y - u - x| < h := by
    have hu' : |u| < h / 2 := lt_of_not_ge (fun hh' => hu (scaledMollifier_eq_zero hρ hh hh'))
    have hy' : |y - x| < h / 4 := by simpa only [Metric.mem_ball, Real.dist_eq] using hy
    have ht := abs_sub (y - x) u
    rw [show y - x - u = y - u - x by ring] at ht
    linarith
  have hD := _root_.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y u => f (y - u) * scaledMollifier ρ h u)
    (F' := fun y u => deriv f (y - u) * scaledMollifier ρ h u)
    (x₀ := x) (s := Metric.ball x (h / 4))
    (bound := fun u => B * scaledMollifier ρ h u)
    (Metric.ball_mem_nhds x (by linarith)) (Eventually.of_forall hmeas) hint hdmeas ?_
    (hκi.const_mul B) ?_
  · have he : mollifyLine ρ h f = fun y => ∫ u, f (y - u) * scaledMollifier ρ h u :=
      funext (mollifyLine_eq f)
    rw [he]
    exact hD.2
  · exact ae_of_all _ fun u y hy => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (scaledMollifier_nonneg hρ hh u)]
      by_cases hu : scaledMollifier ρ h u = 0
      · simp only [hu, mul_zero, le_refl]
      · exact mul_le_mul_of_nonneg_right (hb _ (hwindow u y hu hy)) (scaledMollifier_nonneg hρ hh u)
  · exact ae_of_all _ fun u y hy => by
      by_cases hu : scaledMollifier ρ h u = 0
      · simp only [hu, mul_zero]
        exact hasDerivAt_const _ _
      · exact (((hd _ (hwindow u y hu hy)).hasDerivAt).comp_sub_const y u).mul_const _

/-- The local classical derivative bound is preserved on a smaller convolution window. -/
theorem abs_deriv_mollifyLine_le_of_local {ρ f : ℝ → ℝ} (hρ : IsMollifier ρ)
    {h x B : ℝ} (hh : 0 < h) (hB : 0 ≤ B) (hf : LocallyIntegrable f volume)
    (hd : ∀ y : ℝ, |y - x| < h → DifferentiableAt ℝ f y)
    (hb : ∀ y : ℝ, |y - x| < h → |deriv f y| ≤ B) :
    |deriv (mollifyLine ρ h f) x| ≤ B := by
  rw [(hasDerivAt_mollifyLine_of_local hρ hh hf hd hb).deriv]
  rw [← mollifyLine_eq]
  exact (mollifyLine_abs_le_of_local hρ hh hB (measurable_deriv f).aestronglyMeasurable hb).2

end Riesz1
