/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelErrorL1
public import Riesz1.Variance.RegMicroKernelCutoff
public import Riesz1.ToMathlib.TwoScalePowerEnvelope

/-!
# Uniform power envelopes for the actual regularization-error kernel

The error kernel and its derivative are bounded by `C h^(1-s) / d` and
`C h^(1-s) / d²`. These weaker, globally valid envelopes avoid any transition
gap when cutting the kernel at a radius comparable with the smoothing scale.
They serve equation (5.8) in the proof of Lemma 5.3.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- Global central-cell envelopes, with constants before the length and radius.
The kernel's singularity itself is excluded. Its `L¹` mass is handled separately. -/
theorem inverseKernel_regularization_power_envelopes (P : Parameters) (ρ : ℝ → ℝ)
    (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L h t : ℝ, 0 < L → 0 < h → h ≤ L / 4 →
      |t| < L / 2 → t ≠ 0 →
      |inverseKernel P L t - mollifyLine ρ h (inverseKernel P L) t| ≤
        C * h ^ (1 - P.val.2) * |t| ^ (-1 : ℝ) ∧
      |deriv (fun u => inverseKernel P L u - mollifyLine ρ h (inverseKernel P L) u) t| ≤
        C * h ^ (1 - P.val.2) * |t| ^ (-2 : ℝ) := by
  obtain ⟨A, hA, hnear⟩ := inverseKernel_mollify_near P ρ hρ
  obtain ⟨B, hB, hfar⟩ := inverseKernel_regularization_far P
  obtain ⟨D, hD, hsize⟩ := abs_inverseKernel_le_cell P
  obtain ⟨J, hJ, hgrad⟩ := inverseKernel_deriv_regularization_bounds P ρ hρ
  let K := A + B + D + J
  have hK : 0 < K := by dsimp [K]; positivity
  have hAK : A ≤ K := by dsimp [K]; linarith
  have hBK : B ≤ K := by dsimp [K]; linarith
  have hDK : D ≤ K := by dsimp [K]; linarith
  have hJK : J ≤ K := by dsimp [K]; linarith
  refine ⟨2 * K, by positivity, fun L h t hL hh hhL ht ht0 => ?_⟩
  have hd : 0 < |t| := abs_pos.mpr ht0
  have hdist : latticeDist L t = |t| := circDist_eq_abs hL ht.le
  have hval := TwoScalePowerEnvelope.of_piecewise (k := 0) P.property.2.1.le
    P.property.2.2 hh hd (by norm_num) hK.le
    (fun hth => (abs_sub _ _).trans ((add_le_add
      (hsize L t hL ht ht0) (hnear L t h hL hh hhL hth)).trans (by
        simp only [sub_zero]
        nlinarith [mul_le_mul_of_nonneg_right hDK (Real.rpow_nonneg hd.le (-P.val.2)),
          mul_le_mul_of_nonneg_right hAK (Real.rpow_nonneg hh.le (-P.val.2))])))
    (fun hht => by
      have hb := hfar ρ hρ L t h hL hh (by rw [hdist]; exact hht.le)
      rw [hdist] at hb
      simp only [sub_zero]
      exact hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hBK hh.le) (Real.rpow_nonneg hd.le _)))
  have hdiff := (inverseKernel_contDiffAt_of_abs_lt P hL ht0
    (ht.trans (by linarith))).differentiableAt (by simp)
  have hsm := (contDiff_mollifyLine_of_locallyIntegrable hρ hh
    (inverseKernel_locallyIntegrable P hL)).differentiable (by simp) t
  rw [deriv_fun_sub hdiff hsm]
  have hb := hgrad L t h hL hh hhL ht.le ht0
  have hdv := TwoScalePowerEnvelope.of_piecewise (k := 1) P.property.2.1.le
    P.property.2.2 hh hd (by norm_num) hK.le
    (fun hth => (hb.1 hth).trans (mul_le_mul_of_nonneg_right hJK (by positivity)))
    (fun hht => by
      have he : -P.val.2 - 1 - 1 = -P.val.2 - 2 := by ring
      rw [he]
      exact (hb.2 hht).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hJK hh.le) (Real.rpow_nonneg hd.le _)))
  constructor
  · simpa only [sub_zero] using hval
  · convert hdv using 1; norm_num

end Riesz1
