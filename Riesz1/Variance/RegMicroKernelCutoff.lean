/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelDifferentiable
public import Riesz1.ToMathlib.PowerKernelCutoff

/-!
# Uniform quantitative cutoffs of the inverse transport kernel

The near kernel has mass `O(a^(1-s))`, and the far kernel has derivative
`O(1_{|t|≥a/2}|t|^(-s-1))` on a centered period. All constants precede
the cutoff radius and circle length. These are the concrete kernel-side
estimates for the first derivative in the proof of Lemma 5.3.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- A nonzero displacement smaller than one period avoids the singular lattice. -/
theorem inverseKernel_contDiffAt_of_abs_lt (P : Parameters) {L t : ℝ}
    (hL : 0 < L) (ht : t ≠ 0) (htL : |t| < L) :
    ContDiffAt ℝ ∞ (inverseKernel P L) t := by
  apply contDiffAt_inverseKernel P hL
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    exact ht (by simpa only [Int.cast_zero, zero_mul] using hk)
  · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
    have hmul : |t| = |(k : ℝ)| * L := by rw [hk, abs_mul, abs_of_pos hL]
    nlinarith

/-- Quantitative near/far cutoffs of the actual inverse kernel, with one
constant independent of the radius, the length and the point. The far
derivative power is truncated away from zero, so its integral is meaningful. -/
theorem inverseKernel_quantitative_cutoff (P : Parameters) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → ∃ χ : ℝ → ℝ,
      ContDiff ℝ ∞ χ ∧ (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) ∧
      (∀ t, χ (-t) = χ t) ∧
      (∀ t, |t| ≤ a / 2 → χ t = 0) ∧ (∀ t, a ≤ |t| → χ t = 1) ∧
      (∀ t, |deriv χ t| ≤ C / a) ∧
      (∀ t, |t| < a / 2 ∨ a < |t| → deriv χ t = 0) ∧
      ∀ L : ℝ, 0 < L → a < L / 2 →
        Function.support (fun t => inverseKernel P L t * (1 - χ t)) ⊆ Ioc (-a) a ∧
        IntegrableOn (fun t => inverseKernel P L t * (1 - χ t)) (Icc (-a) a) ∧
        (∫ t in Icc (-a) a, |inverseKernel P L t * (1 - χ t)|) ≤ C * a ^ (1 - P.val.2) ∧
        ContDiffOn ℝ 1 (fun t => inverseKernel P L t * χ t) (Ioo (-L) L) ∧
        ∀ t : ℝ, |t| < L / 2 →
          |deriv (fun u => inverseKernel P L u * χ u) t| ≤
            C * (Ici (a / 2)).indicator (fun d : ℝ => d ^ (-P.val.2 - 1)) |t| := by
  obtain ⟨D₀, hD₀, hsize⟩ := abs_inverseKernel_le_cell P
  obtain ⟨D₁, hD₁, hgrad⟩ := inverseKernel_iteratedDeriv_bound P 1
  obtain ⟨B, hB, hcut⟩ := exists_even_scaled_cutoff
  let D := D₀ + D₁
  let C := B + D * (1 + B) + 2 * D / (1 - P.val.2) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hτ : 0 < 1 - P.val.2 := sub_pos.mpr P.property.2.2
  have hproduct : 0 ≤ D * (1 + B) := by positivity
  have hquot : 0 ≤ 2 * D / (1 - P.val.2) := by positivity
  have hDC : D * (1 + B) ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hNC : 2 * D / (1 - P.val.2) ≤ C := by dsimp [C]; linarith
  refine ⟨C, by dsimp [C]; positivity, fun a ha => ?_⟩
  obtain ⟨χ, hχ, hχb, heven, hzero, hone, hderiv, hout⟩ := hcut a ha
  refine ⟨χ, hχ, hχb, heven, hzero, hone,
    fun t => (hderiv t).trans (div_le_div_of_nonneg_right hBC ha.le), hout, fun L hL haL => ?_⟩
  have hKs (t : ℝ) (ht : t ≠ 0) (htL : |t| < L) :
      ContDiffAt ℝ 1 (inverseKernel P L) t :=
    (inverseKernel_contDiffAt_of_abs_lt P hL ht htL).of_le (by simp)
  have hkb (t : ℝ) (ht : t ≠ 0) (htL : |t| < L / 2) :
      |inverseKernel P L t| ≤ D * |t| ^ (-P.val.2) :=
    (hsize L t hL htL ht).trans
      (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith)
        (Real.rpow_nonneg (abs_nonneg t) _))
  have hkdb (t : ℝ) (ht : t ≠ 0) (htL : |t| < L / 2) :
      |deriv (inverseKernel P L) t| ≤ D * |t| ^ (-P.val.2 - 1) := by
    have htlat : ∀ k : ℤ, t ≠ k * L := by
      intro k hk
      have hz : latticeDist L t ≤ 0 := by
        simpa only [hk, sub_self, abs_zero] using latticeDist_le_abs_sub L t hL k
      rw [latticeDist_eq_abs_of_abs_lt hL htL] at hz
      exact ht (abs_nonpos_iff.mp hz)
    have hb := hgrad L t hL htlat
    rw [iteratedDeriv_one, Nat.cast_one, latticeDist_eq_abs_of_abs_lt hL htL] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith)
      (Real.rpow_nonneg (abs_nonneg t) _))
  have hsupp : Function.support (fun t => inverseKernel P L t * (1 - χ t)) ⊆ Ioc (-a) a := by
    intro t ht
    have ht' : |t| < a := by
      by_contra hn
      exact ht (by dsimp only; rw [hone t (le_of_not_gt hn), sub_self, mul_zero])
    exact ⟨(abs_lt.mp ht').1, (abs_lt.mp ht').2.le⟩
  have hnear := PowerKernelCutoff.integral_abs_near_le ha hD.le P.property.2.2
    ((inverseKernel_locallyIntegrable P hL).integrableOn_isCompact isCompact_Icc)
    hχ.continuous hχb (show ∀ᵐ t : ℝ ∂(volume.restrict (Icc (-a) a)),
      |inverseKernel P L t| ≤ D * |t| ^ (-P.val.2) from by
        filter_upwards [ae_restrict_mem measurableSet_Icc,
          ae_restrict_of_ae (show ∀ᵐ t : ℝ, t ≠ 0 by rw [ae_iff]; simp)] with t ht ht0
        exact hkb t ht0 ((abs_le.mpr ht).trans_lt haL))
  refine ⟨hsupp, hnear.1, hnear.2.trans ?_, ?_, fun t ht => ?_⟩
  · calc D * (2 * a ^ (1 - P.val.2) / (1 - P.val.2)) =
          (2 * D / (1 - P.val.2)) * a ^ (1 - P.val.2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hNC (Real.rpow_nonneg ha.le _)
  · intro t ht
    exact (PowerKernelCutoff.contDiffAt_far ha hχ hzero hKs
      (abs_lt.mpr ht)).contDiffWithinAt
  · have hh := PowerKernelCutoff.abs_deriv_far_le (e := -P.val.2) ha hD.le hB.le
      hχ hχb hzero hderiv (fun u hu => hout u (Or.inr hu))
      (fun u hu huL => hKs u hu (huL.trans (by linarith))) hkb hkdb ht
    exact hh.trans (mul_le_mul_of_nonneg_right hDC
      (indicator_nonneg (fun d _ => Real.rpow_nonneg (abs_nonneg t) _) _))

end Riesz1
