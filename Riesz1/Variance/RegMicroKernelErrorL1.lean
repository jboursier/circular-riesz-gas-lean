/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelShift
public import Riesz1.ToMathlib.CircleMollifyError
public import Riesz1.ToMathlib.MollifierPointwise.Smoothing

/-!
# The integrable regularization-error kernel

The kernel `P_L - P_L * ρ_h` has `L¹` norm `O(h^(1-s))`, uniformly in
`L` when `h ≤ L/4`. Unlike its derivative, this error kernel is integrable.
Its near convolution can therefore be differentiated by transferring the
derivative to the transport density. This is an alternative to the
principal-value cancellation step in the proof of Lemma 5.3.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- A first-order increment bound for the inverse kernel away from its lattice. -/
theorem inverseKernel_shift_bound (P : Parameters) :
    ∃ C : ℝ, 0 < C ∧ ∀ L t u : ℝ, 0 < L →
      (∀ k : ℤ, t ≠ k * L) → |u| ≤ latticeDist L t / 2 →
      |inverseKernel P L (t - u) - inverseKernel P L t| ≤
        C * |u| * latticeDist L t ^ (-P.val.2 - 1) := by
  obtain ⟨D, hD, hbound⟩ := inverseKernel_iteratedDeriv_bound P 1
  let e := -P.val.2 - 1
  have he : e ≤ 0 := by dsimp [e]; linarith [P.property.2.1]
  refine ⟨D * (1 / 2 : ℝ) ^ e, by positivity, ?_⟩
  intro L t u hL ht hu
  have hd : 0 < latticeDist L t := latticeDist_pos ht
  have hdist (z : ℝ) (hz : z ∈ uIcc t (t - u)) :
      latticeDist L t / 2 ≤ latticeDist L z := by
    have hzt : |z - t| ≤ |u| := by
      simpa only [sub_sub_cancel_left, abs_neg] using abs_sub_left_of_mem_uIcc hz
    have h := circDist_le_add_abs hL t z
    change latticeDist L t ≤ latticeDist L z + |t - z| at h
    rw [abs_sub_comm t z] at h
    linarith
  have hne (z : ℝ) (hz : z ∈ uIcc t (t - u)) : ∀ k : ℤ, z ≠ k * L := by
    intro k hk
    have hzero : latticeDist L z ≤ 0 := by
      simpa only [hk, sub_self, abs_zero] using latticeDist_le_abs_sub L z hL k
    linarith [hdist z hz]
  have hdiff (z : ℝ) (hz : z ∈ uIcc t (t - u)) :
      DifferentiableAt ℝ (inverseKernel P L) z :=
    (contDiffAt_inverseKernel P hL (hne z hz)).differentiableAt (by simp)
  have hderiv (z : ℝ) (hz : z ∈ uIcc t (t - u)) :
      ‖deriv (inverseKernel P L) z‖ ≤
        D * (1 / 2 : ℝ) ^ e * latticeDist L t ^ e := by
    have h := hbound L z hL (hne z hz)
    simp only [iteratedDeriv_one, Nat.cast_one, Real.norm_eq_abs] at h ⊢
    have hp : latticeDist L z ^ e ≤ (latticeDist L t / 2) ^ e :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (hdist z hz) he
    calc |deriv (inverseKernel P L) z|
        ≤ D * latticeDist L z ^ e := h
      _ ≤ D * (latticeDist L t / 2) ^ e := mul_le_mul_of_nonneg_left hp hD.le
      _ = D * (1 / 2 : ℝ) ^ e * latticeDist L t ^ e := by
        rw [show latticeDist L t / 2 = (1 / 2 : ℝ) * latticeDist L t by ring,
          Real.mul_rpow (by positivity) hd.le]
        ring
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hderiv (convex_uIcc t (t - u))
    left_mem_uIcc right_mem_uIcc
  simp only [Real.norm_eq_abs, sub_sub_cancel_left, abs_neg] at h
  dsimp [e] at h ⊢
  convert h using 1
  ring

/-- The actual error kernel is bounded by `C h d^(-s-1)` outside its smoothing
window. The constant is chosen before the mollifier and the circle length. -/
theorem inverseKernel_regularization_far (P : Parameters) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℝ → ℝ), IsMollifier ρ →
      ∀ L t h : ℝ, 0 < L → 0 < h → h ≤ latticeDist L t →
      |inverseKernel P L t - mollifyLine ρ h (inverseKernel P L) t| ≤
        C * h * latticeDist L t ^ (-P.val.2 - 1) := by
  obtain ⟨C, hC, hshift⟩ := inverseKernel_shift_bound P
  refine ⟨C, hC, fun ρ hρ L t h hL hh hd => ?_⟩
  have ht : ∀ k : ℤ, t ≠ k * L := by
    intro k hk
    have hz : latticeDist L t ≤ 0 := by
      simpa only [hk, sub_self, abs_zero] using latticeDist_le_abs_sub L t hL k
    linarith
  have hH : ∀ u : ℝ, |u| ≤ h / 2 →
      |inverseKernel P L (t - u) - inverseKernel P L t| ≤
        (C * latticeDist L t ^ (-P.val.2 - 1)) * |u| ^ (1 : ℝ) := by
    intro u hu
    have hb := hshift L t u hL ht (by linarith)
    simpa only [Real.rpow_one, mul_right_comm C |u|] using hb
  have hb := mollifyLine_sub_le_of_holder hρ hh (inverseKernel_locallyIntegrable P hL)
    (mul_nonneg hC.le (Real.rpow_nonneg (latticeDist_pos ht).le _)) (by norm_num : (0 : ℝ) ≤ 1) t hH
  rw [abs_sub_comm, Real.rpow_one] at hb
  calc _ ≤ (C * latticeDist L t ^ (-P.val.2 - 1)) * (h / 2) := hb
    _ ≤ (C * latticeDist L t ^ (-P.val.2 - 1)) * h :=
      mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg hC.le (Real.rpow_nonneg (latticeDist_pos ht).le _))
    _ = _ := by ring

/-- In the central smoothing window, `|P_L * ρ_h| ≤ C h^(-s)` uniformly
in the circle length. -/
theorem inverseKernel_mollify_near (P : Parameters) (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L t h : ℝ, 0 < L → 0 < h → h ≤ L / 4 → |t| ≤ h →
      |mollifyLine ρ h (inverseKernel P L) t| ≤ C * h ^ (-P.val.2) := by
  obtain ⟨D, hD, hkernel⟩ := abs_inverseKernel_le_cell P
  obtain ⟨M, hM, hmoll⟩ := hρ.exists_bound
  have hs : 0 < 1 - P.val.2 := sub_pos.mpr P.property.2.2
  let C := M * D * 2 * (3 / 2 : ℝ) ^ (1 - P.val.2) / (1 - P.val.2) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun L t h hL hh hhL ht => ?_⟩
  have hlocal := inverseKernel_locallyIntegrable P hL
  have hw := norm_integral_mul_le_window hlocal
    (contDiff_scaledMollifier hρ).continuous
    (abs_scaledMollifier_le hh hmoll)
    (fun u hu => scaledMollifier_eq_zero hρ hh hu) (x := t)
  have hPi : IntegrableOn (fun y => |inverseKernel P L y|)
      (Ioo (t - h / 2) (t + h / 2)) :=
    ((hlocal.integrableOn_isCompact isCompact_Icc).mono_set Ioo_subset_Icc_self).abs
  have hpowi : IntegrableOn (fun y : ℝ => D * |y| ^ (-P.val.2))
      (Ioo (t - h / 2) (t + h / 2)) := by
    have hp := intervalIntegrable_abs_rpow
      (show -1 < -P.val.2 by linarith [P.property.2.2]) (t - h / 2) (t + h / 2)
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).mp hp).const_mul D
  have hmass : (∫ y in Ioo (t - h / 2) (t + h / 2), |inverseKernel P L y|) ≤
      D * (2 * (3 * h / 2) ^ (1 - P.val.2) / (1 - P.val.2)) := by
    calc _ ≤ ∫ y in Ioo (t - h / 2) (t + h / 2), D * |y| ^ (-P.val.2) := by
          apply integral_mono_ae hPi hpowi
          filter_upwards [ae_restrict_mem measurableSet_Ioo,
            ae_restrict_of_ae (show ∀ᵐ y : ℝ, y ≠ 0 by rw [ae_iff]; simp)] with y hy hy0
          have hyabs : |y| < L / 2 := by
            have ht' := abs_le.mp ht
            have hy' : |y| < 3 * h / 2 :=
              abs_lt.mpr ⟨by linarith [hy.1, ht'.1], by linarith [hy.2, ht'.2]⟩
            exact hy'.trans (by linarith)
          exact hkernel L y hL hyabs hy0
      _ = D * ∫ y in (t - h / 2)..(t + h / 2), |y| ^ (-P.val.2) := by
          rw [integral_const_mul, intervalIntegral.integral_of_le (by linarith),
            integral_Ioc_eq_integral_Ioo]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hD.le
          simpa only [sub_zero] using integral_abs_sub_rpow_le_radius P.property.2.2
            (x := 0) (R := 3 * h / 2) (by positivity) (by linarith)
            (by linarith [abs_le.mp ht]) (by linarith [abs_le.mp ht])
  change |mollifyLine ρ h (inverseKernel P L) t| ≤ _
  unfold mollifyLine
  apply hw.trans ((mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ M * h⁻¹)).trans ?_)
  have he : h⁻¹ * h ^ (1 - P.val.2) = h ^ (-P.val.2) := by
    rw [← Real.rpow_neg_one h, ← Real.rpow_add hh]
    congr 1
    ring
  rw [show 3 * h / 2 = (3 / 2 : ℝ) * h by ring,
    Real.mul_rpow (by norm_num : 0 ≤ (3 / 2 : ℝ)) hh.le]
  have halg : M * h⁻¹ * (D * (2 * ((3 / 2 : ℝ) ^ (1 - P.val.2) * h ^ (1 - P.val.2)) /
      (1 - P.val.2))) =
      (M * D * 2 * (3 / 2 : ℝ) ^ (1 - P.val.2) / (1 - P.val.2)) *
        (h⁻¹ * h ^ (1 - P.val.2)) := by ring
  rw [halg, he]
  dsimp [C]
  nlinarith [Real.rpow_nonneg hh.le (-P.val.2)]

/-- The regularization-error kernel has `L¹` norm `O(h^(1-s))`. Its
integrability is part of the conclusion, including at the singular lattice.
The constant depends on the parameters and the fixed mollifier only. -/
theorem inverseKernel_regularization_L1 (P : Parameters) (ρ : ℝ → ℝ)
    (hρ : IsMollifier ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ L h : ℝ, 0 < L → 0 < h → h ≤ L / 4 →
      IntegrableOn (fun t => inverseKernel P L t - mollifyLine ρ h (inverseKernel P L) t)
        (Icc (-(L / 2)) (L / 2)) ∧
      (∫ t in Icc (-(L / 2)) (L / 2),
        |inverseKernel P L t - mollifyLine ρ h (inverseKernel P L) t|) ≤
          K * h ^ (1 - P.val.2) := by
  obtain ⟨A, hA, hnear⟩ := inverseKernel_mollify_near P ρ hρ
  obtain ⟨B, hB, hfar⟩ := inverseKernel_regularization_far P
  obtain ⟨D, hD, hkernel⟩ := abs_inverseKernel_le_cell P
  let s := P.val.2
  have hs0 : 0 < s := P.property.2.1
  have hs1 : s < 1 := P.property.2.2
  let J := 2 * D / (1 - s) + 2 * A
  let K := J + 2 * B / s
  have hK : 0 < K := by dsimp [K, J]; positivity
  refine ⟨K, hK, fun L h hL hh hhL => ?_⟩
  let E := fun t => inverseKernel P L t - mollifyLine ρ h (inverseKernel P L) t
  have hEi : LocallyIntegrable E volume :=
    (inverseKernel_locallyIntegrable P hL).sub
      (contDiff_mollifyLine_of_locallyIntegrable hρ hh
        (inverseKernel_locallyIntegrable P hL)).continuous.locallyIntegrable
  have hcenterI : IntervalIntegrable E volume (-h) h :=
    (hEi.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hpI : IntervalIntegrable (fun t : ℝ => |t| ^ (-s)) volume (-h) h :=
    intervalIntegrable_abs_rpow (by linarith) _ _
  have hcenter : (∫ t in (-h)..h, |E t|) ≤ J * h ^ (1 - s) := by
    calc _ ≤ ∫ t in (-h)..h, D * |t| ^ (-s) + A * h ^ (-s) := by
          apply intervalIntegral.integral_mono_ae_restrict (by linarith) hcenterI.abs
            ((hpI.const_mul D).add intervalIntegrable_const)
          filter_upwards [ae_restrict_mem measurableSet_Icc,
            ae_restrict_of_ae (show ∀ᵐ t : ℝ, t ≠ 0 by rw [ae_iff]; simp)] with t ht ht0
          have ht' : |t| ≤ h := abs_le.mpr ⟨ht.1, ht.2⟩
          exact (abs_sub _ _).trans (add_le_add
            (hkernel L t hL (ht'.trans_lt (by linarith)) ht0)
            (hnear L t h hL hh hhL ht'))
      _ = J * h ^ (1 - s) := by
          rw [intervalIntegral.integral_add (hpI.const_mul D) intervalIntegrable_const,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
            smul_eq_mul]
          have hp : (∫ t in (-h)..h, |t| ^ (-s)) = 2 * h ^ (1 - s) / (1 - s) := by
            rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
            exact integral_abs_rpow_symm hs1 hh.le
          rw [hp]
          have he : h * h ^ (-s) = h ^ (1 - s) := by
            conv_lhs => lhs; rw [← Real.rpow_one h]
            rw [← Real.rpow_add hh]
            congr 1
          dsimp [J]
          calc _ = (2 * D / (1 - s)) * h ^ (1 - s) + 2 * A * (h * h ^ (-s)) := by ring
            _ = _ := by rw [he]; ring
  have htail (t : ℝ) (ht : h ≤ |t|) (htL : |t| ≤ L / 2) :
      |E t| ≤ B * h * |t| ^ (-s - 1) := by
    have hdist : latticeDist L t = |t| := circDist_eq_abs hL htL
    have hb := hfar ρ hρ L t h hL hh (by rwa [hdist])
    simpa only [hdist] using hb
  have hi : IntervalIntegrable E volume (-(L / 2)) (L / 2) :=
    (hEi.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hnorm := integral_abs_two_tails_le hh (by linarith : h ≤ L / 2)
    (by positivity : 0 ≤ B * h) (by linarith : -s - 1 < -1) hi hcenter htail
  refine ⟨hEi.integrableOn_isCompact isCompact_Icc, ?_⟩
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  apply hnorm.trans
  change J * h ^ (1 - s) + 2 * (B * h / (-(-s - 1) - 1) * h ^ (-s - 1 + 1)) ≤
    K * h ^ (1 - s)
  rw [show -(-s - 1) - 1 = s by ring, show -s - 1 + 1 = -s by ring]
  have he : h * h ^ (-s) = h ^ (1 - s) := by
    conv_lhs => lhs; rw [← Real.rpow_one h]
    rw [← Real.rpow_add hh]
    congr 1
  dsimp [K]
  have halg : 2 * (B * h / s * h ^ (-s)) = (2 * B / s) * (h * h ^ (-s)) := by ring
  rw [halg, he]
  ring_nf
  exact le_rfl

end Riesz1
