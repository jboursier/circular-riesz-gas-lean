/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelFubini
public import Riesz1.ToMathlib.MollifierPointwise.Circle
public import Riesz1.ToMathlib.MollifyLocalDerivative
public import Riesz1.ToMathlib.AbsRpowRadius
public import Riesz1.ToMathlib.IntegrableTwoTails
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Increment estimates for the derivative of the inverse kernel

The mean value theorem and the second-derivative bound give
`|P_L'(t-u) - P_L'(t)| ≤ C |u| d(t,Lℤ)^(-s-2)` when
`|u| ≤ d(t,Lℤ)/2`. The constant precedes the circle length.
This is the far-region kernel estimate in Lemma 5.3.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The period-integrability certificate gives local integrability
on the whole real cover, including the lattice points. -/
theorem inverseKernel_locallyIntegrable (P : Parameters) {L : ℝ} (hL : 0 < L) :
    LocallyIntegrable (inverseKernel P L) volume := by
  intro x
  refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
    (intervalIntegrable_inverseKernel P hL (x - 1) (x + 1))

/-- A uniform first-order increment estimate for `P_L'` on a segment that
stays at least half the original distance away from every lattice point. -/
theorem inverseKernel_deriv_shift_bound (P : Parameters) :
    ∃ C : ℝ, 0 < C ∧ ∀ L t u : ℝ, 0 < L →
      (∀ k : ℤ, t ≠ k * L) → |u| ≤ latticeDist L t / 2 →
      |deriv (inverseKernel P L) (t - u) - deriv (inverseKernel P L) t| ≤
        C * |u| * latticeDist L t ^ (-P.val.2 - 2) := by
  obtain ⟨D, hD, hbound⟩ := inverseKernel_iteratedDeriv_bound P 2
  let e := -P.val.2 - 2
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
      have h := latticeDist_le_abs_sub L z hL k
      simpa only [hk, sub_self, abs_zero] using h
    linarith [hdist z hz]
  have hdiff (z : ℝ) (hz : z ∈ uIcc t (t - u)) :
      DifferentiableAt ℝ (deriv (inverseKernel P L)) z :=
    ((contDiffAt_inverseKernel P hL (hne z hz)).derivWithin (m := 1) (by simp)).differentiableAt
      (by norm_num)
  have hderiv (z : ℝ) (hz : z ∈ uIcc t (t - u)) :
      ‖deriv (deriv (inverseKernel P L)) z‖ ≤
        D * (1 / 2 : ℝ) ^ e * latticeDist L t ^ e := by
    have h := hbound L z hL (hne z hz)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_ofNat, Real.norm_eq_abs] at h ⊢
    have hp : latticeDist L z ^ e ≤ (latticeDist L t / 2) ^ e :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (hdist z hz) he
    calc |deriv (deriv (inverseKernel P L)) z|
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

/-- Averaging `P_L'` over a mollifier window separated from the singular lattice
has error `C h d^(-s-2)`. Absolute integrability of this average is part of the
conclusion. No global integrability of the singular derivative is presumed. -/
theorem inverseKernel_deriv_average_far (P : Parameters) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℝ → ℝ), IsMollifier ρ →
      ∀ L t h : ℝ, 0 < L → 0 < h → (∀ k : ℤ, t ≠ k * L) →
        h ≤ latticeDist L t →
      Integrable (fun u => deriv (inverseKernel P L) (t - u) * scaledMollifier ρ h u) ∧
      |deriv (inverseKernel P L) t -
        ∫ u, deriv (inverseKernel P L) (t - u) * scaledMollifier ρ h u| ≤
          C * h * latticeDist L t ^ (-P.val.2 - 2) := by
  obtain ⟨C, hC, hshift⟩ := inverseKernel_deriv_shift_bound P
  refine ⟨C, hC, fun ρ hρ L t h hL hh ht hd => ?_⟩
  let A := C * h * latticeDist L t ^ (-P.val.2 - 2)
  let F : ℝ → ℝ := fun u =>
    (deriv (inverseKernel P L) (t - u) - deriv (inverseKernel P L) t) *
      scaledMollifier ρ h u
  have hκ : Integrable (scaledMollifier ρ h) :=
    (contDiff_scaledMollifier hρ).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_scaledMollifier hρ hh)
  have hm : Measurable F :=
    (((measurable_deriv _).comp (measurable_const.sub measurable_id)).sub measurable_const).mul
      (contDiff_scaledMollifier hρ).continuous.measurable
  have hmajor (u : ℝ) : ‖F u‖ ≤ A * scaledMollifier ρ h u := by
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (scaledMollifier_nonneg hρ hh u)]
    by_cases hu : h / 2 ≤ |u|
    · rw [scaledMollifier_eq_zero hρ hh hu, mul_zero, mul_zero]
    · have hu' : |u| ≤ latticeDist L t / 2 := by linarith [lt_of_not_ge hu]
      have hb := hshift L t u hL ht hu'
      have hCh : C * |u| ≤ C * h := mul_le_mul_of_nonneg_left (by linarith [lt_of_not_ge hu]) hC.le
      have hpower : 0 ≤ latticeDist L t ^ (-P.val.2 - 2) :=
        Real.rpow_nonneg (latticeDist_pos ht).le _
      exact mul_le_mul_of_nonneg_right
        (hb.trans (mul_le_mul_of_nonneg_right hCh hpower)) (scaledMollifier_nonneg hρ hh u)
  have hFi : Integrable F := (hκ.const_mul A).mono' hm.aestronglyMeasurable
    (ae_of_all _ hmajor)
  have hci : Integrable (fun u => deriv (inverseKernel P L) t * scaledMollifier ρ h u) :=
    hκ.const_mul _
  have hgi : Integrable (fun u => deriv (inverseKernel P L) (t - u) * scaledMollifier ρ h u) :=
    (hFi.add hci).congr (ae_of_all _ fun u => by dsimp [F]; ring)
  have hsplit : ∫ u, F u =
      (∫ u, deriv (inverseKernel P L) (t - u) * scaledMollifier ρ h u) -
        deriv (inverseKernel P L) t := by
    dsimp only [F]
    simp_rw [sub_mul]
    rw [integral_sub hgi hci, integral_const_mul, integral_scaledMollifier hρ hh, mul_one]
  refine ⟨hgi, ?_⟩
  have hb := norm_integral_le_of_norm_le (hκ.const_mul A) (ae_of_all _ hmajor)
  rw [hsplit, Real.norm_eq_abs, integral_const_mul, integral_scaledMollifier hρ hh, mul_one,
    abs_sub_comm] at hb
  exact hb

/-- The far-region error estimate for the classical derivative of the actual
smoothed kernel. It is the `d > h` half of the bound on `R_h`.
The constant is chosen before both the mollifier and the circle length. -/
theorem inverseKernel_deriv_regularization_far (P : Parameters) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℝ → ℝ), IsMollifier ρ →
      ∀ L t h : ℝ, 0 < L → 0 < h → h < latticeDist L t →
      |deriv (inverseKernel P L) t - deriv (mollifyLine ρ h (inverseKernel P L)) t| ≤
        C * h * latticeDist L t ^ (-P.val.2 - 2) := by
  obtain ⟨C, hC, haverage⟩ := inverseKernel_deriv_average_far P
  obtain ⟨D, hD, hfirst⟩ := inverseKernel_iteratedDeriv_bound P 1
  refine ⟨C, hC, fun ρ hρ L t h hL hh hd => ?_⟩
  have hdist (y : ℝ) (hy : |y - t| < h) :
      latticeDist L t - h ≤ latticeDist L y := by
    have h := circDist_le_add_abs hL t y
    change latticeDist L t ≤ latticeDist L y + |t - y| at h
    rw [abs_sub_comm t y] at h
    linarith
  have hne (y : ℝ) (hy : |y - t| < h) : ∀ k : ℤ, y ≠ k * L := by
    intro k hk
    have hzero : latticeDist L y ≤ 0 := by
      simpa only [hk, sub_self, abs_zero] using latticeDist_le_abs_sub L y hL k
    linarith [hdist y hy]
  have hdifferentiable (y : ℝ) (hy : |y - t| < h) :
      DifferentiableAt ℝ (inverseKernel P L) y :=
    (contDiffAt_inverseKernel P hL (hne y hy)).differentiableAt (by simp)
  have hbound (y : ℝ) (hy : |y - t| < h) :
      |deriv (inverseKernel P L) y| ≤ D * (latticeDist L t - h) ^ (-P.val.2 - 1) := by
    have hb := hfirst L y hL (hne y hy)
    simp only [iteratedDeriv_one, Nat.cast_one] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hd) (hdist y hy)
        (by linarith [P.property.2.1])) hD.le)
  have hsmooth := hasDerivAt_mollifyLine_of_local hρ hh
    (inverseKernel_locallyIntegrable P hL) hdifferentiable hbound
  rw [hsmooth.deriv]
  have ht : ∀ k : ℤ, t ≠ k * L := hne t (by simpa using hh)
  exact (haverage ρ hρ L t h hL hh ht hd.le).2

/-- In the central smoothing window, differentiating the mollifier gives
`|P_L * ρ_h'| ≤ C h^(-s-1)`. The bound is uniform in the circle length.
The smoothing radius is small enough that the window meets only one lattice point. -/
theorem inverseKernel_mollify_deriv_near (P : Parameters) (ρ : ℝ → ℝ)
    (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L t h : ℝ, 0 < L → 0 < h → h ≤ L / 4 → |t| ≤ h →
      |deriv (mollifyLine ρ h (inverseKernel P L)) t| ≤ C * h ^ (-P.val.2 - 1) := by
  obtain ⟨D, hD, hkernel⟩ := abs_inverseKernel_le_cell P
  obtain ⟨M, hM, hmoll⟩ := hρ.exists_bound_deriv
  let C := M * D * 2 * (3 / 2 : ℝ) ^ (1 - P.val.2) / (1 - P.val.2) + 1
  have hs : 0 < 1 - P.val.2 := sub_pos.mpr P.property.2.2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun L t h hL hh hhL ht => ?_⟩
  have hlocal := inverseKernel_locallyIntegrable P hL
  rw [(hasDerivAt_mollifyLine hρ hh hlocal t).deriv]
  have hw := norm_integral_mul_le_window hlocal
    ((contDiff_scaledMollifier hρ).continuous_deriv (by simp))
    (abs_deriv_scaledMollifier_le hρ hh hmoll)
    (fun u hu => deriv_scaledMollifier_eq_zero hρ hh hu) (x := t)
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
  have hscale : M * h⁻¹ ^ 2 *
      (D * (2 * (3 * h / 2) ^ (1 - P.val.2) / (1 - P.val.2))) =
      (M * D * 2 * (3 / 2 : ℝ) ^ (1 - P.val.2) / (1 - P.val.2)) *
        h ^ (-P.val.2 - 1) := by
    rw [show 3 * h / 2 = (3 / 2 : ℝ) * h by ring, Real.mul_rpow (by norm_num) hh.le,
      ← Real.rpow_neg_one h, ← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    norm_num only [Nat.cast_ofNat, neg_mul, one_mul]
    have he : h ^ (-2 : ℝ) * h ^ (1 - P.val.2) = h ^ (-P.val.2 - 1) := by
      rw [← Real.rpow_add hh]
      congr 1
      ring
    calc _ = (M * D * 2 * (3 / 2 : ℝ) ^ (1 - P.val.2) / (1 - P.val.2)) *
          (h ^ (-2 : ℝ) * h ^ (1 - P.val.2)) := by ring
      _ = _ := by rw [he]
  exact hw.trans ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans
    (by rw [← sq, hscale]; dsimp [C]; nlinarith [Real.rpow_nonneg hh.le (-P.val.2 - 1)]))

/-- Both pointwise bounds for the regularization-error kernel on the central
cell. Here `τ = 1-s`, so the exponents are `τ-2` and `τ-3`, respectively. -/
theorem inverseKernel_deriv_regularization_bounds (P : Parameters) (ρ : ℝ → ℝ)
    (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L t h : ℝ, 0 < L → 0 < h → h ≤ L / 4 →
      |t| ≤ L / 2 → t ≠ 0 →
      (|t| ≤ h →
        |deriv (inverseKernel P L) t - deriv (mollifyLine ρ h (inverseKernel P L)) t| ≤
          C * (|t| ^ (-P.val.2 - 1) + h ^ (-P.val.2 - 1))) ∧
      (h < |t| →
        |deriv (inverseKernel P L) t - deriv (mollifyLine ρ h (inverseKernel P L)) t| ≤
          C * h * |t| ^ (-P.val.2 - 2)) := by
  obtain ⟨A, hA, hnear⟩ := inverseKernel_mollify_deriv_near P ρ hρ
  obtain ⟨B, hB, hfar⟩ := inverseKernel_deriv_regularization_far P
  obtain ⟨D, hD, hfirst⟩ := inverseKernel_iteratedDeriv_bound P 1
  let C := A + B + D
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith
  refine ⟨C, by dsimp [C]; positivity, fun L t h hL hh hhL htL ht0 => ?_⟩
  have hdist : latticeDist L t = |t| := circDist_eq_abs hL htL
  have ht : ∀ k : ℤ, t ≠ k * L := by
    intro k hk
    have hz : latticeDist L t ≤ 0 := by
      simpa only [hk, sub_self, abs_zero] using latticeDist_le_abs_sub L t hL k
    rw [hdist] at hz
    exact ht0 (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))
  constructor
  · intro hth
    have hp := hfirst L t hL ht
    simp only [iteratedDeriv_one, Nat.cast_one, hdist] at hp
    have hm := hnear L t h hL hh hhL hth
    calc _ ≤ |deriv (inverseKernel P L) t| +
          |deriv (mollifyLine ρ h (inverseKernel P L)) t| := abs_sub _ _
      _ ≤ D * |t| ^ (-P.val.2 - 1) + A * h ^ (-P.val.2 - 1) := add_le_add hp hm
      _ ≤ C * (|t| ^ (-P.val.2 - 1) + h ^ (-P.val.2 - 1)) := by
        nlinarith [mul_le_mul_of_nonneg_right hDC (Real.rpow_nonneg (abs_nonneg t) (-P.val.2 - 1)),
          mul_le_mul_of_nonneg_right hAC (Real.rpow_nonneg hh.le (-P.val.2 - 1))]
  · intro hht
    have hb := hfar ρ hρ L t h hL hh (by rwa [hdist])
    rw [hdist] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hBC hh.le) (Real.rpow_nonneg (abs_nonneg t) _))

/-- The absolute first moment of the regularization-error derivative is
`O(h^(1-s))`. Integrability is proved as part of the statement. The kernel
derivative itself is not asserted to be integrable at zero. -/
theorem inverseKernel_deriv_regularization_firstMoment (P : Parameters) (ρ : ℝ → ℝ)
    (hρ : IsMollifier ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ L h : ℝ, 0 < L → 0 < h → h ≤ L / 4 →
      IntegrableOn (fun t => |t| *
        |deriv (inverseKernel P L) t - deriv (mollifyLine ρ h (inverseKernel P L)) t|)
        (Icc (-(L / 2)) (L / 2)) ∧
      (∫ t in (-(L / 2))..(L / 2), |t| *
        |deriv (inverseKernel P L) t - deriv (mollifyLine ρ h (inverseKernel P L)) t|) ≤
          K * h ^ (1 - P.val.2) := by
  obtain ⟨C, hC, hkernel⟩ := inverseKernel_deriv_regularization_bounds P ρ hρ
  let s := P.val.2
  have hs0 : 0 < s := P.property.2.1
  have hs1 : s < 1 := P.property.2.2
  let K := C * (2 / (1 - s) + 2 + 4 / s)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, fun L h hL hh hhL => ?_⟩
  let q : ℝ → ℝ := fun t => |t| *
    |deriv (inverseKernel P L) t - deriv (mollifyLine ρ h (inverseKernel P L)) t|
  have hqn (t : ℝ) : 0 ≤ q t := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hqm : Measurable q := continuous_abs.measurable.mul
    (continuous_abs.measurable.comp ((measurable_deriv _).sub (measurable_deriv _)))
  have hmul (u : ℝ) (hu : 0 < u) (e : ℝ) : u * u ^ e = u ^ (e + 1) := by
    calc u * u ^ e = u ^ (1 : ℝ) * u ^ e := by rw [Real.rpow_one]
      _ = u ^ (e + 1) := by rw [← Real.rpow_add hu]; congr 1; ring
  have hnear (t : ℝ) (ht : |t| ≤ h) :
      q t ≤ C * (|t| ^ (-s) + |t| * h ^ (-s - 1)) := by
    by_cases ht0 : t = 0
    · subst ht0
      dsimp [q]
      simp only [abs_zero, zero_mul]
      positivity
    · have hb := (hkernel L t h hL hh hhL (by linarith) ht0).1 ht
      have htpos := abs_pos.mpr ht0
      have he := hmul |t| htpos (-s - 1)
      rw [show -s - 1 + 1 = -s by ring] at he
      calc q t ≤ |t| * (C * (|t| ^ (-s - 1) + h ^ (-s - 1))) :=
            mul_le_mul_of_nonneg_left hb (abs_nonneg t)
        _ = C * (|t| ^ (-s) + |t| * h ^ (-s - 1)) := by rw [← he]; ring
  have hfar (t : ℝ) (ht : h < |t|) (htL : |t| ≤ L / 2) :
      q t ≤ C * h * |t| ^ (-s - 1) := by
    have ht0 : t ≠ 0 := by intro ht0; simp only [ht0, abs_zero] at ht; linarith
    have hb := (hkernel L t h hL hh hhL htL ht0).2 ht
    have he := hmul |t| (abs_pos.mpr ht0) (-s - 2)
    rw [show -s - 2 + 1 = -s - 1 by ring] at he
    calc q t ≤ |t| * (C * h * |t| ^ (-s - 2)) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg t)
      _ = C * h * |t| ^ (-s - 1) := by rw [← he]; ring
  have hmajor (t : ℝ) (htL : |t| ≤ L / 2) :
      q t ≤ C * (|t| ^ (-s) + |t| * h ^ (-s - 1)) := by
    by_cases ht : |t| ≤ h
    · exact hnear t ht
    · have ht' : h < |t| := lt_of_not_ge ht
      have he := hmul |t| (lt_trans hh ht') (-s - 1)
      rw [show -s - 1 + 1 = -s by ring] at he
      calc q t ≤ C * h * |t| ^ (-s - 1) := hfar t ht' htL
        _ ≤ C * |t| * |t| ^ (-s - 1) := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left ht'.le hC.le) (by positivity)
        _ = C * |t| ^ (-s) := by rw [mul_assoc, he]
        _ ≤ _ := by
          have hn : 0 ≤ C * (|t| * h ^ (-s - 1)) := by positivity
          nlinarith
  have hmajorI : IntegrableOn (fun t : ℝ => C * (|t| ^ (-s) + |t| * h ^ (-s - 1)))
      (Icc (-(L / 2)) (L / 2)) :=
    ((integrableOn_abs_rpow (by linarith) (by positivity)).add
      ((continuous_abs.mul continuous_const).continuousOn.integrableOn_Icc)).const_mul C
  have hqi : IntegrableOn q (Icc (-(L / 2)) (L / 2)) := by
    refine hmajorI.mono' hqm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hqn t)]
    exact hmajor t (abs_le.mpr ⟨ht.1, ht.2⟩)
  have hqmid : IntervalIntegrable q volume (-h) h :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr
      (hqi.mono_set (Icc_subset_Icc (by linarith) (by linarith)))
  have hcenter : (∫ t in (-h)..h, q t) ≤
      C * (2 / (1 - s) + 2) * h ^ (1 - s) := by
    have hpi : IntervalIntegrable (fun t : ℝ => |t| ^ (-s)) volume (-h) h :=
      intervalIntegrable_abs_rpow (by linarith) _ _
    calc _ ≤ ∫ t in (-h)..h, C * (|t| ^ (-s) + h ^ (-s)) := by
          apply intervalIntegral.integral_mono_ae_restrict (by linarith) hqmid
            ((hpi.add intervalIntegrable_const).const_mul C)
          filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          have ht' : |t| ≤ h := abs_le.mpr ⟨ht.1, ht.2⟩
          have he := hmul h hh (-s - 1)
          rw [show -s - 1 + 1 = -s by ring] at he
          have hb : |t| * h ^ (-s - 1) ≤ h ^ (-s) := by
            simpa only [he] using
              mul_le_mul_of_nonneg_right ht' (Real.rpow_nonneg hh.le (-s - 1))
          exact (hnear t ht').trans
            (mul_le_mul_of_nonneg_left (add_le_add le_rfl hb) hC.le)
      _ = C * (2 / (1 - s) + 2) * h ^ (1 - s) := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_add hpi intervalIntegrable_const,
            intervalIntegral.integral_const, smul_eq_mul]
          have hp : (∫ t in (-h)..h, |t| ^ (-s)) = 2 * h ^ (1 - s) / (1 - s) := by
            rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
            exact integral_abs_rpow_symm hs1 hh.le
          rw [hp]
          have he := hmul h hh (-s)
          rw [show -s + 1 = 1 - s by ring] at he
          calc _ = C * (2 * h ^ (1 - s) / (1 - s) + 2 * (h * h ^ (-s))) := by ring
            _ = _ := by rw [he]; ring
  have htail (t : ℝ) (ht : h ≤ |t|) (htL : |t| ≤ L / 2) :
      |q t| ≤ (2 * C * h) * |t| ^ (-s - 1) := by
    rw [abs_of_nonneg (hqn t)]
    rcases ht.eq_or_lt with ht | ht
    · have he := hmul h hh (-s - 1)
      rw [show -s - 1 + 1 = -s by ring] at he
      have hb := hnear t (by linarith)
      rw [← ht, he] at hb
      rw [← ht]
      calc q t ≤ C * (h ^ (-s) + h ^ (-s)) := hb
        _ = 2 * C * h * h ^ (-s - 1) := by rw [← he]; ring
    · exact (hfar t ht htL).trans (by
        nlinarith [mul_nonneg (mul_nonneg hC.le hh.le)
          (Real.rpow_nonneg (abs_nonneg t) (-s - 1))])
  have hi : IntervalIntegrable q volume (-(L / 2)) (L / 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr hqi
  have hnorm := integral_abs_two_tails_le hh (by linarith : h ≤ L / 2)
    (by positivity : 0 ≤ 2 * C * h) (by linarith : -s - 1 < -1) hi
    (by simpa only [abs_of_nonneg (hqn _)] using hcenter) htail
  simp only [abs_of_nonneg (hqn _)] at hnorm
  refine ⟨hqi, hnorm.trans ?_⟩
  have he := hmul h hh (-s)
  rw [show -s + 1 = 1 - s by ring] at he
  change C * (2 / (1 - s) + 2) * h ^ (1 - s) +
    2 * (2 * C * h / (-(-s - 1) - 1) * h ^ (-s - 1 + 1)) ≤ K * h ^ (1 - s)
  rw [show -(-s - 1) - 1 = s by ring, show -s - 1 + 1 = -s by ring]
  dsimp [K]
  have halg : 2 * (2 * C * h / s * h ^ (-s)) = (4 * C / s) * (h * h ^ (-s)) := by ring
  rw [halg, he]
  ring_nf
  exact le_rfl

end Riesz1
