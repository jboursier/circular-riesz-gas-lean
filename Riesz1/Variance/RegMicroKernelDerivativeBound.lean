/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelCutoff
public import Riesz1.ToMathlib.CircleFiniteMarkConvolution
public import Riesz1.ToMathlib.PeriodicConvolutionSmoothing
public import Riesz1.ToMathlib.FiniteMarkDistanceLocal

/-!
# The quantitative inverse convolution derivative

This internal analytic estimate applies the periodic near/far differentiation
identity at a radius proportional to the actual capped mark distance. Its
constant is uniform in the circle length and the marked points. Transport
envelopes are analytic inputs here, to be supplied by the transport
bounds when applying this estimate to the profile.
-/

public section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

namespace Riesz1.Internal

/-- Uniform derivative estimate for the actual inverse convolution, from
the two transport envelopes. This is an internal analytic helper, not a theorem
of the paper, and it takes the estimates as added hypotheses. -/
theorem inverseConv_deriv_bound (P : Parameters) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (ι : Type*) [Fintype ι] [Nonempty ι] :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ) [Fact (0 < L)] (marks : ι → ℝ)
      (q : ℝ → ℝ) (A : ℝ), 0 ≤ A → Measurable q →
      Function.Periodic q L → LocallyIntegrable q volume →
      (∀ y : ℝ, (∀ j, (y : AddCircle L) ≠ (marks j : AddCircle L)) →
        ContDiffAt ℝ 1 q y ∧
        |q y| ≤ A * cappedMarkDistance (fun j => (marks j : AddCircle L)) (y : AddCircle L) ^ (-b) ∧
        |deriv q y| ≤ A *
          cappedMarkDistance (fun j => (marks j : AddCircle L)) (y : AddCircle L) ^ (-1 - b)) →
      ∀ c : ℝ, (∀ j, (c : AddCircle L) ≠ (marks j : AddCircle L)) →
        IntegrableOn (fun y => q y * inverseKernel P L (c - y)) (Ioc (-(L / 2)) (L / 2)) ∧
        DifferentiableAt ℝ (inverseConv P L q) c ∧
        |deriv (inverseConv P L q) c| ≤
          C * A * cappedMarkDistance (fun j => (marks j : AddCircle L))
            (c : AddCircle L) ^ (-P.val.2 - b) := by
  obtain ⟨K, hK, hcut⟩ := inverseKernel_quantitative_cutoff P
  obtain ⟨J, hJ, hfar⟩ := CirclePowerConvolution.integral_far_power_capped_le
    P.property.2.1 hb hb1 ι
  let C₀ := K * (1 / 4 : ℝ) ^ (-1 - b) * (1 / 2 : ℝ) ^ (1 - P.val.2)
  let C := C₀ + K * J
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨C, by dsimp [C]; positivity, fun L hL marks q A hA hqm hqp hqi hq c hc => ?_⟩
  let r := cappedMarkDistance (fun j => (marks j : AddCircle L)) (c : AddCircle L)
  have hr : 0 < r := cappedMarkDistance_pos _ _ hc
  have hr1 : r ≤ 1 := cappedMarkDistance_le_one _ _
  have hrL : r ≤ L / 2 := by
    obtain ⟨j⟩ := ‹Nonempty ι›
    apply (cappedMarkDistance_le_dist _ _ j).trans
    rw [dist_eq_norm]
    simpa only [abs_of_pos hL.out] using AddCircle.norm_le_half_period L hL.out.ne'
  let a := r / 2
  let ε := r / 8
  have ha : 0 < a := by dsimp [a]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have haL : a < L / 2 := by dsimp [a]; linarith [hL.out]
  obtain ⟨χ, hχ, hχb, _heven, hzero, _hone, _hχd, _hχout, hkernel⟩ := hcut a ha
  obtain ⟨hNs, hNi, hmass, hFs, hFd⟩ := hkernel L hL.out haL
  let N := fun t => inverseKernel P L t * (1 - χ t)
  let F := fun t => inverseKernel P L t * χ t
  have hFreg (t : ℝ) (ht : |t| < L) : ContDiffAt ℝ 1 F t :=
    (hFs t (abs_lt.mp ht)).contDiffAt (isOpen_Ioo.mem_nhds (abs_lt.mp ht))
  have hFc : ContinuousOn F (Icc (-(3 * L / 4)) (3 * L / 4)) := by
    intro t ht
    exact (hFreg t (abs_lt.mpr ⟨by linarith [ht.1, hL.out],
      by linarith [ht.2, hL.out]⟩)).continuousAt.continuousWithinAt
  have hFdc : ContinuousOn (deriv F) (Icc (-(3 * L / 4)) (3 * L / 4)) := by
    intro t ht
    exact ((hFreg t (abs_lt.mpr ⟨by linarith [ht.1, hL.out],
      by linarith [ht.2, hL.out]⟩)).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hFc
  obtain ⟨B₁, hB₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hFdc
  have hnear (x : ℝ) (hx : x ∈ ball c ε) (t : ℝ) (ht : t ∈ Ioc (-a) a) :
      r / 4 ≤ cappedMarkDistance (fun j => (marks j : AddCircle L)) ((x - t : ℝ) : AddCircle L) := by
    apply le_cappedMarkDistance_of_dist (fun j => (marks j : AddCircle L))
      (x := (c : AddCircle L)) (r := r) (by linarith) le_rfl
    have hx' : |x - c| < ε := by simpa only [mem_ball, Real.dist_eq] using hx
    have ht' : |t| ≤ a := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have hd : dist (c : AddCircle L) ((x - t : ℝ) : AddCircle L) ≤ |c - (x - t)| :=
      by
        rw [dist_eq_norm, ← AddCircle.coe_sub]
        exact (QuotientAddGroup.norm_mk_le_norm (m := c - (x - t))
          (S := AddSubgroup.zmultiples L)).trans_eq (Real.norm_eq_abs _)
    have hab : |c - (x - t)| ≤ |x - c| + |t| := by
      calc _ = |-(x - c) + t| := by congr 1; ring
        _ ≤ |-(x - c)| + |t| := abs_add_le _ _
        _ = _ := by rw [abs_neg]
    dsimp [ε, a] at *
    linarith
  have hgood (x : ℝ) (hx : x ∈ ball c ε) (t : ℝ) (ht : t ∈ Ioc (-a) a) :
      ∀ j, ((x - t : ℝ) : AddCircle L) ≠ (marks j : AddCircle L) := by
    intro j hj
    have hd := (hnear x hx t ht).trans (cappedMarkDistance_le_dist _ _ j)
    rw [hj, dist_self] at hd
    linarith
  have hfarRange (x : ℝ) (hx : x ∈ ball c ε) (y : ℝ)
      (hy : y ∈ Ioc (c - L / 2) (c + L / 2)) :
      x - y ∈ Icc (-(3 * L / 4)) (3 * L / 4) := by
    have hx' : |x - c| < ε := by simpa only [mem_ball, Real.dist_eq] using hx
    obtain ⟨hx0, hx1⟩ := abs_lt.mp hx'
    dsimp [ε] at *
    constructor <;> linarith [hy.1, hy.2]
  let M := A * (r / 4) ^ (-1 - b)
  obtain ⟨hconvI, hconvD⟩ := PeriodicConvolution.hasDerivAt_split
    (q := q) (K := inverseKernel P L) (N := N) (F := F)
    (a := a) (c := c) (ε := ε) (A := A * (r / 4) ^ (-b)) (B := max B₀ B₁) (M := M)
    hL.out ha.le hε (by dsimp [a, ε]; linarith) hqp (inverseKernel_periodic P hL.out)
    hqm ((hqi.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self)
    (hNi.mono_set Ioc_subset_Icc_self) hNs ((measurable_inverseKernel P hL.out).mul hχ.continuous.measurable)
    (fun t => by dsimp [N, F]; ring)
    (fun x hx t ht => (hq _ (hgood x hx t ht)).2.1.trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity)
        (hnear x hx t ht) (by linarith)) hA))
    (fun x hx t ht => ⟨(hq _ (hgood x hx t ht)).1.differentiableAt (by norm_num),
      (hq _ (hgood x hx t ht)).2.2.trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity)
          (hnear x hx t ht) (by linarith)) hA)⟩)
    (fun x hx y hy => by
      have ht : |F (x - y)| ≤ B₀ := by simpa only [Real.norm_eq_abs] using hB₀ _ (hfarRange x hx y hy)
      exact ht.trans (le_max_left _ _))
    (fun x hx y hy => ⟨(hFreg _ (abs_lt.mpr ⟨by linarith [(hfarRange x hx y hy).1, hL.out],
      by linarith [(hfarRange x hx y hy).2, hL.out]⟩)).differentiableAt (by norm_num),
      (show |deriv F (x - y)| ≤ max B₀ B₁ from by
        have ht : |deriv F (x - y)| ≤ B₁ := by simpa only [Real.norm_eq_abs] using hB₁ _ (hfarRange x hx y hy)
        exact ht.trans (le_max_right _ _))⟩)
  refine ⟨hconvI, hconvD.differentiableAt, ?_⟩
  change |deriv (fun x => ∫ y in Ioc (-(L / 2)) (L / 2), q y * inverseKernel P L (x - y)) c| ≤ _
  rw [hconvD.deriv]
  have hnearInt : |∫ t in Ioc (-a) a, deriv q (c - t) * N t| ≤ C₀ * A * r ^ (-P.val.2 - b) := by
    have hm : 0 ≤ M := by dsimp [M]; positivity
    have hbound : |∫ t in Ioc (-a) a, deriv q (c - t) * N t| ≤
        M * ∫ t in Ioc (-a) a, |N t| := by
      have hn := norm_integral_le_of_norm_le
        ((hNi.mono_set Ioc_subset_Icc_self).abs.const_mul M)
        (show ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (-a) a)),
          ‖deriv q (c - t) * N t‖ ≤ M * |N t| from by
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            exact (hq _ (hgood c (mem_ball_self hε) t ht)).2.2.trans
              (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity)
                (hnear c (mem_ball_self hε) t ht) (by linarith)) hA))
      simpa only [Real.norm_eq_abs, integral_const_mul] using hn
    have hmass' : (∫ t in Ioc (-a) a, |N t|) ≤ K * a ^ (1 - P.val.2) := by
      rw [← integral_Icc_eq_integral_Ioc]
      exact hmass
    apply hbound.trans ((mul_le_mul_of_nonneg_left hmass' hm).trans_eq ?_)
    dsimp [M, a, C₀]
    rw [show r / 4 = (1 / 4 : ℝ) * r by ring,
      show r / 2 = (1 / 2 : ℝ) * r by ring,
      Real.mul_rpow (by norm_num : 0 ≤ (1 / 4 : ℝ)) hr.le,
      Real.mul_rpow (by norm_num : 0 ≤ (1 / 2 : ℝ)) hr.le]
    have he : r ^ (-1 - b) * r ^ (1 - P.val.2) = r ^ (-P.val.2 - b) := by
      rw [← Real.rpow_add hr]; congr 1; ring
    calc _ = (K * (1 / 4 : ℝ) ^ (-1 - b) * (1 / 2 : ℝ) ^ (1 - P.val.2)) * A *
        (r ^ (-1 - b) * r ^ (1 - P.val.2)) := by ring
      _ = _ := by rw [he]
  obtain ⟨hUi, hUb⟩ := hfar L marks c r hr le_rfl q A hA hqm (fun y hy => (hq y hy).2.1)
  let U := fun y => (Ici (r / 4)).indicator (fun t : ℝ => t ^ (-P.val.2 - 1))
    (circDist L (y - c)) * |q y|
  have hUp : Function.Periodic U L := by
    intro y
    dsimp [U]
    rw [hqp y, show y + L - c = (y - c) + L by ring, circDist_add_period hL.out]
  have hUshift : IntegrableOn U (Ioc (c - L / 2) (c + L / 2)) := by
    have hi := PeriodicConvolution.intervalIntegrable_of_period hL.out hUp hUi
      (c - L / 2) (c + L / 2)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [hL.out])).mp hi
  have hUeq : (∫ y in Ioc (c - L / 2) (c + L / 2), U y) =
      ∫ y in Ioc (-(L / 2)) (L / 2), U y := by
    rw [← intervalIntegral.integral_of_le (by linarith [hL.out]),
      ← intervalIntegral.integral_of_le (by linarith [hL.out])]
    convert hUp.intervalIntegral_add_eq (c - L / 2) (-(L / 2)) using 1 <;> congr 1 <;> ring
  have hfarInt : |∫ y in Ioc (c - L / 2) (c + L / 2), q y * deriv F (c - y)| ≤
      K * J * A * r ^ (-P.val.2 - b) := by
    have hn := norm_integral_le_of_norm_le (hUshift.const_mul K)
      (show ∀ᵐ y : ℝ ∂(volume.restrict (Ioc (c - L / 2) (c + L / 2))),
        ‖q y * deriv F (c - y)‖ ≤ K * U y from by
          filter_upwards [ae_restrict_mem measurableSet_Ioc,
            ae_restrict_of_ae (show ∀ᵐ y : ℝ, y ≠ c + L / 2 by rw [ae_iff]; simp)] with y hy hyend
          have hylt : y < c + L / 2 := lt_of_le_of_ne hy.2 hyend
          have ht : |c - y| < L / 2 := abs_lt.mpr ⟨by linarith, by linarith [hy.1]⟩
          have hd : circDist L (y - c) = |c - y| := by
            rw [circDist_eq_abs hL.out (by rw [abs_sub_comm]; exact ht.le), abs_sub_comm]
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          have hb := mul_le_mul_of_nonneg_left (hFd (c - y) ht) (abs_nonneg (q y))
          have hb' : |q y| * |deriv F (c - y)| ≤ |q y| *
              (K * (Ici (r / 4)).indicator (fun d : ℝ => d ^ (-P.val.2 - 1)) |c - y|) := by
            simpa only [a, div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hb
          exact hb'.trans_eq (by dsimp [U]; rw [hd]; ring))
    rw [Real.norm_eq_abs, integral_const_mul, hUeq] at hn
    exact hn.trans ((mul_le_mul_of_nonneg_left hUb hK.le).trans_eq (by ring))
  exact (abs_add_le _ _).trans ((add_le_add hnearInt hfarInt).trans_eq (by dsimp [C]; ring))

end Riesz1.Internal
