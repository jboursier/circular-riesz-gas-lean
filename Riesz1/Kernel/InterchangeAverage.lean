/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.InterchangeGamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic

/-!
# Averages of Gaussians over one period

For an integer `k` and a time `t`, the average of the Gaussian `exp(-(y - k)^2 / (4t))` over
`y ∈ [0, 1]` is the second term of the integrand `u_k^x(t)` in the proof of Lemma 2.1.
This file proves its elementary bounds, the integrability of
`t ^ (-1 - α)` times this average on `(0, ∞)`, and the Fubini identity
`∫_{(0,∞)} t^{-1-α} ∫_0^1 e^{-(y-k)^2/(4t)} dy dt = Γ(α) ∫_0^1 ((y-k)^2/4)^{-α} dy`
for `0 < α < 1/2`.

Main results:
* `Riesz1.gaussAverage_le_sqrt`, `Riesz1.gaussAverage_le_one`: the uniform bounds `0 ≤ A ≤ √(4πt)`
  and `A ≤ 1`.
* `Riesz1.integrableOn_rpow_mul_gaussAverage`: the integrability of `t ^ (-1 - α) A_k(t)`.
* `Riesz1.integral_rpow_mul_gaussAverage`: the Fubini identity.
-/

public section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- The average over one period `[0, 1]` of the Gaussian `exp(-(y - k)^2 / (4t))` centered at the
integer `k`. Its values at `t ≤ 0` are never used,
because every time integral in this development is over `(0, ∞)`. -/
@[expose] noncomputable def gaussAverage (k : ℤ) (t : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, Real.exp (-(y - k) ^ 2 / (4 * t))

/-- The average of a Gaussian is nonnegative. -/
lemma gaussAverage_nonneg (k : ℤ) (t : ℝ) : 0 ≤ gaussAverage k t :=
  intervalIntegral.integral_nonneg zero_le_one fun _ _ => (Real.exp_pos _).le

/-- The Gaussian centered at `k` is continuous in `y`. -/
lemma continuous_gauss_shift (k : ℤ) (t : ℝ) :
    Continuous fun y : ℝ => Real.exp (-(y - k) ^ 2 / (4 * t)) := by
  fun_prop

/-- The Gaussian centered at `k` is integrable on `ℝ` for `t > 0`. -/
lemma integrable_gauss_shift (k : ℤ) {t : ℝ} (ht : 0 < t) :
    Integrable fun y : ℝ => Real.exp (-(y - k) ^ 2 / (4 * t)) := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / (4 * t)) (by positivity)).comp_sub_right (k : ℝ)
  refine h.congr (Eventually.of_forall fun y => ?_)
  show Real.exp (-(1 / (4 * t)) * (y - k) ^ 2) = Real.exp (-(y - k) ^ 2 / (4 * t))
  congr 1
  ring

/-- The whole-line integral of the centered Gaussian is `√(4πt)`, the normalization of the heat
kernel in equation (2.7). -/
lemma integral_gauss_shift (k : ℤ) {t : ℝ} (ht : 0 < t) :
    ∫ y : ℝ, Real.exp (-(y - k) ^ 2 / (4 * t)) = Real.sqrt (4 * Real.pi * t) := by
  calc ∫ y : ℝ, Real.exp (-(y - k) ^ 2 / (4 * t))
      = ∫ y : ℝ, Real.exp (-(1 / (4 * t)) * (y - k) ^ 2) := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        show Real.exp (-(y - k) ^ 2 / (4 * t)) = Real.exp (-(1 / (4 * t)) * (y - k) ^ 2)
        congr 1
        ring
    _ = ∫ y : ℝ, Real.exp (-(1 / (4 * t)) * y ^ 2) :=
        integral_sub_right_eq_self (fun y : ℝ => Real.exp (-(1 / (4 * t)) * y ^ 2)) (k : ℝ)
    _ = Real.sqrt (Real.pi / (1 / (4 * t))) := integral_gaussian _
    _ = Real.sqrt (4 * Real.pi * t) := by
        congr 1
        field_simp

/-- The average of a Gaussian over `[0, 1]` is at most the whole-line integral `√(4πt)`. -/
lemma gaussAverage_le_sqrt (k : ℤ) {t : ℝ} (ht : 0 < t) :
    gaussAverage k t ≤ Real.sqrt (4 * Real.pi * t) := by
  rw [← integral_gauss_shift k ht]
  unfold gaussAverage
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact setIntegral_le_integral (integrable_gauss_shift k ht)
    (Eventually.of_forall fun y => (Real.exp_pos _).le)

/-- The average of a Gaussian over `[0, 1]` is at most one. -/
lemma gaussAverage_le_one (k : ℤ) {t : ℝ} (ht : 0 < t) : gaussAverage k t ≤ 1 := by
  unfold gaussAverage
  have hle : ∀ y ∈ Icc (0 : ℝ) 1, Real.exp (-(y - k) ^ 2 / (4 * t)) ≤ 1 := fun y _ =>
    Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _))
      (by positivity))
  have h := intervalIntegral.integral_mono_on (f := fun y : ℝ => Real.exp (-(y - k) ^ 2 / (4 * t)))
    (g := fun _ => (1 : ℝ)) zero_le_one ((continuous_gauss_shift k t).intervalIntegrable 0 1)
    (intervalIntegrable_const (μ := volume)) hle
  simpa using h

/-- The Gaussian average is strongly measurable in `t` on `(0, ∞)`, as a parametric integral of a
jointly measurable function. -/
lemma aestronglyMeasurable_gaussAverage (k : ℤ) :
    AEStronglyMeasurable (fun t : ℝ => gaussAverage k t) (volume.restrict (Ioi 0)) := by
  have hmeas : Measurable fun p : ℝ × ℝ => Real.exp (-(p.2 - k) ^ 2 / (4 * p.1)) := by
    fun_prop
  have hm : StronglyMeasurable fun t : ℝ => ∫ y in Ioc (0 : ℝ) 1,
      Real.exp (-(y - k) ^ 2 / (4 * t)) :=
    StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))
      (f := fun p : ℝ × ℝ => Real.exp (-(p.2 - k) ^ 2 / (4 * p.1))) hmeas.stronglyMeasurable
  have e : (fun t : ℝ => gaussAverage k t) =
      fun t : ℝ => ∫ y in Ioc (0 : ℝ) 1, Real.exp (-(y - k) ^ 2 / (4 * t)) := by
    funext t
    unfold gaussAverage
    rw [intervalIntegral.integral_of_le zero_le_one]
  rw [e]
  exact hm.aestronglyMeasurable

/-- The product `t ^ (-1 - α) A_k(t)` is integrable on `(0, ∞)` for `0 < α < 1/2`. Near zero the
average is at most `√(4πt)`, and at infinity it is at most one. -/
lemma integrableOn_rpow_mul_gaussAverage {α : ℝ} (hα : 0 < α) (hα1 : α < 1 / 2) (k : ℤ) :
    IntegrableOn (fun t : ℝ => t ^ (-1 - α) * gaussAverage k t) (Ioi 0) := by
  have hA := aestronglyMeasurable_gaussAverage k
  have hpow : Measurable fun t : ℝ => t ^ (-1 - α) := measurable_id.pow_const _
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · -- Near zero: the average is at most `√(4π) t^{1/2}`.
    have hb : IntegrableOn (fun t : ℝ => Real.sqrt (4 * Real.pi) * t ^ (-1 / 2 - α)) (Ioc 0 1) := by
      have h1 : IntervalIntegrable (fun t : ℝ => t ^ (-1 / 2 - α)) volume 0 1 :=
        intervalIntegral.intervalIntegrable_rpow' (by linarith)
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 h1).const_mul _
    refine Integrable.mono' hb
      ((hpow.aestronglyMeasurable.mul (hA.mono_set Ioc_subset_Ioi_self))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : (0 : ℝ) < t := ht.1
    have hnn : 0 ≤ t ^ (-1 - α) * gaussAverage k t :=
      mul_nonneg (Real.rpow_nonneg ht0.le _) (gaussAverage_nonneg k t)
    rw [Real.norm_of_nonneg hnn]
    calc t ^ (-1 - α) * gaussAverage k t
        ≤ t ^ (-1 - α) * Real.sqrt (4 * Real.pi * t) :=
          mul_le_mul_of_nonneg_left (gaussAverage_le_sqrt k ht0) (Real.rpow_nonneg ht0.le _)
      _ = Real.sqrt (4 * Real.pi) * t ^ (-1 / 2 - α) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow t,
            show (-1 / 2 - α) = (-1 - α) + 1 / 2 by ring, Real.rpow_add ht0]
          ring
  · -- At infinity: the average is at most one.
    have hb : IntegrableOn (fun t : ℝ => t ^ (-1 - α)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine Integrable.mono' hb
      ((hpow.aestronglyMeasurable.mul (hA.mono_set (Ioi_subset_Ioi zero_le_one)))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht1
    have hnn : 0 ≤ t ^ (-1 - α) * gaussAverage k t :=
      mul_nonneg (Real.rpow_nonneg ht0.le _) (gaussAverage_nonneg k t)
    rw [Real.norm_of_nonneg hnn]
    calc t ^ (-1 - α) * gaussAverage k t ≤ t ^ (-1 - α) * 1 :=
          mul_le_mul_of_nonneg_left (gaussAverage_le_one k ht0) (Real.rpow_nonneg ht0.le _)
      _ = t ^ (-1 - α) := mul_one _

/-- The Fubini identity for the averaged Gaussian against a power of `t`, for `0 < α < 1/2`:
`∫_{(0,∞)} t^{-1-α} A_k(t) dt = Γ(α) ∫_0^1 ((y-k)^2/4)^{-α} dy`. The inner `t`-integral is the
reciprocal-time Gamma integral, which holds for every `y ≠ k`. -/
lemma integral_rpow_mul_gaussAverage {α : ℝ} (hα : 0 < α) (hα1 : α < 1 / 2) (k : ℤ) :
    ∫ t in Ioi (0 : ℝ), t ^ (-1 - α) * gaussAverage k t =
      Real.Gamma α * ∫ y in (0 : ℝ)..1, ((y - k) ^ 2 / 4) ^ (-α) := by
  set μ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set ν := volume.restrict (Ioc (0 : ℝ) 1) with hν
  let F : ℝ → ℝ → ℝ := fun t y => t ^ (-1 - α) * Real.exp (-(y - k) ^ 2 / (4 * t))
  -- Pulling the constant `t^{-1-α}` inside the `y`-integral.
  have hpull : ∀ t : ℝ, t ^ (-1 - α) * gaussAverage k t = ∫ y in Ioc (0 : ℝ) 1, F t y := by
    intro t
    unfold gaussAverage
    rw [intervalIntegral.integral_of_le zero_le_one, integral_const_mul]
  have hmeasF : Measurable (Function.uncurry F) := by
    simp only [F, Function.uncurry_def]
    fun_prop
  have hnonneg : ∀ t : ℝ, 0 < t → ∀ y : ℝ, 0 ≤ F t y := fun t ht y =>
    mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
  have hint : Integrable (Function.uncurry F) (μ.prod ν) := by
    rw [integrable_prod_iff hmeasF.aestronglyMeasurable]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hc : Continuous fun y : ℝ => F t y := by
        simp only [F]
        fun_prop
      exact (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    · have hcongr : (fun t : ℝ => ∫ y, ‖F t y‖ ∂ν) =ᵐ[μ]
          fun t : ℝ => t ^ (-1 - α) * gaussAverage k t := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : (0 : ℝ) < t := ht
        have hn : ∀ y : ℝ, ‖F t y‖ = F t y := fun y =>
          Real.norm_of_nonneg (hnonneg t ht0 y)
        simp only [hn]
        rw [hpull t]
      exact (integrableOn_rpow_mul_gaussAverage hα hα1 k).congr hcongr.symm
  have hswap := integral_integral_swap (μ := μ) (ν := ν) hint
  -- The left side of the swapped identity is the target integral.
  have hL : ∫ t in Ioi (0 : ℝ), t ^ (-1 - α) * gaussAverage k t =
      ∫ t, ∫ y, F t y ∂ν ∂μ := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    exact hpull t
  -- The inner `t`-integral is the reciprocal-time Gamma integral for every `y ≠ k`.
  have hR : ∫ y, ∫ t, F t y ∂μ ∂ν =
      ∫ y, Real.Gamma α * ((y - k) ^ 2 / 4) ^ (-α) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc, (volume.restrict (Ioc (0 : ℝ) 1)).ae_ne k]
      with y hy hyk
    have hpos : 0 < (y - k) ^ 2 / 4 := by
      have : y - k ≠ 0 := sub_ne_zero.2 hyk
      positivity
    have he : ∀ t : ℝ, F t y = t ^ (-1 - α) * Real.exp (-((y - k) ^ 2 / 4) / t) := by
      intro t
      simp only [F]
      congr 2
      ring
    simp only [he]
    exact (integral_rpow_neg_exp_div_Ioi hα hpos).trans (mul_comm _ _)
  rw [hL, hswap, hR, integral_const_mul, intervalIntegral.integral_of_le zero_le_one]

end Riesz1
