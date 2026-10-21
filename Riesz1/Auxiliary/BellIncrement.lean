/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The averaged increment of a periodic profile

The parts that do not involve the kernel `g`: the
averaged increment `D`, the energy `‖ψ'‖²_{L²(ℓ⁻¹𝕋)}`, and the constant `A = ℓ ‖ψ'‖²`. The
facts proved here are the ones used in the kernel part of Lemma B.1: the bounds
`D(r) ≤ r² ℓ⁻¹ ‖ψ'‖²` and `|D'(r)| ≤ 2 |r| ℓ⁻¹ ‖ψ'‖²`, together with evenness, periodicity and
differentiability of `D`.

The profile `ψ` is a real `C^∞` function on `ℝ` with period `ℓ⁻¹`, as in
`Riesz1/Auxiliary/GradientSplittingDifferences.lean`. The circle `𝕋 = ℝ/ℤ` has length one, so
its integral is the integral over `[0, 1]`. The integrands are one-periodic in `x`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The averaged increment `D(r) = ∫_𝕋 (ψ((x+r)/ℓ) - ψ(x/ℓ))² dx`. -/
noncomputable def bellIncrement (ℓ : ℝ) (ψ : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (ψ ((x + r) / ℓ) - ψ (x / ℓ)) ^ 2

/-- The squared norm `‖ψ'‖²_{L²(ℓ⁻¹𝕋)} = ∫_0^{ℓ⁻¹} ψ'(u)² du`, on the
circle `ℓ⁻¹𝕋`, which has length `ℓ⁻¹`. -/
noncomputable def bellEnergy (ℓ : ℝ) (ψ : ℝ → ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..ℓ⁻¹, (deriv ψ u) ^ 2

/-- The constant `A = ℓ ‖ψ'‖²_{L²(ℓ⁻¹𝕋)}`. -/
noncomputable def bellConstant (ℓ : ℝ) (ψ : ℝ → ℝ) : ℝ :=
  ℓ * bellEnergy ℓ ψ

/-- The derivative `D'(r)` of `bellIncrement`, differentiated under the integral sign. -/
noncomputable def bellIncrementDeriv (ℓ : ℝ) (ψ : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, 2 * (ψ ((x + r) / ℓ) - ψ (x / ℓ)) * (deriv ψ ((x + r) / ℓ) / ℓ)

/-- A continuous real function is bounded on each interval `[-R, R]`. -/
lemma exists_bound_of_abs_le {φ : ℝ → ℝ} (hφ : Continuous φ) (R : ℝ) :
    ∃ M : ℝ, ∀ t : ℝ, |t| ≤ R → |φ t| ≤ M := by
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hφ.continuousOn
  refine ⟨M, fun t ht => ?_⟩
  have h := hM t ⟨(abs_le.mp ht).1, (abs_le.mp ht).2⟩
  simpa [Real.norm_eq_abs] using h

/-- The chain rule for `r ↦ ψ((x + r)/ℓ)`. -/
lemma hasDerivAt_psi_shift {ℓ : ℝ} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (x r : ℝ) : HasDerivAt (fun r : ℝ => ψ ((x + r) / ℓ)) (deriv ψ ((x + r) / ℓ) / ℓ) r := by
  have hd : HasDerivAt ψ (deriv ψ ((x + r) / ℓ)) ((x + r) / ℓ) :=
    ((hψ.differentiable (by simp)) _).hasDerivAt
  have hl : HasDerivAt (fun r : ℝ => (x + r) / ℓ) (1 / ℓ) r :=
    ((hasDerivAt_id' r).const_add x).div_const ℓ
  have e : deriv ψ ((x + r) / ℓ) / ℓ = deriv ψ ((x + r) / ℓ) * (1 / ℓ) := by ring
  rw [e]
  exact HasDerivAt.comp r hd hl

/-- The derivative of the periodic profile `ψ` has the same period. -/
lemma deriv_periodic {ψ : ℝ → ℝ} {c : ℝ} (hper : Function.Periodic ψ c) :
    Function.Periodic (deriv ψ) c := by
  intro y
  have hfun : (fun x => ψ (x + c)) = ψ := funext hper
  have h : deriv (fun x => ψ (x + c)) y = deriv ψ (y + c) := deriv_comp_add_const ψ c y
  rw [hfun] at h
  exact h.symm

/-- Integrals of a one-periodic function over `[0, 1]` do not change under a translation. -/
lemma integral_add_of_periodic {g : ℝ → ℝ} (hg : Function.Periodic g 1) (t : ℝ) :
    ∫ x in (0 : ℝ)..1, g (x + t) = ∫ x in (0 : ℝ)..1, g x := by
  rw [intervalIntegral.integral_comp_add_right g t, zero_add, add_comm 1 t]
  simpa using hg.intervalIntegral_add_eq t 0

/-- The squared slope `(ψ'(x/ℓ)/ℓ)²` of the profile `x ↦ ψ(x/ℓ)` has the integral
`ℓ⁻¹ ‖ψ'‖²_{L²(ℓ⁻¹𝕋)}` over `[0, 1]`. -/
lemma integral_slope_sq {ℓ : ℝ} {ψ : ℝ → ℝ} (hℓ : 0 < ℓ) :
    ∫ x in (0 : ℝ)..1, (deriv ψ (x / ℓ) / ℓ) ^ 2 = ℓ⁻¹ * bellEnergy ℓ ψ := by
  have hpt : (fun x : ℝ => (deriv ψ (x / ℓ) / ℓ) ^ 2) =
      fun x => ℓ⁻¹ ^ 2 * (fun u => (deriv ψ u) ^ 2) (x / ℓ) := by
    funext x
    simp only [div_eq_mul_inv]
    ring
  have hcomp := intervalIntegral.integral_comp_div (a := (0 : ℝ)) (b := 1)
    (fun u => (deriv ψ u) ^ 2) hℓ.ne'
  simp only [zero_div, one_div, smul_eq_mul] at hcomp
  rw [hpt, intervalIntegral.integral_const_mul, hcomp, bellEnergy]
  field_simp

/-- The slope `ψ'((x + t)/ℓ)/ℓ` of the profile has squared integral `ℓ⁻¹ ‖ψ'‖²` over `[0, 1]`,
for every shift `t`. -/
lemma integral_slope_sq_shift {ℓ : ℝ} {ψ : ℝ → ℝ} (hℓ : 0 < ℓ)
    (hper : Function.Periodic ψ ℓ⁻¹) (t : ℝ) :
    ∫ x in (0 : ℝ)..1, (deriv ψ ((x + t) / ℓ) / ℓ) ^ 2 = ℓ⁻¹ * bellEnergy ℓ ψ := by
  have hp : Function.Periodic (fun x : ℝ => (deriv ψ (x / ℓ) / ℓ) ^ 2) 1 := by
    intro x
    simp only
    rw [show (x + 1) / ℓ = x / ℓ + ℓ⁻¹ by ring, deriv_periodic hper (x / ℓ)]
  exact (integral_add_of_periodic hp t).trans (integral_slope_sq hℓ)

/-- The averaged increment is one-periodic in `r`, since `ψ` has period `ℓ⁻¹`. -/
lemma bellIncrement_periodic {ℓ : ℝ} {ψ : ℝ → ℝ} (hper : Function.Periodic ψ ℓ⁻¹) :
    Function.Periodic (bellIncrement ℓ ψ) 1 := by
  intro r
  unfold bellIncrement
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  rw [show (x + (r + 1)) / ℓ = (x + r) / ℓ + ℓ⁻¹ by ring, hper ((x + r) / ℓ)]

/-- The averaged increment is even in `r`: the substitution `x ↦ x + r` swaps the two terms. -/
lemma bellIncrement_neg {ℓ : ℝ} {ψ : ℝ → ℝ} (hper : Function.Periodic ψ ℓ⁻¹) (r : ℝ) :
    bellIncrement ℓ ψ (-r) = bellIncrement ℓ ψ r := by
  have hΦ : Function.Periodic (fun x : ℝ => (ψ ((x + -r) / ℓ) - ψ (x / ℓ)) ^ 2) 1 := by
    intro x
    simp only
    rw [show (x + 1 + -r) / ℓ = (x + -r) / ℓ + ℓ⁻¹ by ring,
      show (x + 1) / ℓ = x / ℓ + ℓ⁻¹ by ring, hper ((x + -r) / ℓ), hper (x / ℓ)]
  have key : ∫ x in (0 : ℝ)..1, (ψ ((x + -r) / ℓ) - ψ (x / ℓ)) ^ 2
      = ∫ x in (0 : ℝ)..1, (ψ ((x + r) / ℓ) - ψ (x / ℓ)) ^ 2 := by
    have h1 := integral_add_of_periodic hΦ r
    rw [← h1]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [show (x + r + -r) / ℓ = x / ℓ by ring]
    ring
  exact key

/-- The derivative of the integrand of `bellIncrement` in `r`. -/
lemma hasDerivAt_bellIncrement_integrand {ℓ : ℝ} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (x r : ℝ) :
    HasDerivAt (fun r : ℝ => (ψ ((x + r) / ℓ) - ψ (x / ℓ)) ^ 2)
      (2 * (ψ ((x + r) / ℓ) - ψ (x / ℓ)) * (deriv ψ ((x + r) / ℓ) / ℓ)) r := by
  have h2 : HasDerivAt (fun r : ℝ => ψ ((x + r) / ℓ) - ψ (x / ℓ))
      (deriv ψ ((x + r) / ℓ) / ℓ) r :=
    HasDerivAt.sub_const (ψ (x / ℓ)) (hasDerivAt_psi_shift hψ x r)
  have h3 : HasDerivAt (fun r : ℝ => (ψ ((x + r) / ℓ) - ψ (x / ℓ)) ^ 2)
      (((2 : ℕ) : ℝ) * (ψ ((x + r) / ℓ) - ψ (x / ℓ)) ^ (2 - 1) * (deriv ψ ((x + r) / ℓ) / ℓ)) r :=
    HasDerivAt.pow h2 2
  convert h3 using 1
  norm_num

/-- The derivative `bellIncrementDeriv` is continuous in `r`. -/
lemma continuous_bellIncrementDeriv {ℓ : ℝ} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    Continuous (bellIncrementDeriv ℓ ψ) := by
  have hc : Continuous ψ := hψ.continuous
  have hd : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  unfold bellIncrementDeriv
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 1
  show Continuous fun p : ℝ × ℝ =>
    2 * (ψ ((p.2 + p.1) / ℓ) - ψ (p.2 / ℓ)) * (deriv ψ ((p.2 + p.1) / ℓ) / ℓ)
  fun_prop

/-- The averaged increment is differentiable in `r`, with derivative `bellIncrementDeriv`. -/
lemma hasDerivAt_bellIncrement {ℓ : ℝ} {ψ : ℝ → ℝ} (hℓ : 0 < ℓ) (hψ : ContDiff ℝ ∞ ψ)
    (r₀ : ℝ) : HasDerivAt (bellIncrement ℓ ψ) (bellIncrementDeriv ℓ ψ r₀) r₀ := by
  have hc : Continuous ψ := hψ.continuous
  have hd : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  set R : ℝ := (|r₀| + 2) / ℓ with hR
  have hR0 : 0 ≤ R := div_nonneg (by positivity) hℓ.le
  obtain ⟨M0, hM0⟩ := exists_bound_of_abs_le hc R
  obtain ⟨M1, hM1⟩ := exists_bound_of_abs_le hd R
  have hM0' : 0 ≤ M0 := le_trans (abs_nonneg _) (hM0 0 (by simpa using hR0))
  have hM1' : 0 ≤ M1 := le_trans (abs_nonneg _) (hM1 0 (by simpa using hR0))
  -- Uniform bound for `r` in the unit ball around `r₀` and `x` in `[0, 1]`.
  have hdiv : ∀ y c : ℝ, |y| ≤ c → |y / ℓ| ≤ c / ℓ := fun y c h => by
    rw [abs_div, abs_of_pos hℓ]
    exact div_le_div_of_nonneg_right h hℓ.le
  have hbnd : ∀ x ∈ Icc (0 : ℝ) 1, ∀ r ∈ Metric.ball r₀ 1,
      ‖2 * (ψ ((x + r) / ℓ) - ψ (x / ℓ)) * (deriv ψ ((x + r) / ℓ) / ℓ)‖
        ≤ 2 * (2 * M0) * (M1 / ℓ) := by
    intro x hx r hr
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hr
    have hxr : |(x + r)| ≤ |r₀| + 2 := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le r₀, hx.1, hx.2, hr.1, hr.2]
      · linarith [le_abs_self r₀, hx.1, hx.2, hr.1, hr.2]
    have hx' : |x| ≤ |r₀| + 2 := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le r₀, hx.1, hx.2, abs_nonneg r₀]
      · linarith [le_abs_self r₀, hx.1, hx.2, abs_nonneg r₀]
    have ha : |ψ ((x + r) / ℓ) - ψ (x / ℓ)| ≤ 2 * M0 := by
      have h1 := hM0 _ (hdiv _ _ hxr)
      have h2 := hM0 _ (hdiv _ _ hx')
      have := abs_sub (ψ ((x + r) / ℓ)) (ψ (x / ℓ))
      linarith
    have hb : |deriv ψ ((x + r) / ℓ) / ℓ| ≤ M1 / ℓ := by
      rw [abs_div, abs_of_pos hℓ]
      exact div_le_div_of_nonneg_right (hM1 _ (hdiv _ _ hxr)) hℓ.le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
    have hb0 : 0 ≤ |deriv ψ ((x + r) / ℓ) / ℓ| := abs_nonneg _
    have ha0 : 0 ≤ |ψ ((x + r) / ℓ) - ψ (x / ℓ)| := abs_nonneg _
    have hM1ℓ : 0 ≤ M1 / ℓ := div_nonneg hM1' hℓ.le
    calc 2 * |ψ ((x + r) / ℓ) - ψ (x / ℓ)| * |deriv ψ ((x + r) / ℓ) / ℓ|
        ≤ 2 * (2 * M0) * |deriv ψ ((x + r) / ℓ) / ℓ| := by
          gcongr
      _ ≤ 2 * (2 * M0) * (M1 / ℓ) := by gcongr
  have hF_int : IntervalIntegrable
      (fun x : ℝ => (ψ ((x + r₀) / ℓ) - ψ (x / ℓ)) ^ 2) volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ => (ψ ((x + r₀) / ℓ) - ψ (x / ℓ)) ^ 2).intervalIntegrable _ _
  have hF'_meas : AEStronglyMeasurable
      (fun x : ℝ => 2 * (ψ ((x + r₀) / ℓ) - ψ (x / ℓ)) * (deriv ψ ((x + r₀) / ℓ) / ℓ))
      (volume.restrict (uIoc (0 : ℝ) 1)) :=
    (by fun_prop : Continuous fun x : ℝ =>
      2 * (ψ ((x + r₀) / ℓ) - ψ (x / ℓ)) * (deriv ψ ((x + r₀) / ℓ) / ℓ)).aestronglyMeasurable
  have hF_meas : ∀ᶠ r in 𝓝 r₀, AEStronglyMeasurable
      (fun x : ℝ => (ψ ((x + r) / ℓ) - ψ (x / ℓ)) ^ 2) (volume.restrict (uIoc (0 : ℝ) 1)) :=
    Eventually.of_forall fun r => (by fun_prop : Continuous fun x : ℝ =>
      (ψ ((x + r) / ℓ) - ψ (x / ℓ)) ^ 2).aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIoc (0 : ℝ) 1 → ∀ r ∈ Metric.ball r₀ 1,
      ‖2 * (ψ ((t + r) / ℓ) - ψ (t / ℓ)) * (deriv ψ ((t + r) / ℓ) / ℓ)‖
        ≤ (fun _ : ℝ => 2 * (2 * M0) * (M1 / ℓ)) t := by
    refine Eventually.of_forall (fun t ht r hr => ?_)
    rw [uIoc_of_le zero_le_one] at ht
    exact hbnd t (Ioc_subset_Icc_self ht) r hr
  have h_diff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIoc (0 : ℝ) 1 → ∀ r ∈ Metric.ball r₀ 1,
      HasDerivAt (fun r : ℝ => (ψ ((t + r) / ℓ) - ψ (t / ℓ)) ^ 2)
        (2 * (ψ ((t + r) / ℓ) - ψ (t / ℓ)) * (deriv ψ ((t + r) / ℓ) / ℓ)) r :=
    Eventually.of_forall (fun t _ r _ => hasDerivAt_bellIncrement_integrand hψ t r)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := fun r x => (ψ ((x + r) / ℓ) - ψ (x / ℓ)) ^ 2)
    (F' := fun r x => 2 * (ψ ((x + r) / ℓ) - ψ (x / ℓ)) * (deriv ψ ((x + r) / ℓ) / ℓ))
    (x₀ := r₀) (s := Metric.ball r₀ 1) (bound := fun _ : ℝ => 2 * (2 * M0) * (M1 / ℓ))
    (a := 0) (b := 1) (Metric.ball_mem_nhds r₀ one_pos) hF_meas hF_int hF'_meas h_bound
    intervalIntegrable_const h_diff
  exact key.2

lemma deriv_bellIncrement {ℓ : ℝ} {ψ : ℝ → ℝ} (hℓ : 0 < ℓ) (hψ : ContDiff ℝ ∞ ψ) (r : ℝ) :
    deriv (bellIncrement ℓ ψ) r = bellIncrementDeriv ℓ ψ r :=
  (hasDerivAt_bellIncrement hℓ hψ r).deriv

/-- The averaged increment is continuous. -/
lemma continuous_bellIncrement {ℓ : ℝ} {ψ : ℝ → ℝ} (hℓ : 0 < ℓ) (hψ : ContDiff ℝ ∞ ψ) :
    Continuous (bellIncrement ℓ ψ) :=
  continuous_iff_continuousAt.2 fun r => (hasDerivAt_bellIncrement hℓ hψ r).continuousAt

/-- Cauchy–Schwarz on a segment starting at `0`: `(∫_0^r g)² ≤ r ∫_0^r g²`. -/
lemma sq_integral_le_mul_integral {g : ℝ → ℝ} (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r) :
    (∫ t in (0 : ℝ)..r, g t) ^ 2 ≤ r * ∫ t in (0 : ℝ)..r, g t ^ 2 := by
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0
    simp
  set I := ∫ t in (0 : ℝ)..r, g t with hI
  set J := ∫ t in (0 : ℝ)..r, g t ^ 2 with hJ
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..r, (g t - I / r) ^ 2 :=
    intervalIntegral.integral_nonneg hpos.le (fun t _ => sq_nonneg _)
  have hc1 : Continuous fun t => g t ^ 2 := by fun_prop
  have hc2 : Continuous fun t => 2 * (I / r) * g t := by fun_prop
  have hexp : ∫ t in (0 : ℝ)..r, (g t - I / r) ^ 2 = J - I ^ 2 / r := by
    have h : ∀ t, (g t - I / r) ^ 2 = (g t ^ 2 - 2 * (I / r) * g t) + (I / r) ^ 2 :=
      fun t => by ring
    have hi1 : IntervalIntegrable (fun t => g t ^ 2 - 2 * (I / r) * g t) volume 0 r :=
      (hc1.sub hc2).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun t => g t ^ 2) volume 0 r := hc1.intervalIntegrable _ _
    have hi3 : IntervalIntegrable (fun t => 2 * (I / r) * g t) volume 0 r :=
      hc2.intervalIntegrable _ _
    simp_rw [h]
    rw [intervalIntegral.integral_add hi1 (intervalIntegrable_const),
      intervalIntegral.integral_sub hi2 hi3, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero]
    field_simp
    ring
  rw [hexp] at hnn
  have h2 : I ^ 2 / r ≤ J := by linarith
  rw [div_le_iff₀ hpos] at h2
  linarith

/-- Fubini on the rectangle `[0, 1] × [0, r]` for a jointly continuous integrand. -/
lemma integral_integral_swap_unit {F : ℝ → ℝ → ℝ} (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    {r : ℝ} (hr : 0 ≤ r) :
    ∫ x in (0 : ℝ)..1, ∫ t in (0 : ℝ)..r, F x t = ∫ t in (0 : ℝ)..r, ∫ x in (0 : ℝ)..1, F x t := by
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) r))) := by
    rw [Measure.prod_restrict, uIoc_of_le zero_le_one]
    exact (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hswap := intervalIntegral_integral_swap (a := 0) (b := 1) (f := F)
    (μ := volume.restrict (Ioc (0 : ℝ) r)) hint
  simpa only [intervalIntegral.integral_of_le hr] using hswap

/-- The averaged increment is bounded by `r² ℓ⁻¹ ‖ψ'‖²` for `r ≥ 0`. -/
lemma bellIncrement_le_of_nonneg {ℓ : ℝ} {ψ : ℝ → ℝ} (hℓ : 0 < ℓ) (hψ : ContDiff ℝ ∞ ψ)
    (hper : Function.Periodic ψ ℓ⁻¹) {r : ℝ} (hr : 0 ≤ r) :
    bellIncrement ℓ ψ r ≤ r ^ 2 * ℓ⁻¹ * bellEnergy ℓ ψ := by
  have hd : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hslope : Continuous fun p : ℝ × ℝ => (deriv ψ ((p.1 + p.2) / ℓ) / ℓ) ^ 2 := by
    fun_prop
  -- Fundamental theorem of calculus in `r`, for each fixed `x`.
  have hftc : ∀ x : ℝ, ψ ((x + r) / ℓ) - ψ (x / ℓ)
      = ∫ t in (0 : ℝ)..r, deriv ψ ((x + t) / ℓ) / ℓ := by
    intro x
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => ψ ((x + t) / ℓ)) (f' := fun t : ℝ => deriv ψ ((x + t) / ℓ) / ℓ)
      (a := 0) (b := r) (fun t _ => hasDerivAt_psi_shift hψ x t)
      ((by fun_prop : Continuous fun t : ℝ => deriv ψ ((x + t) / ℓ) / ℓ).intervalIntegrable _ _)
    simp only [add_zero] at h
    exact h.symm
  have hD : bellIncrement ℓ ψ r
      = ∫ x in (0 : ℝ)..1, (∫ t in (0 : ℝ)..r, deriv ψ ((x + t) / ℓ) / ℓ) ^ 2 := by
    unfold bellIncrement
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [hftc x]
  have hcont1 : Continuous fun x : ℝ => ∫ t in (0 : ℝ)..r, deriv ψ ((x + t) / ℓ) / ℓ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x t => deriv ψ ((x + t) / ℓ) / ℓ)
      (by fun_prop : Continuous fun p : ℝ × ℝ => deriv ψ ((p.1 + p.2) / ℓ) / ℓ) 0 r
  have hcont2 : Continuous fun x : ℝ => r * ∫ t in (0 : ℝ)..r, (deriv ψ ((x + t) / ℓ) / ℓ) ^ 2 :=
    continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun x t => (deriv ψ ((x + t) / ℓ) / ℓ) ^ 2) hslope 0 r)
  have hle : ∫ x in (0 : ℝ)..1, (∫ t in (0 : ℝ)..r, deriv ψ ((x + t) / ℓ) / ℓ) ^ 2
      ≤ ∫ x in (0 : ℝ)..1, r * ∫ t in (0 : ℝ)..r, (deriv ψ ((x + t) / ℓ) / ℓ) ^ 2 := by
    have hi1 : IntervalIntegrable (fun x : ℝ => (∫ t in (0 : ℝ)..r, deriv ψ ((x + t) / ℓ) / ℓ) ^ 2)
        volume 0 1 := (hcont1.pow 2).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun x : ℝ => r * ∫ t in (0 : ℝ)..r,
        (deriv ψ ((x + t) / ℓ) / ℓ) ^ 2) volume 0 1 := hcont2.intervalIntegrable _ _
    refine intervalIntegral.integral_mono_on zero_le_one hi1 hi2 (fun x _ => ?_)
    exact sq_integral_le_mul_integral (by fun_prop) hr
  have hswap := integral_integral_swap_unit
    (F := fun x t => (deriv ψ ((x + t) / ℓ) / ℓ) ^ 2) hslope hr
  calc bellIncrement ℓ ψ r
      = ∫ x in (0 : ℝ)..1, (∫ t in (0 : ℝ)..r, deriv ψ ((x + t) / ℓ) / ℓ) ^ 2 := hD
    _ ≤ ∫ x in (0 : ℝ)..1, r * ∫ t in (0 : ℝ)..r, (deriv ψ ((x + t) / ℓ) / ℓ) ^ 2 := hle
    _ = r * ∫ x in (0 : ℝ)..1, ∫ t in (0 : ℝ)..r, (deriv ψ ((x + t) / ℓ) / ℓ) ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ = r * ∫ t in (0 : ℝ)..r, ∫ x in (0 : ℝ)..1, (deriv ψ ((x + t) / ℓ) / ℓ) ^ 2 := by
        rw [hswap]
    _ = r * ∫ t in (0 : ℝ)..r, ℓ⁻¹ * bellEnergy ℓ ψ := by
        congr 1
        exact intervalIntegral.integral_congr (fun t _ => integral_slope_sq_shift hℓ hper t)
    _ = r * (r * (ℓ⁻¹ * bellEnergy ℓ ψ)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    _ = r ^ 2 * ℓ⁻¹ * bellEnergy ℓ ψ := by ring

/-- The averaged increment is bounded by `r² ℓ⁻¹ ‖ψ'‖²` for every real `r`. -/
lemma bellIncrement_le {ℓ : ℝ} {ψ : ℝ → ℝ} (hℓ : 0 < ℓ) (hψ : ContDiff ℝ ∞ ψ)
    (hper : Function.Periodic ψ ℓ⁻¹) (r : ℝ) :
    bellIncrement ℓ ψ r ≤ r ^ 2 * ℓ⁻¹ * bellEnergy ℓ ψ := by
  rcases le_total 0 r with hr | hr
  · exact bellIncrement_le_of_nonneg hℓ hψ hper hr
  · rw [← bellIncrement_neg hper r]
    have h := bellIncrement_le_of_nonneg hℓ hψ hper (neg_nonneg.mpr hr)
    rwa [neg_sq] at h

/-- The derivative part of Lemma B.1: `|D'(r)| ≤ 2 |r| ℓ⁻¹ ‖ψ'‖²`. -/
lemma abs_bellIncrementDeriv_le {ℓ : ℝ} {ψ : ℝ → ℝ} (hℓ : 0 < ℓ) (hψ : ContDiff ℝ ∞ ψ)
    (hper : Function.Periodic ψ ℓ⁻¹) (r : ℝ) :
    |bellIncrementDeriv ℓ ψ r| ≤ 2 * |r| * ℓ⁻¹ * bellEnergy ℓ ψ := by
  rcases eq_or_ne r 0 with rfl | hr0
  · simp [bellIncrementDeriv]
  have hc : Continuous ψ := hψ.continuous
  have hd : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have habs : 0 < |r| := abs_pos.mpr hr0
  set μ : ℝ := 1 / |r| with hμ
  have hμpos : 0 < μ := by positivity
  -- Pointwise: `|2 u v| ≤ μ u² + v²/μ`, from the squares `(μ u ∓ v)² ≥ 0`.
  have hpt : ∀ u v : ℝ, |2 * u * v| ≤ μ * u ^ 2 + v ^ 2 / μ := by
    intro u v
    have h1 : 0 ≤ (μ * u - v) ^ 2 / μ := div_nonneg (sq_nonneg _) hμpos.le
    have h2 : 0 ≤ (μ * u + v) ^ 2 / μ := div_nonneg (sq_nonneg _) hμpos.le
    have k1 : μ * u ^ 2 + v ^ 2 / μ - 2 * u * v = (μ * u - v) ^ 2 / μ := by
      field_simp
      ring
    have k2 : μ * u ^ 2 + v ^ 2 / μ + 2 * u * v = (μ * u + v) ^ 2 / μ := by
      field_simp
      ring
    rw [abs_le]
    constructor <;> linarith
  have hfun_cont : Continuous fun x : ℝ => ψ ((x + r) / ℓ) - ψ (x / ℓ) := by fun_prop
  have hslope_cont : Continuous fun x : ℝ => deriv ψ ((x + r) / ℓ) / ℓ := by fun_prop
  have hint_eq : ∫ x in (0 : ℝ)..1, (deriv ψ ((x + r) / ℓ) / ℓ) ^ 2 = ℓ⁻¹ * bellEnergy ℓ ψ :=
    integral_slope_sq_shift hℓ hper r
  have hle_abs : ∫ x in (0 : ℝ)..1, |2 * (ψ ((x + r) / ℓ) - ψ (x / ℓ)) * (deriv ψ ((x + r) / ℓ) / ℓ)|
      ≤ ∫ x in (0 : ℝ)..1, (μ * (ψ ((x + r) / ℓ) - ψ (x / ℓ)) ^ 2
        + (deriv ψ ((x + r) / ℓ) / ℓ) ^ 2 / μ) := by
    have hc3 : Continuous fun x : ℝ =>
        |2 * (ψ ((x + r) / ℓ) - ψ (x / ℓ)) * (deriv ψ ((x + r) / ℓ) / ℓ)| := by fun_prop
    have hc4 : Continuous fun x : ℝ =>
        μ * (ψ ((x + r) / ℓ) - ψ (x / ℓ)) ^ 2 + (deriv ψ ((x + r) / ℓ) / ℓ) ^ 2 / μ := by
      fun_prop
    refine intervalIntegral.integral_mono_on zero_le_one (hc3.intervalIntegrable _ _)
      (hc4.intervalIntegrable _ _) (fun x _ => hpt _ _)
  have hsplit : ∫ x in (0 : ℝ)..1, (μ * (ψ ((x + r) / ℓ) - ψ (x / ℓ)) ^ 2
        + (deriv ψ ((x + r) / ℓ) / ℓ) ^ 2 / μ)
      = μ * bellIncrement ℓ ψ r + (ℓ⁻¹ * bellEnergy ℓ ψ) / μ := by
    have hi1 : IntervalIntegrable (fun x : ℝ => μ * (ψ ((x + r) / ℓ) - ψ (x / ℓ)) ^ 2)
        volume 0 1 := by
      apply Continuous.intervalIntegrable; fun_prop
    have hi2 : IntervalIntegrable (fun x : ℝ => (deriv ψ ((x + r) / ℓ) / ℓ) ^ 2 / μ)
        volume 0 1 := by
      apply Continuous.intervalIntegrable; fun_prop
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_div, hint_eq]
    rfl
  have hD := bellIncrement_le hℓ hψ hper r
  have hbound : μ * bellIncrement ℓ ψ r + (ℓ⁻¹ * bellEnergy ℓ ψ) / μ
      ≤ 2 * |r| * ℓ⁻¹ * bellEnergy ℓ ψ := by
    have hμr : μ * (r ^ 2 * ℓ⁻¹ * bellEnergy ℓ ψ) = |r| * ℓ⁻¹ * bellEnergy ℓ ψ := by
      rw [hμ, ← sq_abs]
      field_simp
    have hdiv : (ℓ⁻¹ * bellEnergy ℓ ψ) / μ = |r| * (ℓ⁻¹ * bellEnergy ℓ ψ) := by
      rw [hμ]
      field_simp
    have hmono := mul_le_mul_of_nonneg_left hD hμpos.le
    nlinarith [hmono, hμr, hdiv]
  have hfinal : bellIncrementDeriv ℓ ψ r
      = ∫ x in (0 : ℝ)..1, 2 * (ψ ((x + r) / ℓ) - ψ (x / ℓ)) * (deriv ψ ((x + r) / ℓ) / ℓ) := rfl
  rw [hfinal]
  calc |∫ x in (0 : ℝ)..1, 2 * (ψ ((x + r) / ℓ) - ψ (x / ℓ)) * (deriv ψ ((x + r) / ℓ) / ℓ)|
      ≤ ∫ x in (0 : ℝ)..1, |2 * (ψ ((x + r) / ℓ) - ψ (x / ℓ)) * (deriv ψ ((x + r) / ℓ) / ℓ)| :=
        intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ _ := hle_abs
    _ = μ * bellIncrement ℓ ψ r + (ℓ⁻¹ * bellEnergy ℓ ψ) / μ := hsplit
    _ ≤ 2 * |r| * ℓ⁻¹ * bellEnergy ℓ ψ := hbound

/-- The derivative part of Lemma B.1, stated for the derivative of `bellIncrement`. -/
lemma abs_deriv_bellIncrement_le {ℓ : ℝ} {ψ : ℝ → ℝ} (hℓ : 0 < ℓ) (hψ : ContDiff ℝ ∞ ψ)
    (hper : Function.Periodic ψ ℓ⁻¹) (r : ℝ) :
    |deriv (bellIncrement ℓ ψ) r| ≤ 2 * |r| * ℓ⁻¹ * bellEnergy ℓ ψ := by
  rw [deriv_bellIncrement hℓ hψ r]
  exact abs_bellIncrementDeriv_le hℓ hψ hper r

end Riesz1

end
