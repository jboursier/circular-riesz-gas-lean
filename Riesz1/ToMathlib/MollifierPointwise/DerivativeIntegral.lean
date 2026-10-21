/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.Derivative

/-!
# The integral of the circle regularization over one period

The regularization `f_h` has the same integral as `f` over one period. This file proves `Riesz1.integral_circleMollify`:
`∫_{-L/2}^{L/2} f_h = ∫_{-L/2}^{L/2} f` for every mollifier `ρ`, length `L > 0`, scale `h > 0` and
locally integrable `L`-periodic `f`.

The proof writes `f_h(x) = ∫ f(x - u) ρ_h(u) du`, exchanges the order of integration over one period
(Fubini), and uses that the integral of `f(· - u)` over one period does not depend on `u`.
-/

public section

open MeasureTheory Set intervalIntegral

namespace Riesz1

/-- The integrand `(x, u) ↦ f(x - u) κ(u)` is integrable on `I × ℝ` for an interval `I`. -/
lemma integrable_prod_sub_mul {f κ : ℝ → ℝ} {a b : ℝ} (hf : LocallyIntegrable f volume)
    (hκ : Continuous κ) (hκc : HasCompactSupport κ) :
    Integrable (fun p : ℝ × ℝ => f (p.1 - p.2) * κ p.2) ((volume.restrict (Ioc a b)).prod volume) := by
  obtain ⟨R, hR⟩ := exists_radius_of_hasCompactSupport hκc
  set I0 : Set ℝ := Icc (a - R - 1) (b + R + 1) with hI0
  have hF0 : Integrable (I0.indicator f) := (integrable_indicator_iff measurableSet_Icc).2
    (hf.integrableOn_isCompact isCompact_Icc)
  have hκi : Integrable κ := hκ.integrable_of_hasCompactSupport hκc
  have hconv := Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hκi hF0
  have hprod : (volume.restrict (Ioc a b)).prod (volume : Measure ℝ) =
      (volume.prod volume).restrict (Ioc a b ×ˢ univ) := by
    calc (volume.restrict (Ioc a b)).prod (volume : Measure ℝ)
        = (volume.restrict (Ioc a b)).prod (volume.restrict univ) := by rw [Measure.restrict_univ]
      _ = (volume.prod volume).restrict (Ioc a b ×ˢ univ) := Measure.prod_restrict _ _
  rw [hprod]
  refine (hconv.integrableOn).congr_fun (fun p hp => ?_) (measurableSet_Ioc.prod MeasurableSet.univ)
  obtain ⟨hp1, -⟩ := hp
  simp only [ContinuousLinearMap.mul_apply']
  by_cases hk : κ p.2 = 0
  · simp [hk]
  · have hp2 : |p.2| < R := by
      by_contra hc
      exact hk (hR p.2 (not_lt.mp hc))
    have hmem : p.1 - p.2 ∈ I0 := by
      rw [hI0, Set.mem_Icc]
      have h1 := abs_lt.mp hp2
      have hp1' := Set.mem_Ioc.mp hp1
      constructor <;> linarith [h1.1, h1.2, hp1'.1, hp1'.2]
    rw [Set.indicator_of_mem hmem, mul_comm]

/-- The integral of `f(· - u)` over one period is independent of the shift `u`, for `L`-periodic `f`. -/
lemma integral_Ioc_sub_shift {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hper : Function.Periodic f L)
    (u : ℝ) :
    ∫ x in Ioc (-(L / 2)) (L / 2), f (x - u) = ∫ x in Ioc (-(L / 2)) (L / 2), f x := by
  rw [← intervalIntegral.integral_of_le (by linarith), ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_sub_right f u]
  have h1 := hper.intervalIntegral_add_eq (-(L / 2) - u) (-(L / 2))
  rw [show -(L / 2) - u + L = L / 2 - u by ring, show -(L / 2) + L = L / 2 by ring] at h1
  exact h1

/-- **Integral over one period.** For a mollifier `ρ`, a length `L > 0`, a scale `h > 0` and a
locally integrable `L`-periodic `f`, the regularization `f_h` has the same integral as `f` over
`[-L/2, L/2]`. -/
theorem integral_circleMollify {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {L h : ℝ} (hL : 0 < L) (hh : 0 < h)
    {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (hper : Function.Periodic f L) :
    ∫ x in (-(L / 2))..(L / 2), circleMollify ρ L h f x =
      ∫ x in (-(L / 2))..(L / 2), f x := by
  have hκc := hasCompactSupport_scaledMollifier hρ hh
  have hκ : Continuous (scaledMollifier ρ h) := (contDiff_scaledMollifier hρ (h := h)).continuous
  -- Rewrite `f_h(x)` as `∫ f(x - u) ρ_h(u) du`, using the substitution `y = x - u`.
  have hcv : ∀ x : ℝ, circleMollify ρ L h f x = ∫ u, f (x - u) * scaledMollifier ρ h u := by
    intro x
    rw [circleMollify_fun_eq hρ hL hh hf hper]
    simp only
    rw [← integral_sub_left_eq_self (fun y => f y * scaledMollifier ρ h (x - y)) volume x]
    simp
  simp_rw [hcv]
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
  -- Exchange the order of integration on `Ioc (-L/2) (L/2) × ℝ`.
  have hfub := integral_integral_swap (μ := volume.restrict (Ioc (-(L / 2)) (L / 2)))
    (ν := (volume : Measure ℝ)) (f := fun x u => f (x - u) * scaledMollifier ρ h u)
    (integrable_prod_sub_mul hf hκ hκc)
  rw [hfub]
  -- The inner integral over one period does not depend on `u`.
  have hinner : ∀ u : ℝ, ∫ x in Ioc (-(L / 2)) (L / 2), f (x - u) * scaledMollifier ρ h u =
      (∫ x in Ioc (-(L / 2)) (L / 2), f x) * scaledMollifier ρ h u := by
    intro u
    rw [MeasureTheory.integral_mul_const, integral_Ioc_sub_shift hL hper u]
  simp_rw [hinner]
  rw [MeasureTheory.integral_const_mul, integral_scaledMollifier hρ hh, mul_one]

end Riesz1

end
