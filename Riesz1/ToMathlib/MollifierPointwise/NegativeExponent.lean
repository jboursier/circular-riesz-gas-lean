/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.Circle

/-!
# Pointwise regularization estimates for negative exponents

Lemma 5.1 is stated for `0 ≤ γ < 1`. Its uniform part uses the pointwise estimates only with
the exponent `b = 1 - s + α ≥ 0` (its bounds for `α < 0` come from a Fourier argument). This
file extends the pointwise estimates to `-1 < γ < 0`. No statement in the paper depends on it.

* `Riesz1.circleMollify_sup_bound_neg`: for `γ < 0` and `|f(y)| ≤ circDist(y)^(-γ)`, the regularization
  satisfies `|f_h(x)| ≤ C max(circDist(x), h)^(-γ)`.
* `Riesz1.circleMollify_deriv_bound_neg`: for `-1 < γ < 0`, with the value bound
  `|f(y)| ≤ circDist(y)^(-γ)` added, `|f_h'(x)| ≤ C max(circDist(x), h)^(-1-γ)`.

The value bound is needed for the derivative. Without it the derivative bound is false: a smooth step
`f` with a jump at `0` (constant `1` on `(0, L/4)`, `0` on `(-L/2, 0)`, and small slope elsewhere)
satisfies `|f'(y)| ≤ |y|^(-1-γ)` off `0`, but `f_h'(0) = ρ(0) / h`, which is not `O(h^(-1-γ))` as
`h → 0`.

Length `L > 0` and scale `h > 0` are arbitrary. No bound `h ≤ 1` or `L ≥ 1` is used.
-/

public section

open MeasureTheory Set intervalIntegral

namespace Riesz1

/-- The zero set of `circDist L` is countable, so the zeros are almost nowhere. -/
lemma ae_circDist_ne_zero (L : ℝ) :
    ∀ᵐ y ∂(volume : Measure ℝ), circDist L y ≠ 0 := by
  have hsub : {y : ℝ | circDist L y = 0} ⊆ Set.range (fun n : ℤ => (n : ℝ) * L) := by
    intro y hy
    refine ⟨round (y / L), ?_⟩
    have h0 : |y - L * round (y / L)| = 0 := hy
    have h1 := abs_eq_zero.mp h0
    show ((round (y / L) : ℤ) : ℝ) * L = y
    calc ((round (y / L) : ℤ) : ℝ) * L = L * round (y / L) := mul_comm _ _
      _ = y := by linarith
  have hcount : {y : ℝ | circDist L y = 0}.Countable := (Set.countable_range _).mono hsub
  filter_upwards [hcount.ae_notMem volume] with y hy
  exact hy

/-- **Value bound for negative exponents.** Let `γ < 0`. If `|f(y)| ≤ circDist(y)^(-γ)` for almost
every `y`, then `|f_h(x)| ≤ C max(circDist(x), h)^(-γ)` for every `x`, with `C` depending only on
`γ`. -/
theorem circleMollify_sup_bound_neg {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {γ : ℝ} (hγ : γ < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ) (f : ℝ → ℝ), 0 < L → Function.Periodic f L →
      LocallyIntegrable f volume →
      (∀ᵐ y ∂(volume : Measure ℝ), circDist L y ≠ 0 → |f y| ≤ circDist L y ^ (-γ)) →
      ∀ h : ℝ, 0 < h → ∀ x : ℝ,
        |circleMollify ρ L h f x| ≤ C * (max (circDist L x) h) ^ (-γ) := by
  refine ⟨(3 / 2 : ℝ) ^ (-γ), by positivity, ?_⟩
  intro L f hL hper hf hfb h hh x
  set M := max (circDist L x) h with hM
  have hM1 : circDist L x ≤ M := le_max_left _ _
  have hM2 : h ≤ M := le_max_right _ _
  have hMpos : 0 < M := lt_of_lt_of_le hh hM2
  have hγ' : (0 : ℝ) ≤ -γ := by linarith
  rw [circleMollify_eq_mollifyLine hρ hL hh hf hper x]
  show |(∫ y, f y * scaledMollifier ρ h (x - y))| ≤ (3 / 2 : ℝ) ^ (-γ) * M ^ (-γ)
  have hκi : Integrable (scaledMollifier ρ h) :=
    ((contDiff_scaledMollifier hρ (h := h)).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_scaledMollifier hρ hh))
  have hintg : Integrable (fun y => (3 / 2 : ℝ) ^ (-γ) * M ^ (-γ) * scaledMollifier ρ h (x - y)) :=
    ((hκi.comp_sub_left x).const_mul _)
  have hbound : ∀ᵐ y ∂(volume : Measure ℝ),
      ‖f y * scaledMollifier ρ h (x - y)‖ ≤
        (3 / 2 : ℝ) ^ (-γ) * M ^ (-γ) * scaledMollifier ρ h (x - y) := by
    filter_upwards [hfb, ae_circDist_ne_zero L] with y hy hne
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (scaledMollifier_nonneg hρ hh _)]
    by_cases hz : scaledMollifier ρ h (x - y) = 0
    · simp [hz]
    · have hclose : |x - y| < h / 2 := by
        by_contra hc
        exact hz (scaledMollifier_eq_zero hρ hh (not_lt.mp hc))
      have hcd : circDist L y ≤ 3 / 2 * M := by
        have h1 := circDist_le_add_abs hL y x
        rw [abs_sub_comm] at h1
        linarith
      have hpow : circDist L y ^ (-γ) ≤ (3 / 2 * M) ^ (-γ) :=
        Real.rpow_le_rpow (circDist_nonneg _ _) hcd hγ'
      rw [Real.mul_rpow (by norm_num) hMpos.le] at hpow
      have hρ0 := scaledMollifier_nonneg hρ hh (x - y)
      exact mul_le_mul_of_nonneg_right ((hy hne).trans hpow) hρ0
  have hfinal := norm_integral_le_of_norm_le hintg hbound
  rw [MeasureTheory.integral_const_mul, integral_sub_left_eq_self (scaledMollifier ρ h) volume x,
    integral_scaledMollifier hρ hh, mul_one] at hfinal
  rw [← Real.norm_eq_abs]
  exact hfinal

/-- **Derivative bound for negative exponents.** Let `-1 < γ < 0`. Assume the value bound
`|f(y)| ≤ circDist(y)^(-γ)` for almost every `y`, that `f` is differentiable off zero, and that
`|f'(y)| ≤ circDist(y)^(-1-γ)` off zero. Then `f_h` is differentiable, and its derivative satisfies
`|f_h'(x)| ≤ C max(circDist(x), h)^(-1-γ)`, with `C` depending only on `ρ` and `γ`. -/
theorem circleMollify_deriv_bound_neg {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {γ : ℝ} (hγ0 : γ < 0)
    (hγ1 : -1 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ) (f : ℝ → ℝ), 0 < L → Function.Periodic f L →
      LocallyIntegrable f volume →
      (∀ᵐ y ∂(volume : Measure ℝ), circDist L y ≠ 0 → |f y| ≤ circDist L y ^ (-γ)) →
      (∀ y : ℝ, circDist L y ≠ 0 → DifferentiableAt ℝ f y) →
      (∀ y : ℝ, circDist L y ≠ 0 → |deriv f y| ≤ circDist L y ^ (-1 - γ)) →
      ∀ h : ℝ, 0 < h → ∀ x : ℝ, ∃ D : ℝ,
        HasDerivAt (circleMollify ρ L h f) D x ∧
          |D| ≤ C * (max (circDist L x) h) ^ (-1 - γ) := by
  obtain ⟨M, hM0, hM⟩ := hρ.exists_bound_deriv
  have hK0 : 0 ≤ (3 / 2 : ℝ) ^ (-γ) * M := mul_nonneg (by positivity) hM0
  have hK1 : 0 < (1 / 2 : ℝ) ^ (-1 - γ) := by positivity
  refine ⟨(3 / 2 : ℝ) ^ (-γ) * M + (1 / 2 : ℝ) ^ (-1 - γ) + 1, by linarith, ?_⟩
  intro L f hL hper hf hfb hdiff hder h hh x
  have hfun : circleMollify ρ L h f = mollifyLine ρ h f :=
    funext (circleMollify_eq_mollifyLine hρ hL hh hf hper)
  refine ⟨∫ y, f y * deriv (scaledMollifier ρ h) (x - y), ?_, ?_⟩
  · rw [hfun]
    exact hasDerivAt_mollifyLine hρ hh hf x
  have hc0 : 0 ≤ circDist L x := circDist_nonneg _ _
  rcases lt_or_ge (circDist L x) h with hnear | hfar
  · -- Near case: `circDist L x < h`, so the maximum is `h`.
    rw [max_eq_right hnear.le]
    set B : ℝ := (3 / 2 * h) ^ (-γ) * (M * (h⁻¹ * h⁻¹)) with hB
    have hB0 : 0 ≤ B := mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (mul_nonneg hM0 (by positivity))
    set g : ℝ → ℝ := (Ioo (x - h / 2) (x + h / 2)).indicator (fun _ => B) with hg
    have hgi : Integrable g :=
      (integrableOn_const measure_Ioo_lt_top.ne).integrable_indicator measurableSet_Ioo
    have hpt : ∀ᵐ y ∂(volume : Measure ℝ),
        ‖f y * deriv (scaledMollifier ρ h) (x - y)‖ ≤ g y := by
      filter_upwards [hfb, ae_circDist_ne_zero L] with y hy hne
      by_cases hw : |x - y| < h / 2
      · have hyI : y ∈ Ioo (x - h / 2) (x + h / 2) := by
          obtain ⟨h1, h2⟩ := abs_lt.mp hw
          exact ⟨by linarith, by linarith⟩
        rw [hg, Set.indicator_of_mem hyI]
        have hcd : circDist L y ≤ 3 / 2 * h := by
          have h1 := circDist_le_add_abs hL y x
          rw [abs_sub_comm] at h1
          linarith
        have hpow : |f y| ≤ (3 / 2 * h) ^ (-γ) :=
          (hy hne).trans (Real.rpow_le_rpow (circDist_nonneg _ _) hcd (by linarith))
        have hd : |deriv (scaledMollifier ρ h) (x - y)| ≤ M * (h⁻¹ * h⁻¹) :=
          abs_deriv_scaledMollifier_le hρ hh hM (x - y)
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul hpow hd (abs_nonneg _) (Real.rpow_nonneg (by positivity) _)
      · have hw' : h / 2 ≤ |x - y| := le_of_not_gt hw
        rw [deriv_scaledMollifier_eq_zero hρ hh hw', mul_zero, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => hB0) y
    have hbd := norm_integral_le_of_norm_le hgi hpt
    have hgint : ∫ y, g y = h * B := by
      rw [hg, integral_indicator_const B measurableSet_Ioo, Real.volume_real_Ioo_of_le (by linarith),
        smul_eq_mul]
      ring
    have hpow_h : h ^ (-1 - γ) = h ^ (-γ) * h⁻¹ := by
      rw [show (-1 - γ) = -γ + (-1) by ring, Real.rpow_add hh, Real.rpow_neg_one]
    have hBeq : h * B = (3 / 2 : ℝ) ^ (-γ) * M * h ^ (-1 - γ) := by
      rw [hB, hpow_h, Real.mul_rpow (by norm_num) hh.le]
      field_simp
    rw [hgint, hBeq] at hbd
    rw [Real.norm_eq_abs] at hbd
    exact hbd.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hh.le _))
  · -- Far case: `circDist L x ≥ h`, so the maximum is `circDist L x`.
    rw [max_eq_left hfar]
    have hcpos : 0 < circDist L x := lt_of_lt_of_le hh hfar
    -- On the window `[x - h/2, x + h/2]` the circle distance is at least `circDist L x / 2`.
    have hwin : ∀ y ∈ Icc (x - h / 2) (x + h / 2), circDist L x * (1 / 2) ≤ circDist L y := by
      intro y hy
      have hxy : |y - x| ≤ h / 2 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have h1 := circDist_le_add_abs hL x y
      rw [abs_sub_comm] at h1
      linarith
    have hwin_pos : ∀ y ∈ Icc (x - h / 2) (x + h / 2), 0 < circDist L y := fun y hy =>
      lt_of_lt_of_le (by positivity) (hwin y hy)
    have hβ : -1 - γ < 0 := by linarith
    have hpowle : ∀ y ∈ Icc (x - h / 2) (x + h / 2),
        circDist L y ^ (-1 - γ) ≤ (circDist L x * (1 / 2)) ^ (-1 - γ) := fun y hy =>
      Real.rpow_le_rpow_of_nonpos (by positivity) (hwin y hy) hβ.le
    have hab : x - h / 2 ≤ x + h / 2 := by linarith
    -- The derivative of `y ↦ ρ_h(x - y)`.
    have hv : ∀ y : ℝ, HasDerivAt (fun y => scaledMollifier ρ h (x - y))
        (-(deriv (scaledMollifier ρ h) (x - y))) y := by
      intro y
      have h1 : HasDerivAt (fun y : ℝ => x - y) (-1) y := by
        simpa using (hasDerivAt_id y).const_sub x
      have h2 := ((contDiff_scaledMollifier hρ (h := h)).differentiable (by simp) (x - y)).hasDerivAt
      have h3 := h2.comp y h1
      exact h3.congr_deriv (by ring)
    have hva : scaledMollifier ρ h (x - (x - h / 2)) = 0 :=
      scaledMollifier_eq_zero hρ hh (by rw [show x - (x - h / 2) = h / 2 by ring, abs_of_pos (by linarith)])
    have hvb : scaledMollifier ρ h (x - (x + h / 2)) = 0 :=
      scaledMollifier_eq_zero hρ hh (by
        rw [show x - (x + h / 2) = -(h / 2) by ring, abs_neg, abs_of_pos (by linarith)])
    -- Integrate by parts on the window, where `f` is differentiable.
    have hu' : IntervalIntegrable (deriv f) volume (x - h / 2) (x + h / 2) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      refine Measure.integrableOn_of_bounded (M := (circDist L x * (1 / 2)) ^ (-1 - γ))
        measure_Ioc_lt_top.ne (measurable_deriv f).aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioc (fun y hy => ?_)
      have hyI : y ∈ Icc (x - h / 2) (x + h / 2) := ⟨hy.1.le, hy.2⟩
      rw [Real.norm_eq_abs]
      exact (hder y (hwin_pos y hyI).ne').trans (hpowle y hyI)
    have hv' : IntervalIntegrable (fun y => -(deriv (scaledMollifier ρ h) (x - y))) volume
        (x - h / 2) (x + h / 2) := by
      have hc : Continuous (fun y => -(deriv (scaledMollifier ρ h) (x - y))) :=
        ((contDiff_scaledMollifier hρ (h := h)).continuous_deriv (by simp)).comp
          (continuous_const.sub continuous_id) |>.neg
      exact hc.intervalIntegrable _ _
    have hdiff_win : ∀ y ∈ uIcc (x - h / 2) (x + h / 2), HasDerivAt f (deriv f y) y := by
      intro y hy
      rw [uIcc_of_le hab] at hy
      exact (hdiff y (hwin_pos y hy).ne').hasDerivAt
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := f)
      (v := fun y => scaledMollifier ρ h (x - y)) (u' := deriv f)
      (v' := fun y => -(deriv (scaledMollifier ρ h) (x - y))) hdiff_win
      (fun y _ => hv y) hu' hv'
    simp only [hva, hvb, mul_zero, zero_sub, sub_zero, mul_neg, intervalIntegral.integral_neg,
      neg_inj] at hibp
    -- `∫ f ρ_h'(x - ·) = ∫ f' ρ_h(x - ·)` over the window. The integrand vanishes off the window.
    have hD : ∫ y, f y * deriv (scaledMollifier ρ h) (x - y) =
        ∫ y in (x - h / 2)..(x + h / 2), f y * deriv (scaledMollifier ρ h) (x - y) := by
      rw [intervalIntegral.integral_of_le hab]
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hyo : h / 2 ≤ |x - y| := by
        by_contra hc
        obtain ⟨h1, h2⟩ := abs_lt.mp (not_le.mp hc)
        exact hy ⟨by linarith, by linarith⟩
      rw [deriv_scaledMollifier_eq_zero hρ hh hyo, mul_zero]
    rw [hD, hibp, intervalIntegral.integral_of_le hab, ← Real.norm_eq_abs]
    have hκi : Integrable (scaledMollifier ρ h) :=
      ((contDiff_scaledMollifier hρ (h := h)).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_scaledMollifier hρ hh))
    have hvint : Integrable (fun y => scaledMollifier ρ h (x - y)) := hκi.comp_sub_left x
    have hbnd : ∀ᵐ y ∂(volume.restrict (Ioc (x - h / 2) (x + h / 2))),
        ‖deriv f y * scaledMollifier ρ h (x - y)‖ ≤
          (circDist L x * (1 / 2)) ^ (-1 - γ) * scaledMollifier ρ h (x - y) := by
      refine ae_restrict_of_forall_mem measurableSet_Ioc (fun y hy => ?_)
      have hyI : y ∈ Icc (x - h / 2) (x + h / 2) := ⟨hy.1.le, hy.2⟩
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (scaledMollifier_nonneg hρ hh _)]
      exact mul_le_mul_of_nonneg_right ((hder y (hwin_pos y hyI).ne').trans (hpowle y hyI))
        (scaledMollifier_nonneg hρ hh _)
    have hgi' : Integrable (fun y => (circDist L x * (1 / 2)) ^ (-1 - γ) *
        scaledMollifier ρ h (x - y)) (volume.restrict (Ioc (x - h / 2) (x + h / 2))) :=
      (hvint.const_mul _).integrableOn
    have hbd2 := norm_integral_le_of_norm_le hgi' hbnd
    rw [MeasureTheory.integral_const_mul] at hbd2
    have hvle : ∫ y in Ioc (x - h / 2) (x + h / 2), scaledMollifier ρ h (x - y) ≤ 1 := by
      have h1 := setIntegral_le_integral (s := Ioc (x - h / 2) (x + h / 2)) hvint
        (Filter.Eventually.of_forall fun y => scaledMollifier_nonneg hρ hh (x - y))
      rwa [integral_sub_left_eq_self (scaledMollifier ρ h) volume x,
        integral_scaledMollifier hρ hh] at h1
    have hvnn : 0 ≤ ∫ y in Ioc (x - h / 2) (x + h / 2), scaledMollifier ρ h (x - y) :=
      setIntegral_nonneg measurableSet_Ioc (fun y _ => scaledMollifier_nonneg hρ hh (x - y))
    have hK : (circDist L x * (1 / 2)) ^ (-1 - γ) =
        circDist L x ^ (-1 - γ) * (1 / 2) ^ (-1 - γ) :=
      Real.mul_rpow hc0 (by norm_num)
    rw [hK] at hbd2
    have hcβ : 0 ≤ circDist L x ^ (-1 - γ) := Real.rpow_nonneg hc0 _
    have hKβ : 0 ≤ circDist L x ^ (-1 - γ) * (1 / 2) ^ (-1 - γ) := mul_nonneg hcβ hK1.le
    have h5 : circDist L x ^ (-1 - γ) * (1 / 2) ^ (-1 - γ) *
        ∫ y in Ioc (x - h / 2) (x + h / 2), scaledMollifier ρ h (x - y) ≤
          circDist L x ^ (-1 - γ) * (1 / 2) ^ (-1 - γ) :=
      mul_le_of_le_one_right hKβ hvle
    have h6 : (1 / 2 : ℝ) ^ (-1 - γ) ≤
        (3 / 2 : ℝ) ^ (-γ) * M + (1 / 2 : ℝ) ^ (-1 - γ) + 1 := by linarith
    have h7 : circDist L x ^ (-1 - γ) * (1 / 2) ^ (-1 - γ) ≤
        ((3 / 2 : ℝ) ^ (-γ) * M + (1 / 2 : ℝ) ^ (-1 - γ) + 1) * circDist L x ^ (-1 - γ) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right h6 hcβ
    exact hbd2.trans (h5.trans h7)

end Riesz1

end
