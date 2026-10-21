/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.NegativeExponent

/-!
# Negative exponents: continuity in place of the value bound

`Riesz1.circleMollify_deriv_bound_neg` (`NegativeExponent.lean`) bounds the derivative of the circle
regularization for `-1 < γ < 0` under the value bound `|f(y)| ≤ circDist(y)^(-γ)`. That bound forces
`f` to vanish at its singular point `0`. The derivative of the regularization does not change when a
constant is added to `f`, so the value bound is stronger than the derivative bound needs.

This file replaces the value bound by continuity of `f`. For a continuous periodic `f` whose
derivative satisfies `|f'(y)| ≤ circDist(y)^(-1-γ)` off zero, the value bound holds after subtracting
`f(0)`, and the derivative bound follows from `NegativeExponent.lean` applied to `f - f(0)`.

Main result:
* `Riesz1.circleMollify_deriv_bound_neg_of_continuous`: for `-1 < γ < 0`, if `f` is continuous,
  `L`-periodic and differentiable off zero with `|f'(y)| ≤ circDist(y)^(-1-γ)`, then
  `|f_h'(x)| ≤ C max(circDist(x), h)^(-1-γ)` for every `0 < h` and every `x`, with `C` depending
  only on `ρ` and `γ`. No value bound is assumed.

Continuity cannot be dropped: the jump example in `NegativeExponent.lean` is discontinuous at `0`.
-/

public section

open MeasureTheory Set intervalIntegral

namespace Riesz1

/-- **Value bound on a half-interval.** Let `F` be continuous, with `|F'(r)| ≤ r^(-1-γ)` on `(0, t]`
and `F` differentiable there. Then `|F(t) - F(0)| ≤ (-γ)⁻¹ t^(-γ)`. The integral of `r^(-1-γ)` is
finite because `-1-γ > -1`. -/
lemma abs_sub_zero_le_of_pos {F : ℝ → ℝ} {γ t : ℝ} (hγ0 : γ < 0) (ht : 0 < t)
    (hF : Continuous F) (hd : ∀ r, 0 < r → r ≤ t → DifferentiableAt ℝ F r)
    (hF' : ∀ r, 0 < r → r ≤ t → |deriv F r| ≤ r ^ (-1 - γ)) :
    |F t - F 0| ≤ (-γ)⁻¹ * t ^ (-γ) := by
  have hcont : ContinuousOn F (Icc 0 t) := hF.continuousOn
  have hderiv : ∀ r ∈ Ioo 0 t, HasDerivAt F (deriv F r) r := fun r hr =>
    (hd r hr.1 hr.2.le).hasDerivAt
  have hφ : IntervalIntegrable (fun r : ℝ => r ^ (-1 - γ)) volume 0 t :=
    intervalIntegrable_rpow' (by linarith)
  have hle : ∀ᵐ r ∂(volume.restrict (uIoc 0 t)), ‖deriv F r‖ ≤ ‖r ^ (-1 - γ)‖ := by
    rw [uIoc_of_le ht.le]
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hr.1.le _)]
    exact hF' r hr.1 hr.2
  have hint : IntervalIntegrable (deriv F) volume 0 t :=
    hφ.mono_fun (measurable_deriv F).aestronglyMeasurable.restrict hle
  have hFTC := integral_eq_sub_of_hasDerivAt_of_le ht.le hcont hderiv hint
  have hb : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioc 0 t → ‖deriv F r‖ ≤ r ^ (-1 - γ) :=
    Filter.Eventually.of_forall fun r hr => by
      rw [Real.norm_eq_abs]
      exact hF' r hr.1 hr.2
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le ht.le hb hφ
  have hpow : ∫ r in (0 : ℝ)..t, r ^ (-1 - γ) = (-γ)⁻¹ * t ^ (-γ) := by
    rw [integral_rpow (Or.inl (by linarith))]
    have e : -1 - γ + 1 = -γ := by ring
    rw [e, Real.zero_rpow (neg_ne_zero.mpr hγ0.ne), sub_zero, div_eq_inv_mul]
  calc |F t - F 0| = ‖∫ r in (0 : ℝ)..t, deriv F r‖ := by rw [hFTC, Real.norm_eq_abs]
    _ ≤ ∫ r in (0 : ℝ)..t, r ^ (-1 - γ) := by simpa [Real.norm_eq_abs] using hnorm
    _ = (-γ)⁻¹ * t ^ (-γ) := hpow

/-- **Value bound on the half-period, both signs.** Let `f` be continuous, with `f` differentiable
at every `r` with `0 < |r| ≤ L/2` and `|f'(r)| ≤ |r|^(-1-γ)` there. Then, for every `t` with
`|t| ≤ L/2`, `|f(t) - f(0)| ≤ (-γ)⁻¹ |t|^(-γ)`. The negative side follows from the positive one by
reflection. -/
lemma abs_sub_zero_le_of_abs_le {f : ℝ → ℝ} {γ L t : ℝ} (hγ0 : γ < 0)
    (hf : Continuous f) (hd : ∀ r : ℝ, 0 < |r| → |r| ≤ L / 2 → DifferentiableAt ℝ f r)
    (hD : ∀ r : ℝ, 0 < |r| → |r| ≤ L / 2 → |deriv f r| ≤ |r| ^ (-1 - γ))
    (ht : |t| ≤ L / 2) : |f t - f 0| ≤ (-γ)⁻¹ * |t| ^ (-γ) := by
  rcases lt_trichotomy t 0 with h | h | h
  · -- Reflect `t < 0` to `-t > 0`: the function `r ↦ f(-r)` has derivative `-f'(-r)`.
    have ht' : -t ≤ L / 2 := by rw [abs_of_neg h] at ht; exact ht
    have key := abs_sub_zero_le_of_pos (F := fun r => f (-r)) hγ0 (neg_pos.mpr h)
      (hf.comp continuous_neg)
      (fun r hr hrt => (hd (-r) (by rw [abs_neg, abs_of_pos hr]; exact hr)
          (by rw [abs_neg, abs_of_pos hr]; linarith)).comp r differentiableAt_id.neg)
      (fun r hr hrt => by
        rw [deriv_comp_neg, abs_neg]
        have := hD (-r) (by rw [abs_neg, abs_of_pos hr]; exact hr)
          (by rw [abs_neg, abs_of_pos hr]; linarith)
        rwa [abs_neg, abs_of_pos hr] at this)
    simp only [neg_neg, neg_zero] at key
    rw [abs_of_neg h]
    exact key
  · subst h
    simp [Real.zero_rpow (neg_ne_zero.mpr hγ0.ne)]
  · have ht' : t ≤ L / 2 := by rw [abs_of_pos h] at ht; exact ht
    rw [abs_of_pos h]
    exact abs_sub_zero_le_of_pos hγ0 h hf
      (fun r hr hrt => hd r (by rw [abs_of_pos hr]; exact hr)
        (by rw [abs_of_pos hr]; linarith))
      (fun r hr hrt => by
        have := hD r (by rw [abs_of_pos hr]; exact hr) (by rw [abs_of_pos hr]; linarith)
        rwa [abs_of_pos hr] at this)

/-- **Value bound on the circle.** Let `f` be continuous and `L`-periodic, differentiable off the
lifts of zero, with `|f'(y)| ≤ circDist(y)^(-1-γ)` off zero. Then, for every `y`,
`|f(y) - f(0)| ≤ (-γ)⁻¹ circDist(y)^(-γ)`. -/
lemma abs_sub_zero_le_circDist {f : ℝ → ℝ} {γ L : ℝ} (hγ0 : γ < 0) (hL : 0 < L)
    (hper : Function.Periodic f L) (hf : Continuous f)
    (hd : ∀ y : ℝ, circDist L y ≠ 0 → DifferentiableAt ℝ f y)
    (hD : ∀ y : ℝ, circDist L y ≠ 0 → |deriv f y| ≤ circDist L y ^ (-1 - γ)) (y : ℝ) :
    |f y - f 0| ≤ (-γ)⁻¹ * circDist L y ^ (-γ) := by
  -- The representative `t = y - L round(y/L)` of `y` lies in `[-L/2, L/2]`.
  have hdist : ∀ r : ℝ, |r| ≤ L / 2 → circDist L r = |r| := fun r hr =>
    circDist_eq_abs hL hr
  have hnz : ∀ r : ℝ, 0 < |r| → |r| ≤ L / 2 → circDist L r ≠ 0 := fun r hr hrL => by
    rw [hdist r hrL]; exact hr.ne'
  set t : ℝ := y - L * round (y / L) with ht_def
  have hct : circDist L y = |t| := rfl
  have h1 : |y / L - round (y / L)| ≤ 1 / 2 := abs_sub_round _
  have h2 : t = L * (y / L - round (y / L)) := by
    rw [ht_def]
    field_simp
  have htL : |t| ≤ L / 2 := by
    calc |t| = L * |y / L - round (y / L)| := by rw [h2, abs_mul, abs_of_pos hL]
      _ ≤ L * (1 / 2) := mul_le_mul_of_nonneg_left h1 hL.le
      _ = L / 2 := by ring
  have hft : f t = f y := by
    rw [ht_def, mul_comm]
    exact hper.sub_int_mul_eq _
  have key := abs_sub_zero_le_of_abs_le hγ0 hf
    (fun r hr hrL => hd r (hnz r hr hrL))
    (fun r hr hrL => by
      have := hD r (hnz r hr hrL)
      rwa [hdist r hrL] at this)
    htL
  calc |f y - f 0| = |f t - f 0| := by rw [hft]
    _ ≤ (-γ)⁻¹ * |t| ^ (-γ) := key
    _ = (-γ)⁻¹ * circDist L y ^ (-γ) := by rw [hct]

/-- **Mollification is affine in the function.** For a locally integrable `f`, the line convolution
of `a f + b` is `a (f ⋆ ρ_h) + b`, because the scaled mollifier has integral one. -/
lemma mollifyLine_affine {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h) {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (a b x : ℝ) :
    mollifyLine ρ h (fun y => a * f y + b) x = a * mollifyLine ρ h f x + b := by
  have hI : Integrable (fun y => f y * scaledMollifier ρ h (x - y)) :=
    integrable_mul_scaled_sub hρ hh hf x
  have hJ : Integrable (fun y => scaledMollifier ρ h (x - y)) := by
    have := integrable_mul_scaled_sub hρ hh (locallyIntegrable_const (1 : ℝ)) x
    simpa using this
  have hsM : ∫ y, scaledMollifier ρ h (x - y) = 1 :=
    (integral_sub_left_eq_self (fun y => scaledMollifier ρ h y) volume x).trans
      (integral_scaledMollifier hρ hh)
  unfold mollifyLine
  have hpt : ∀ y, (a * f y + b) * scaledMollifier ρ h (x - y) =
      a * (f y * scaledMollifier ρ h (x - y)) + b * scaledMollifier ρ h (x - y) :=
    fun y => by ring
  simp_rw [hpt]
  rw [integral_add (hI.const_mul a) (hJ.const_mul b), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, hsM]
  ring

/-- **Regularization derivative bound for `-1 < γ < 0` under continuity.** Let `ρ` be a
mollifier and `-1 < γ < 0`. There is `C > 0`, depending only on `ρ` and `γ`, such that for every
`L > 0` and every continuous `L`-periodic `f` that is differentiable off the lifts of zero with
`|f'(y)| ≤ circDist(y)^(-1-γ)` there, for every `h > 0` and `x`, the regularization has a derivative
at `x` bounded by `C max(circDist(x), h)^(-1-γ)`. -/
theorem circleMollify_deriv_bound_neg_of_continuous {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {γ : ℝ}
    (hγ0 : γ < 0) (hγ1 : -1 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ) (f : ℝ → ℝ), 0 < L → Function.Periodic f L → Continuous f →
      (∀ y : ℝ, circDist L y ≠ 0 → DifferentiableAt ℝ f y) →
      (∀ y : ℝ, circDist L y ≠ 0 → |deriv f y| ≤ circDist L y ^ (-1 - γ)) →
      ∀ h : ℝ, 0 < h → ∀ x : ℝ, ∃ D : ℝ,
        HasDerivAt (circleMollify ρ L h f) D x ∧
          |D| ≤ C * (max (circDist L x) h) ^ (-1 - γ) := by
  obtain ⟨C₁, hC₁, hbound⟩ := circleMollify_deriv_bound_neg hρ hγ0 hγ1
  have hγpos : 0 < -γ := by linarith
  refine ⟨(-γ)⁻¹ * C₁, mul_pos (inv_pos.mpr hγpos) hC₁, ?_⟩
  intro L f hL hper hf hd hD h hh x
  -- The shifted and rescaled `g = (-γ)(f - f(0))` satisfies the value bound with constant one.
  set g : ℝ → ℝ := fun y => (-γ) * (f y - f 0) with hg_def
  have hgV : ∀ y : ℝ, |g y| ≤ circDist L y ^ (-γ) := fun y => by
    calc |g y| = (-γ) * |f y - f 0| := by
          rw [hg_def, abs_mul, abs_of_pos hγpos]
      _ ≤ (-γ) * ((-γ)⁻¹ * circDist L y ^ (-γ)) :=
          mul_le_mul_of_nonneg_left (abs_sub_zero_le_circDist hγ0 hL hper hf hd hD y)
            hγpos.le
      _ = circDist L y ^ (-γ) := mul_inv_cancel_left₀ hγpos.ne' _
  have hgper : Function.Periodic g L := fun y => by
    simp only [hg_def, hper y]
  have hgc : Continuous g := by
    rw [hg_def]
    fun_prop
  have hgd : ∀ y : ℝ, circDist L y ≠ 0 → DifferentiableAt ℝ g y := fun y hy =>
    ((hd y hy).sub_const (f 0)).const_mul (-γ)
  have hgD : ∀ y : ℝ, circDist L y ≠ 0 → |deriv g y| ≤ circDist L y ^ (-1 - γ) := by
    intro y hy
    have hder : deriv g y = (-γ) * deriv f y :=
      (((hd y hy).hasDerivAt.sub_const (f 0)).const_mul (-γ)).deriv
    rw [hder, abs_mul, abs_of_pos hγpos]
    have h1 := hD y hy
    calc (-γ) * |deriv f y| ≤ 1 * |deriv f y| :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ = |deriv f y| := one_mul _
      _ ≤ circDist L y ^ (-1 - γ) := h1
  obtain ⟨D₁, hD₁, hD₁b⟩ := hbound L g hL hgper hgc.locallyIntegrable
    (Filter.Eventually.of_forall fun y _ => hgV y) hgd hgD h hh x
  -- Undoing the affine change: `f ⋆ ρ_h = f(0) + (-γ)⁻¹ (g ⋆ ρ_h)` on the line.
  have hid : ∀ z : ℝ, circleMollify ρ L h f z = f 0 + (-γ)⁻¹ * circleMollify ρ L h g z := by
    intro z
    rw [circleMollify_eq_mollifyLine hρ hL hh hf.locallyIntegrable hper,
      circleMollify_eq_mollifyLine hρ hL hh hgc.locallyIntegrable hgper]
    have hgaff : g = fun y => (-γ) * f y + (-(-γ) * f 0) := by
      funext y
      rw [hg_def]
      ring
    rw [hgaff, mollifyLine_affine hρ hh hf.locallyIntegrable]
    have hI : (-γ)⁻¹ * (-γ) = 1 := inv_mul_cancel₀ hγpos.ne'
    have hcancel : (-γ)⁻¹ * ((-γ) * mollifyLine ρ h f z + -(-γ) * f 0) =
        mollifyLine ρ h f z - f 0 := by
      linear_combination (mollifyLine ρ h f z - f 0) * hI
    rw [hcancel]
    ring
  have hDf : HasDerivAt (circleMollify ρ L h f) ((-γ)⁻¹ * D₁) x := by
    have hfun : circleMollify ρ L h f = fun z => f 0 + (-γ)⁻¹ * circleMollify ρ L h g z :=
      funext hid
    rw [hfun]
    exact (hD₁.const_mul ((-γ)⁻¹)).const_add (f 0)
  refine ⟨(-γ)⁻¹ * D₁, hDf, ?_⟩
  rw [abs_mul, abs_of_pos (inv_pos.mpr hγpos)]
  calc (-γ)⁻¹ * |D₁| ≤ (-γ)⁻¹ * (C₁ * (max (circDist L x) h) ^ (-1 - γ)) :=
        mul_le_mul_of_nonneg_left hD₁b (inv_nonneg.mpr hγpos.le)
    _ = (-γ)⁻¹ * C₁ * (max (circDist L x) h) ^ (-1 - γ) := by ring

end Riesz1

end
