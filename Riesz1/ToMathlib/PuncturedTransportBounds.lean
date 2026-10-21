/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PuncturedOscillatoryUniform

/-!
# Quantitative first derivative and integral bounds at a puncture

The reference derivative is controlled by the supremum of the primitive on a fixed
interval. Integrating the second derivative then gives the exact positive singularity
exponent, and an explicit integral bound. Constants precede the function. These are
analytic helpers for Lemma 5.1.
-/

public section

open MeasureTheory Set intervalIntegral

namespace Riesz1.PuncturedDerivative

/-- Two-sided integration at a puncture, retaining the exact positive exponent.
The coefficient can depend on the two reference values of `q` at distance `R`. -/
theorem exists_abs_le_rpow_punctured {q : ℝ → ℝ} {a b C R : ℝ}
    (hb : 0 < b) (hC : 0 ≤ C) (hR : 0 < R)
    (hq : ∀ t : ℝ, 0 < |t - a| → |t - a| ≤ R → DifferentiableAt ℝ q t)
    (hbound : ∀ t : ℝ, 0 < |t - a| → |t - a| ≤ R →
      |deriv q t| ≤ C * |t - a| ^ (-1 - b)) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 < |t - a| → |t - a| ≤ R →
      |q t| ≤ K * |t - a| ^ (-b) := by
  let Q := |q (a + R)| + |q (a - R)|
  have hQ : 0 ≤ Q := add_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨Q * R ^ b + C / b + 1, by positivity, ?_⟩
  intro t ht htR
  have hright : ∀ u ∈ Ioc 0 R, DifferentiableAt ℝ (fun v => q (a + v)) u := by
    intro u hu
    exact (hq (a + u) (by simpa [abs_of_pos hu.1] using hu.1)
      (by simpa [abs_of_pos hu.1] using hu.2)).comp u (by fun_prop)
  have hleft : ∀ u ∈ Ioc 0 R, DifferentiableAt ℝ (fun v => q (a - v)) u := by
    intro u hu
    exact (hq (a - u) (by simpa [abs_of_pos hu.1] using hu.1)
      (by simpa [abs_of_pos hu.1] using hu.2)).comp u (by fun_prop)
  have hrightb : ∀ u ∈ Ioc 0 R,
      |deriv (fun v => q (a + v)) u| ≤ C * u ^ (-1 - b) := by
    intro u hu
    rw [deriv_comp_const_add]
    simpa [abs_of_pos hu.1] using hbound (a + u)
      (by simpa [abs_of_pos hu.1] using hu.1) (by simpa [abs_of_pos hu.1] using hu.2)
  have hleftb : ∀ u ∈ Ioc 0 R,
      |deriv (fun v => q (a - v)) u| ≤ C * u ^ (-1 - b) := by
    intro u hu
    rw [deriv_comp_const_sub, abs_neg]
    simpa [abs_of_pos hu.1] using hbound (a - u)
      (by simpa [abs_of_pos hu.1] using hu.1) (by simpa [abs_of_pos hu.1] using hu.2)
  have hraw : |q t| ≤ Q + C / b * |t - a| ^ (-b) := by
    rcases le_or_gt a t with hat | hta
    · have hx : t - a ∈ Ioc 0 R := ⟨by simpa [abs_of_nonneg (sub_nonneg.mpr hat)] using ht,
        by simpa [abs_of_nonneg (sub_nonneg.mpr hat)] using htR⟩
      have h := abs_le_rpow_of_deriv_bound hb hC hR hright hrightb hx
      simp only [add_sub_cancel, abs_of_nonneg (sub_nonneg.mpr hat)] at h ⊢
      dsimp [Q]
      linarith [abs_nonneg (q (a - R))]
    · have hx : a - t ∈ Ioc 0 R := ⟨by linarith,
        by simpa [abs_of_neg (sub_neg.mpr hta)] using htR⟩
      have h := abs_le_rpow_of_deriv_bound hb hC hR hleft hleftb hx
      simp only [sub_sub_cancel] at h
      rw [abs_of_neg (sub_neg.mpr hta), neg_sub]
      dsimp [Q]
      linarith [abs_nonneg (q (a + R))]
  have hpow : 1 ≤ R ^ b * |t - a| ^ (-b) := by
    have hc : |t - a| ^ b * |t - a| ^ (-b) = 1 := by
      rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero]
    rw [← hc]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht.le htR hb.le) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hpow hQ,
    Real.rpow_nonneg (abs_nonneg (t - a)) (-b)]

/-- A bounded primitive and a punctured second-derivative bound give a uniform power
bound for its first derivative. The radius and constants are fixed before the function. -/
theorem uniform_deriv_bound_halfInterval {b C M R : ℝ}
    (hb : 0 < b) (hC : 0 ≤ C) (hM : 0 ≤ M) (hR : 0 < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ℝ → ℝ,
      (∀ x ∈ Ioc 0 R, DifferentiableAt ℝ f x) →
      (∀ x ∈ Ioc 0 R, DifferentiableAt ℝ (deriv f) x) →
      (∀ x ∈ Ioc 0 R, |f x| ≤ M) →
      (∀ x ∈ Ioc 0 R, |deriv (deriv f) x| ≤ C * x ^ (-1 - b)) →
      ∀ x ∈ Ioc 0 R, |deriv f x| ≤ K * x ^ (-b) := by
  let D := C * (R / 2) ^ (-1 - b)
  let Q := 2 * M / (R - R / 2) + D * (R - R / 2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hQ : 0 ≤ Q := by
    have hlen : 0 ≤ R - R / 2 := by linarith
    exact add_nonneg (div_nonneg (mul_nonneg (by norm_num) hM) hlen)
      (mul_nonneg hD hlen)
  refine ⟨Q * R ^ b + C / b + 1, by positivity, ?_⟩
  intro f hf hq hMf hbound x hx
  have hsub : Icc (R / 2) R ⊆ Ioc 0 R := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have href : |deriv f R| ≤ Q := by
    apply abs_deriv_le_of_bounded_primitive (by linarith : R / 2 < R) hD
      (fun t ht => hf t (hsub ht)) (fun t ht => hq t (hsub ht))
      (fun t ht => hMf t (hsub ht)) _ (right_mem_Icc.mpr (by linarith))
    intro t ht
    exact (hbound t (hsub ht)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by linarith : 0 < R / 2) ht.1
        (by linarith : -1 - b ≤ 0)) hC)
  have hp : R ^ b * x ^ (-b) ≥ 1 := by
    have hxp := Real.rpow_le_rpow hx.1.le hx.2 hb.le
    have hc : x ^ b * x ^ (-b) = 1 := by
      rw [← Real.rpow_add hx.1, add_neg_cancel, Real.rpow_zero]
    rw [← hc]
    exact mul_le_mul_of_nonneg_right hxp (Real.rpow_nonneg hx.1.le _)
  have hraw := abs_le_rpow_of_deriv_bound hb hC hR hq hbound hx
  have hp0 : 0 ≤ x ^ (-b) := Real.rpow_nonneg hx.1.le _
  nlinarith [mul_le_mul_of_nonneg_left hp hQ]

/-- The exact positive power bound also controls the integral across the puncture. -/
theorem uniform_deriv_integral_bound_halfInterval {b C M R : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hC : 0 ≤ C) (hM : 0 ≤ M) (hR : 0 < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ℝ → ℝ,
      (∀ x ∈ Ioc 0 R, DifferentiableAt ℝ f x) →
      (∀ x ∈ Ioc 0 R, DifferentiableAt ℝ (deriv f) x) →
      (∀ x ∈ Ioc 0 R, |f x| ≤ M) →
      (∀ x ∈ Ioc 0 R, |deriv (deriv f) x| ≤ C * x ^ (-1 - b)) →
      (∀ x ∈ Ioc 0 R, |deriv f x| ≤ K * x ^ (-b)) ∧
      IntervalIntegrable (deriv f) volume 0 R ∧
      (∫ x in (0 : ℝ)..R, |deriv f x|) ≤ K * R ^ (1 - b) / (1 - b) := by
  obtain ⟨K, hK, hboundK⟩ := uniform_deriv_bound_halfInterval hb hC hM hR
  refine ⟨K, hK, fun f hf hq hMf hbound => ?_⟩
  have hpoint := hboundK f hf hq hMf hbound
  have hi : IntervalIntegrable (deriv f) volume 0 R := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
    exact integrableOn_of_deriv_rpow_bound hb hb1 hC hR hq hbound
  refine ⟨hpoint, hi, ?_⟩
  have hp : IntervalIntegrable (fun x : ℝ => K * x ^ (-b)) volume 0 R :=
    (intervalIntegrable_rpow' (by linarith : -1 < -b)).const_mul K
  have hle := integral_mono_on_of_le_Ioo hR.le hi.abs hp
    (fun x hx => hpoint x ⟨hx.1, hx.2.le⟩)
  have hval : (∫ x in (0 : ℝ)..R, K * x ^ (-b)) = K * R ^ (1 - b) / (1 - b) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < -b))]
    rw [Real.zero_rpow (by linarith : -b + 1 ≠ 0), sub_zero]
    rw [show -b + 1 = 1 - b by ring]
    ring
  exact hval ▸ hle

/-- At the logarithmic endpoint, any fixed positive exponent below one gives both
the pointwise and integral bounds, uniformly over primitives on a radius at most one. -/
theorem uniform_deriv_integral_bound_endpoint {δ C M R : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hR : 0 < R) (hR1 : R ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ℝ → ℝ,
      (∀ x ∈ Ioc 0 R, DifferentiableAt ℝ f x) →
      (∀ x ∈ Ioc 0 R, DifferentiableAt ℝ (deriv f) x) →
      (∀ x ∈ Ioc 0 R, |f x| ≤ M) →
      (∀ x ∈ Ioc 0 R, |deriv (deriv f) x| ≤ C * x ^ (-1 : ℝ)) →
      (∀ x ∈ Ioc 0 R, |deriv f x| ≤ K * x ^ (-δ)) ∧
      IntervalIntegrable (deriv f) volume 0 R ∧
      (∫ x in (0 : ℝ)..R, |deriv f x|) ≤ K * R ^ (1 - δ) / (1 - δ) := by
  obtain ⟨K, hK, hb⟩ := uniform_deriv_integral_bound_halfInterval hδ hδ1 hC hM hR
  refine ⟨K, hK, fun f hf hq hMf hbound => hb f hf hq hMf ?_⟩
  intro x hx
  exact (hbound x hx).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hx.1 (hx.2.trans hR1) (by linarith)) hC)

end Riesz1.PuncturedDerivative
