/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HeatKernel.Operators
public import Riesz1.ToMathlib.HeatKernel.Semigroup

/-!
# Time-integral formulas for fractional Laplacians on the unit circle

For a smooth function `f` on the unit circle and `0 < γ < 1`, the two semigroup formulas of
Lemma 2.1 hold pointwise:

* for mean-zero `f`, `(-Δ)^{-γ} f(x) = Γ(γ)⁻¹ ∫_0^∞ (f ∗ W_t)(x) t^{γ-1} dt`.
* for every smooth `f`, `(-Δ)^γ f(x) = γ/Γ(1-γ) ∫_0^∞ (f(x) - (f ∗ W_t)(x)) t^{-1-γ} dt`.

The time integrals run over the subtype `Ioi 0` with its measure `Measure.comap Subtype.val
volume`, so the heat kernel `W_t` only ever sees a positive time. The proofs expand `f ∗ W_t` in
its Fourier series (from `Operators`), interchange the series with the time integral by the
dominated convergence theorem for series, and evaluate each term by the Gamma integrals of
`Semigroup`.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology
open scoped ContDiff Real

namespace Riesz1

open Complex (I)

/-- A time integral over the subtype `Ioi 0` equals the set integral of any function `Φ` of time
that agrees with the integrand at every positive time. -/
lemma integral_subtype_Ioi_eq (G : (t : ℝ) → 0 < t → ℂ) (Φ : ℝ → ℂ)
    (h : ∀ (t : ℝ) (ht : 0 < t), G t ht = Φ t) :
    ∫ t, G t.1 t.2 ∂(Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) volume) =
      ∫ t in Ioi (0 : ℝ), Φ t := by
  rw [← MeasureTheory.integral_subtype_comap measurableSet_Ioi Φ]
  congr 1
  funext t
  exact h t.1 t.2

/-- The identity `|a|^{2s} = (a^2)^s` for real exponents. -/
lemma abs_rpow_two_mul_eq (a s : ℝ) : |a| ^ (2 * s) = (a ^ 2) ^ s := by
  rw [Real.rpow_mul (abs_nonneg a), Real.rpow_two, sq_abs]

/-- The heat exponential, with the square factored as a multiplier of `t`. -/
lemma heat_exp_eq (k : ℤ) (t : ℝ) :
    Real.exp (-4 * π ^ 2 * (k : ℝ) ^ 2 * t) = Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t) := by
  congr 1
  ring

/-- The Gamma integral of a heat exponential: for `k ≠ 0`,
`∫_0^∞ e^{-4π²k²t} t^{γ-1} dt = Γ(γ) |2πk|^{-2γ}`. -/
lemma integral_heat_rpow {γ : ℝ} (hγ : 0 < γ) (k : ℤ) (hk : k ≠ 0) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t) * t ^ (γ - 1) =
      Real.Gamma γ * |2 * π * (k : ℝ)| ^ (2 * (-γ)) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hlam : 0 < 4 * π ^ 2 * (k : ℝ) ^ 2 := by positivity
  have h := rpow_neg_eq_gamma_inv_mul_integral hγ hlam
  have hΓ : Real.Gamma γ ≠ 0 := (Real.Gamma_pos_of_pos hγ).ne'
  have hpow : |2 * π * (k : ℝ)| ^ (2 * (-γ)) = (4 * π ^ 2 * (k : ℝ) ^ 2) ^ (-γ) := by
    rw [abs_rpow_two_mul_eq]
    congr 1
    ring
  rw [hpow, h, ← mul_assoc, mul_inv_cancel₀ hΓ, one_mul]

/-- The Gamma integral of a one-minus-heat factor: for `k ≠ 0`,
`∫_0^∞ (1 - e^{-4π²k²t}) t^{-1-γ} dt = |2πk|^{2γ} Γ(1-γ) / γ`. -/
lemma integral_heat_one_sub {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) (k : ℤ) (hk : k ≠ 0) :
    ∫ t in Ioi (0 : ℝ), (1 - Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t)) * t ^ (-1 - γ) =
      |2 * π * (k : ℝ)| ^ (2 * γ) * Real.Gamma (1 - γ) / γ := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hlam : 0 < 4 * π ^ 2 * (k : ℝ) ^ 2 := by positivity
  have h := integral_one_sub_exp_mul_rpow_neg_one_sub hγ hγ1 hlam
  have hpow : |2 * π * (k : ℝ)| ^ (2 * γ) = (4 * π ^ 2 * (k : ℝ) ^ 2) ^ γ := by
    rw [abs_rpow_two_mul_eq]
    congr 1
    ring
  rw [hpow]
  exact h

/-- The norm of a complex factor times a nonnegative real weight, integrated over `Ioi 0`. -/
lemma integral_norm_mul_real (c : ℂ) (φ : ℝ → ℝ) (hφ : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ φ t) :
    ∫ t in Ioi (0 : ℝ), ‖c * ((φ t : ℝ) : ℂ)‖ = ‖c‖ * ∫ t in Ioi (0 : ℝ), φ t := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hφ t ht)]

/-- Fourier inversion for a smooth function on the unit circle, at a real point. -/
lemma hasSum_circleCoeff (f : UnitAddCircle → ℝ) (hf : IsSmoothCircle f) (x : ℝ) :
    HasSum (fun k : ℤ => fourier k (x : UnitAddCircle) * circleCoeff f k)
      ((f (x : UnitAddCircle) : ℝ) : ℂ) := by
  have hcont : Continuous fun z : UnitAddCircle => ((f z : ℝ) : ℂ) := by
    refine (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 ?_
    exact Complex.continuous_ofReal.comp
      (show ContDiff ℝ ∞ (fun u : ℝ => f (u : UnitAddCircle)) from hf).continuous
  let g : C(UnitAddCircle, ℂ) := ⟨fun z => ((f z : ℝ) : ℂ), hcont⟩
  have h0 : Summable fun k : ℤ => ‖circleCoeff f k‖ := by
    simpa only [pow_zero, one_mul] using summable_norm_two_pi_pow_mul f hf 0
  have hsum : Summable (fourierCoeff (⇑g)) := Summable.of_norm h0
  have h := has_pointwise_sum_fourier_series_of_summable hsum (x : UnitAddCircle)
  convert h using 1
  funext k
  rw [smul_eq_mul, mul_comm]
  rfl

/-- Negative-power formula: for mean-zero smooth `f` and `0 < γ < 1`,
`(-Δ)^{-γ} f(x) = Γ(γ)⁻¹ ∫_0^∞ (f ∗ W_t)(x) t^{γ-1} dt`. -/
theorem fracLapSeries_neg_eq_heat {γ : ℝ} (hγ0 : 0 < γ) (_hγ1 : γ < 1) (f : UnitAddCircle → ℝ)
    (hf : IsSmoothCircle f) (hmean : ∫ x : UnitAddCircle, f x = 0) (x : ℝ) :
    fracLapSeries (-γ) f hf x =
      (((Real.Gamma γ)⁻¹ * ∫ t, heatConvolution f t.2 x * (t : ℝ) ^ (γ - 1)
        ∂(Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) volume) : ℝ) : ℂ) := by
  have hc0 : circleCoeff f 0 = 0 := by rw [circleCoeff_zero, hmean, Complex.ofReal_zero]
  have hΦ : ∀ (t : ℝ) (ht : 0 < t),
      (((heatConvolution f ht x * t ^ (γ - 1) : ℝ)) : ℂ) =
        ∑' k : ℤ, (fourier k (x : UnitAddCircle) * circleCoeff f k) *
          (((Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t) * t ^ (γ - 1) : ℝ)) : ℂ) := by
    intro t ht
    rw [Complex.ofReal_mul, ← (hasSum_heatConvolution f hf ht x).tsum_eq, ← tsum_mul_right]
    refine tsum_congr fun k => ?_
    rw [heat_exp_eq]
    push_cast
    ring
  have hsub : ∫ t, (((heatConvolution f t.2 x * (t : ℝ) ^ (γ - 1)) : ℝ) : ℂ)
      ∂(Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) volume) =
      ∫ t in Ioi (0 : ℝ), ∑' k : ℤ, (fourier k (x : UnitAddCircle) * circleCoeff f k) *
          (((Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t) * t ^ (γ - 1) : ℝ)) : ℂ) :=
    integral_subtype_Ioi_eq (fun (t : ℝ) (ht : 0 < t) =>
      (((heatConvolution f ht x * t ^ (γ - 1) : ℝ)) : ℂ)) _ hΦ
  have hnorm : ∀ k : ℤ, ∫ t in Ioi (0 : ℝ),
      ‖(fourier k (x : UnitAddCircle) * circleCoeff f k) *
        (((Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t) * t ^ (γ - 1) : ℝ)) : ℂ)‖ =
      Real.Gamma γ * ‖fractionalLaplacianCoeffs unitLength (-γ) (circleCoeff f) k‖ := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp [hc0, fractionalLaplacianCoeffs_unit]
    · have hnn : ∀ t ∈ Ioi (0 : ℝ),
          0 ≤ Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t) * t ^ (γ - 1) :=
        fun t ht => mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt ht) _)
      rw [integral_norm_mul_real _ _ hnn, norm_mul, norm_fourier_coe, one_mul,
        integral_heat_rpow hγ0 k hk, fractionalLaplacianCoeffs_unit, ite_eq_right hk, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      ring
  have hint : ∀ k : ℤ, Integrable (fun t : ℝ =>
      (fourier k (x : UnitAddCircle) * circleCoeff f k) *
        (((Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t) * t ^ (γ - 1) : ℝ)) : ℂ))
      (volume.restrict (Ioi 0)) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp [hc0]
    · have hlam : 0 < 4 * π ^ 2 * (k : ℝ) ^ 2 := by
        have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
        positivity
      exact (Integrable.ofReal (integrableOn_exp_mul_rpow_sub_one hγ0 hlam)).const_mul _
  have hsumm : Summable fun k : ℤ => ∫ t in Ioi (0 : ℝ),
      ‖(fourier k (x : UnitAddCircle) * circleCoeff f k) *
        (((Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t) * t ^ (γ - 1) : ℝ)) : ℂ)‖ := by
    simp only [hnorm]
    exact (summable_norm_fracLapCoeff (-γ) f hf).mul_left _
  have hval : ∀ k : ℤ, ∫ t in Ioi (0 : ℝ),
      (fourier k (x : UnitAddCircle) * circleCoeff f k) *
        (((Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t) * t ^ (γ - 1) : ℝ)) : ℂ) =
      (fourier k (x : UnitAddCircle) * circleCoeff f k) *
        (((Real.Gamma γ * |2 * π * (k : ℝ)| ^ (2 * (-γ)) : ℝ)) : ℂ) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp [hc0]
    · rw [MeasureTheory.integral_const_mul, integral_complex_ofReal,
        integral_heat_rpow hγ0 k hk]
  have hΓ : (Real.Gamma γ : ℂ) ≠ 0 := by exact_mod_cast (Real.Gamma_pos_of_pos hγ0).ne'
  unfold fracLapSeries
  rw [Complex.ofReal_mul, ← integral_complex_ofReal, hsub,
    ← MeasureTheory.integral_tsum_of_summable_integral_norm hint hsumm]
  simp only [hval]
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp [hc0, fractionalLaplacianCoeffs_unit]
  · rw [fractionalLaplacianCoeffs_unit, ite_eq_right hk]
    push_cast
    field_simp

/-- Positive-power formula: for smooth `f` and `0 < γ < 1`,
`(-Δ)^γ f(x) = γ/Γ(1-γ) ∫_0^∞ (f(x) - (f ∗ W_t)(x)) t^{-1-γ} dt`. -/
theorem fracLapSeries_eq_heat {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (f : UnitAddCircle → ℝ)
    (hf : IsSmoothCircle f) (x : ℝ) :
    fracLapSeries γ f hf x =
      (((γ / Real.Gamma (1 - γ)) * ∫ t, (f (x : UnitAddCircle) - heatConvolution f t.2 x) *
        (t : ℝ) ^ (-1 - γ) ∂(Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) volume) : ℝ) : ℂ) := by
  have hz : (2 * γ) ≠ 0 := (mul_pos two_pos hγ0).ne'
  have hΦ : ∀ (t : ℝ) (ht : 0 < t),
      ((((f (x : UnitAddCircle) - heatConvolution f ht x) * t ^ (-1 - γ) : ℝ)) : ℂ) =
        ∑' k : ℤ, (fourier k (x : UnitAddCircle) * circleCoeff f k) *
          (((1 - Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t)) * t ^ (-1 - γ) : ℝ) : ℂ) := by
    intro t ht
    have h3 := ((hasSum_circleCoeff f hf x).sub (hasSum_heatConvolution f hf ht x)).mul_right
      ((t ^ (-1 - γ) : ℝ) : ℂ)
    refine (HasSum.tsum_eq ?_).symm
    convert h3 using 1
    · funext k
      rw [heat_exp_eq]
      push_cast
      ring
    · push_cast
      ring
  have hsub : ∫ t, ((((f (x : UnitAddCircle) - heatConvolution f t.2 x) *
        (t : ℝ) ^ (-1 - γ) : ℝ)) : ℂ)
      ∂(Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) volume) =
      ∫ t in Ioi (0 : ℝ), ∑' k : ℤ, (fourier k (x : UnitAddCircle) * circleCoeff f k) *
          (((1 - Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t)) * t ^ (-1 - γ) : ℝ) : ℂ) :=
    integral_subtype_Ioi_eq (fun (t : ℝ) (ht : 0 < t) =>
      ((((f (x : UnitAddCircle) - heatConvolution f ht x) * t ^ (-1 - γ) : ℝ)) : ℂ)) _ hΦ
  have hnorm : ∀ k : ℤ, ∫ t in Ioi (0 : ℝ),
      ‖(fourier k (x : UnitAddCircle) * circleCoeff f k) *
        (((1 - Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t)) * t ^ (-1 - γ) : ℝ) : ℂ)‖ =
      (Real.Gamma (1 - γ) / γ) * ‖fractionalLaplacianCoeffs unitLength γ (circleCoeff f) k‖ := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp [fractionalLaplacianCoeffs_unit]
    · have hlam : 0 < 4 * π ^ 2 * (k : ℝ) ^ 2 := by
        have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
        positivity
      have hnn : ∀ t ∈ Ioi (0 : ℝ),
          0 ≤ (1 - Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t)) * t ^ (-1 - γ) :=
        fun t ht => mul_nonneg (one_sub_exp_nonneg hlam (Set.mem_Ioi.1 ht))
          (Real.rpow_nonneg (le_of_lt (Set.mem_Ioi.1 ht)) _)
      rw [integral_norm_mul_real _ _ hnn, norm_mul, norm_fourier_coe, one_mul,
        integral_heat_one_sub hγ0 hγ1 k hk, fractionalLaplacianCoeffs_unit, ite_eq_right hk, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      ring
  have hint : ∀ k : ℤ, Integrable (fun t : ℝ =>
      (fourier k (x : UnitAddCircle) * circleCoeff f k) *
        (((1 - Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t)) * t ^ (-1 - γ) : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp
    · have hlam : 0 < 4 * π ^ 2 * (k : ℝ) ^ 2 := by
        have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
        positivity
      exact (Integrable.ofReal
        (integrableOn_one_sub_exp_mul_rpow_neg_one_sub hγ0 hγ1 hlam)).const_mul _
  have hsumm : Summable fun k : ℤ => ∫ t in Ioi (0 : ℝ),
      ‖(fourier k (x : UnitAddCircle) * circleCoeff f k) *
        (((1 - Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t)) * t ^ (-1 - γ) : ℝ) : ℂ)‖ := by
    simp only [hnorm]
    exact (summable_norm_fracLapCoeff γ f hf).mul_left _
  have hval : ∀ k : ℤ, ∫ t in Ioi (0 : ℝ),
      (fourier k (x : UnitAddCircle) * circleCoeff f k) *
        (((1 - Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t)) * t ^ (-1 - γ) : ℝ) : ℂ) =
      (fourier k (x : UnitAddCircle) * circleCoeff f k) *
        (((|2 * π * (k : ℝ)| ^ (2 * γ) * Real.Gamma (1 - γ) / γ : ℝ)) : ℂ) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp [Real.zero_rpow hz]
    · rw [MeasureTheory.integral_const_mul, integral_complex_ofReal,
        integral_heat_one_sub hγ0 hγ1 k hk]
  have hΓ : (Real.Gamma (1 - γ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ0.ne'
  unfold fracLapSeries
  rw [Complex.ofReal_mul, ← integral_complex_ofReal, hsub,
    ← MeasureTheory.integral_tsum_of_summable_integral_norm hint hsumm]
  simp only [hval]
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp [fractionalLaplacianCoeffs_unit, Real.zero_rpow hz]
  · rw [fractionalLaplacianCoeffs_unit, ite_eq_right hk]
    push_cast
    field_simp

end Riesz1

end
