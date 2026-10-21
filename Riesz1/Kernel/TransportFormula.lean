/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportSums
public import Riesz1.Kernel.TransportConstants
public import Riesz1.Kernel.TransportSeries
public import Riesz1.Frozen.TransportCoeffs

/-!
# The pointwise transport formula on the unit circle

For `0 < s < 1`, `β > 0` and a real smooth `ξ` on the unit circle, the transport `ψ` of `ξ`
(coefficients `transportCoeffs`) is smooth, has the transport coefficients,
and satisfies, for every `x`,

`ψ(x) = -(4πβ tan(πs/2))⁻¹ ∑_k ∫_0^1 (ξ(y) - ∫ξ) sgn(x-y-k)|x-y-k|^{s-1} dy`

The proof writes `ψ` as a multiple of the fractional Laplacian
`(-Δ)^{(1-s)/2}` of the mean-zero primitive `Ξ` of `ξ`. The singular integral formula
`fracLapSeries_singular` then turns it into an integral against `(Ξ(x) - Ξ(y))|x-y-k|^{s-2}`,
and the integration by parts of `TransportSingular` converts that into the claimed kernel.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology Complex
open scoped ContDiff Real

namespace Riesz1

/-- A smooth function on the unit circle is continuous. -/
lemma continuous_of_isSmoothCircle {ξ : UnitAddCircle → ℝ} (hξ : IsSmoothCircle ξ) :
    Continuous ξ :=
  (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_lift hξ)

/-- A function on the unit circle, read as a function on the circle `Circle unitLength`
(the same circle, with the length `unitLength.val = 1` unfolded). -/
noncomputable def unitFun (ξ : UnitAddCircle → ℝ) : Circle unitLength → ℝ :=
  fun z => ξ (show UnitAddCircle from z)

/-- A smooth real function on the unit circle, viewed as a complex `L²` class on the circle of
length one (`arclength unitLength`). -/
lemma memLp_of_isSmoothCircle {ξ : UnitAddCircle → ℝ} (hξ : IsSmoothCircle ξ) :
    MemLp (fun z : Circle unitLength => (unitFun ξ z : ℂ)) 2 (arclength unitLength) := by
  have : Fact (0 < unitLength.val) := ⟨unitLength.property⟩
  have : IsFiniteMeasure (arclength unitLength) := by
    unfold arclength
    infer_instance
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := ξ) (continuous_of_isSmoothCircle hξ).continuousOn
  refine MemLp.of_bound ?_ C (Eventually.of_forall fun z => ?_)
  · exact (Complex.continuous_ofReal.comp
      (continuous_of_isSmoothCircle hξ : Continuous fun z : Circle unitLength =>
        ξ (show UnitAddCircle from z))).aestronglyMeasurable
  · rw [Complex.norm_real]
    exact hC (show UnitAddCircle from z) (mem_univ _)

/-- The multiplier of the transport on the unit circle: the fractional Laplacian coefficient of
the primitive at exponent `(1 - s)/2` (through `Ξ' = ξ - ∫ξ`). -/
noncomputable def primitiveCoeff {ξ : UnitAddCircle → ℝ} (hξ : IsSmoothCircle ξ) (s : ℝ)
    (k : ℤ) : ℂ :=
  fractionalLaplacianCoeffs unitLength ((1 - s) / 2) (circleCoeff (circlePrimitive hξ)) k

/-- The multiplier vanishes at frequency zero. -/
lemma primitiveCoeff_zero {ξ : UnitAddCircle → ℝ} (hξ : IsSmoothCircle ξ) (s : ℝ) :
    primitiveCoeff hξ s 0 = 0 := by
  unfold primitiveCoeff
  rw [fractionalLaplacianCoeffs_unit]
  simp

/-- The multiplier is the power `|2πk|^{1-s}` times the Fourier coefficient of the primitive,
at every nonzero frequency. -/
lemma primitiveCoeff_eq_mul {ξ : UnitAddCircle → ℝ} (hξ : IsSmoothCircle ξ) (s : ℝ) {k : ℤ}
    (hk : k ≠ 0) :
    primitiveCoeff hξ s k =
      ((|2 * π * (k : ℝ)| ^ (1 - s) : ℝ) : ℂ) * circleCoeff (circlePrimitive hξ) k := by
  unfold primitiveCoeff
  rw [fractionalLaplacianCoeffs_unit, ite_eq_right hk, show 2 * ((1 - s) / 2) = 1 - s by ring]

/-- The Fourier coefficients of the primitive are those of `ξ` divided by `2πik`. -/
lemma circleCoeff_primitive_eq {ξ : UnitAddCircle → ℝ} (hξ : IsSmoothCircle ξ) {k : ℤ}
    (hk : k ≠ 0) :
    circleCoeff (circlePrimitive hξ) k = circleCoeff ξ k / (2 * π * I * (k : ℂ)) := by
  have hkc : (2 * π * I * (k : ℂ)) ≠ 0 := by
    have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
  rw [circleCoeff_eq_mul_primitive hξ hk, mul_div_cancel_left₀ _ hkc]

/-- Decay of the transport multiplier: `|k|^m |a_k| ≤ |2πk|^{m+1}|ξ̂_k|`, so all weighted sums
converge. -/
lemma summable_pow_mul_primitiveCoeff {ξ : UnitAddCircle → ℝ} (hξ : IsSmoothCircle ξ) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (m : ℕ) :
    Summable fun k : ℤ => |(k : ℝ)| ^ m * ‖primitiveCoeff hξ s k‖ := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (summable_norm_two_pi_pow_mul ξ hξ (m + 1))
  by_cases hk : k = 0
  · subst hk; simp [primitiveCoeff_zero]
  · have ha1 : (1 : ℝ) ≤ |2 * π * (k : ℝ)| := by
      have hk' : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
      rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_two]
      nlinarith [Real.two_le_pi]
    have hb : |(k : ℝ)| ≤ |2 * π * (k : ℝ)| := by
      rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_two]
      nlinarith [Real.two_le_pi, abs_nonneg (k : ℝ)]
    have hr : |2 * π * (k : ℝ)| ^ (1 - s) / |2 * π * (k : ℝ)| ≤ 1 := by
      rw [div_le_one (by linarith)]
      calc |2 * π * (k : ℝ)| ^ (1 - s) ≤ |2 * π * (k : ℝ)| ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le ha1 (by linarith)
        _ = |2 * π * (k : ℝ)| := Real.rpow_one _
    have hnorm : ‖((|2 * π * (k : ℝ)| ^ (1 - s) : ℝ) : ℂ) *
        (circleCoeff ξ k / (2 * π * I * (k : ℂ)))‖ =
        |2 * π * (k : ℝ)| ^ (1 - s) / |2 * π * (k : ℝ)| * ‖circleCoeff ξ k‖ := by
      have hk2 : |2 * π * (k : ℝ)| = ‖(2 * π * I * (k : ℂ))‖ := by
        rw [norm_two_pi_I_mul_intCast, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_two]
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg
        (Real.rpow_nonneg (abs_nonneg _) _), ← hk2]
      ring
    rw [primitiveCoeff_eq_mul hξ s hk, circleCoeff_primitive_eq hξ hk, hnorm]
    have hN : 0 ≤ ‖circleCoeff ξ k‖ := norm_nonneg _
    have hbm : |(k : ℝ)| ^ m ≤ |2 * π * (k : ℝ)| ^ m := pow_le_pow_left₀ (abs_nonneg _) hb m
    have hpm : |2 * π * (k : ℝ)| ^ m ≤ |2 * π * (k : ℝ)| ^ (m + 1) :=
      pow_le_pow_right₀ ha1 (Nat.le_succ m)
    have hpos : 0 ≤ |2 * π * (k : ℝ)| ^ (1 - s) / |2 * π * (k : ℝ)| :=
      div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (abs_nonneg _)
    calc |(k : ℝ)| ^ m * (|2 * π * (k : ℝ)| ^ (1 - s) / |2 * π * (k : ℝ)| * ‖circleCoeff ξ k‖)
        ≤ |2 * π * (k : ℝ)| ^ m * (1 * ‖circleCoeff ξ k‖) := by
          apply mul_le_mul (hbm.trans' le_rfl) _ (mul_nonneg hpos hN) (by positivity)
          exact mul_le_mul hr le_rfl hN zero_le_one
      _ ≤ |2 * π * (k : ℝ)| ^ (m + 1) * ‖circleCoeff ξ k‖ := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_right hpm hN

/-- The Fourier series of the multiplier, evaluated on the circle. -/
noncomputable def primitiveSeries {ξ : UnitAddCircle → ℝ} (hξ : IsSmoothCircle ξ) (s : ℝ)
    (z : UnitAddCircle) : ℂ :=
  ∑' k : ℤ, primitiveCoeff hξ s k * fourier k z

/-- The singular integral formula for the primitive series: the terms
`∫_0^1 (Ξ(x) - Ξ(t))/|x - t - n|^{2-s} dt` are summable over `n ∈ ℤ`, and the series is their
real sum multiplied by `C_{(1-s)/2}`. -/
lemma primitiveSeries_singular {ξ : UnitAddCircle → ℝ} (hξ : IsSmoothCircle ξ) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ) :
    Summable (fun n : ℤ => ∫ t in (0 : ℝ)..1,
      (meanZeroPrimitive ξ x - meanZeroPrimitive ξ t) / |x - t - n| ^ (2 - s)) ∧
    primitiveSeries hξ s (x : UnitAddCircle) = ((singularConst ((1 - s) / 2) *
      ∑' n : ℤ, ∫ t in (0 : ℝ)..1,
        (meanZeroPrimitive ξ x - meanZeroPrimitive ξ t) / |x - t - n| ^ (2 - s) : ℝ) : ℂ) := by
  have hγ0 : 0 < (1 - s) / 2 := by linarith
  have hγ1 : (1 - s) / 2 < 1 / 2 := by linarith
  obtain ⟨h1, h2⟩ := fracLapSeries_singular hγ0 hγ1 (circlePrimitive hξ)
    (isSmoothCircle_circlePrimitive hξ) x
  simp only [circlePrimitive_coe] at h1 h2
  rw [show 1 + 2 * ((1 - s) / 2) = 2 - s by ring] at h1 h2
  refine ⟨?_, h2⟩
  refine Summable.of_norm_bounded h1 (fun n => ?_)
  exact intervalIntegral.norm_integral_le_integral_norm zero_le_one

/-- The primitive series is real-valued at every point of the circle. -/
lemma primitiveSeries_eq_ofReal {ξ : UnitAddCircle → ℝ} (hξ : IsSmoothCircle ξ) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (z : UnitAddCircle) :
    ∃ r : ℝ, primitiveSeries hξ s z = (r : ℂ) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  exact ⟨_, (primitiveSeries_singular hξ hs0 hs1 x).2⟩

/-- The transport constant is positive. -/
lemma rieszConstant_parametersExponent_pos (P : Parameters) :
    0 < rieszConstant (parametersExponent P) := by
  have hE0 : 0 < (parametersExponent P).val := (parametersExponent P).2.1
  have hE1 : (parametersExponent P).val < 1 := (parametersExponent P).2.2
  unfold rieszConstant
  exact div_pos (mul_pos (mul_pos (by positivity) (Real.sqrt_pos.2 Real.pi_pos))
    (Real.Gamma_pos_of_pos (by linarith))) (Real.Gamma_pos_of_pos (by linarith))

/-- The transport coefficients of `ξ` are those of the real function
`-(2βc_s)^{-1} · primitiveSeries`. -/
lemma transportCoeffs_eq_mul {ξ : UnitAddCircle → ℝ} (hξ : IsSmoothCircle ξ) (P : Parameters)
    (k : ℤ) :
    transportCoeffs P unitLength ⟨unitFun ξ, memLp_of_isSmoothCircle hξ⟩ k =
      ((-(1 / (2 * P.val.1 * rieszConstant (parametersExponent P))) : ℝ) : ℂ) *
        primitiveCoeff hξ P.val.2 k := by
  by_cases hk : k = 0
  · subst hk
    unfold transportCoeffs
    rw [primitiveCoeff_zero]
    simp
  · have hkc : (2 * π * I * (k : ℂ)) ≠ 0 := by
      have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
    have hβc : (2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero P.property.1.ne')
        (rieszConstant_parametersExponent_pos P).ne'
    unfold transportCoeffs
    rw [ite_eq_right hk]
    show -((|2 * π * (k : ℝ) / 1| ^ (1 - P.val.2) : ℝ) : ℂ) /
        ((2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) * (2 * π * I * (k : ℂ) / 1)) *
        circleCoeff ξ k =
      ((-(1 / (2 * P.val.1 * rieszConstant (parametersExponent P))) : ℝ) : ℂ) *
        primitiveCoeff hξ P.val.2 k
    rw [primitiveCoeff_eq_mul hξ P.val.2 hk, circleCoeff_eq_mul_primitive hξ hk, div_one, div_one]
    push_cast
    field_simp

/-- **Pointwise transport formula.** For `0 < s < 1`, `β > 0` and a
real smooth `ξ` on the unit circle, there is a smooth `ψ` on the circle with the transport
coefficients of `ξ`, and for every real `x` the kernel series
`∑_k ∫_0^1 (ξ(y) - ∫ξ) sgn(x-y-k)|x-y-k|^{s-1} dy` is absolutely summable with
`ψ(x) = -(4πβ tan(πs/2))^{-1} ∑_k ∫_0^1 (ξ(y) - ∫ξ) sgn(x-y-k)|x-y-k|^{s-1} dy`. -/
theorem transport_pointwise_formula (P : Parameters) (ξ : UnitAddCircle → ℝ)
    (hξ : IsSmoothCircle ξ) :
    ∃ ψ : UnitAddCircle → ℝ, IsSmoothCircle ψ ∧
      (∀ k : ℤ, circleCoeff ψ k =
        transportCoeffs P unitLength ⟨unitFun ξ, memLp_of_isSmoothCircle hξ⟩ k) ∧
      ∀ x : ℝ,
        Summable (fun k : ℤ => ∫ y in (0 : ℝ)..1,
          (ξ (y : UnitAddCircle) - circleMean ξ) * signPow P.val.2 (x - y - k)) ∧
        ψ (x : UnitAddCircle) = -(1 / (4 * π * P.val.1 * Real.tan (π * P.val.2 / 2))) *
          ∑' k : ℤ, ∫ y in (0 : ℝ)..1,
            (ξ (y : UnitAddCircle) - circleMean ξ) * signPow P.val.2 (x - y - k) := by
  have hβ : 0 < P.val.1 := P.property.1
  have hs0 : 0 < P.val.2 := P.property.2.1
  have hs1 : P.val.2 < 1 := P.property.2.2
  have hc_pos := rieszConstant_parametersExponent_pos P
  obtain ⟨M, hM⟩ := exists_bound_centered hξ
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = -(1 / (2 * P.val.1 * rieszConstant (parametersExponent P))) :=
    ⟨_, rfl⟩
  have hsum0 : Summable fun j : ℤ => ‖primitiveCoeff hξ P.val.2 j‖ := by
    simpa using summable_pow_mul_primitiveCoeff hξ hs0 hs1 0
  have hG := contDiff_fourierSeries (fun m => summable_pow_mul_primitiveCoeff hξ hs0 hs1 m)
  refine ⟨fun z => ((A : ℂ) * primitiveSeries hξ P.val.2 z).re, ?_, ?_, ?_⟩
  · unfold IsSmoothCircle
    exact Complex.reCLM.contDiff.comp (contDiff_const.mul hG)
  · intro k
    have hcoe : (fun z : UnitAddCircle => (((A : ℂ) * primitiveSeries hξ P.val.2 z).re : ℂ)) =
        fun z => (A : ℂ) * primitiveSeries hξ P.val.2 z := by
      funext z
      obtain ⟨r, hr⟩ := primitiveSeries_eq_ofReal hξ hs0 hs1 z
      rw [hr, Complex.re_ofReal_mul, Complex.ofReal_re]
      push_cast
      ring
    unfold circleCoeff
    rw [hcoe, fourierCoeff.const_mul]
    change (A : ℂ) * fourierCoeff (fun z : UnitAddCircle =>
      ∑' j : ℤ, primitiveCoeff hξ P.val.2 j * fourier j z) k = _
    rw [fourierCoeff_fourierSeries hsum0 k, transportCoeffs_eq_mul hξ P k, hA]
  · intro x
    obtain ⟨hJsum, hval⟩ := primitiveSeries_singular hξ hs0 hs1 x
    refine ⟨summable_centered_signPow hs0 hs1 (ξ' := fun t : ℝ => ξ (t : UnitAddCircle) -
      circleMean ξ) (continuous_centered hξ) hM (integral_centered_eq_zero hξ), ?_⟩
    have hid := sum_singular_eq_sum_centered hs0 hs1
      (Ξ := meanZeroPrimitive ξ) (ξ' := fun t : ℝ => ξ (t : UnitAddCircle) - circleMean ξ)
      (fun t => meanZeroPrimitive_hasDerivAt hξ t) (continuous_centered hξ) hM
      (meanZeroPrimitive_periodic hξ) (integral_centered_eq_zero hξ) hJsum
    beta_reduce at hid
    have hC : singularConst ((1 - P.val.2) / 2) = rieszConstant (parametersExponent P) *
        (1 - P.val.2) / (2 * π * Real.tan (π * P.val.2 / 2)) :=
      singularConst_half_eq P.val.2 hs0 hs1
    have htan : 0 < Real.tan (π * P.val.2 / 2) :=
      Real.tan_pos_of_pos_of_lt_pi_div_two (by positivity) (by nlinarith [Real.pi_pos])
    show ((A : ℂ) * primitiveSeries hξ P.val.2 (x : UnitAddCircle)).re = _
    rw [hval, Complex.re_ofReal_mul, Complex.ofReal_re, hC, ← hid, hA]
    have hβ := P.property.1
    have hc := hc_pos
    field_simp
    ring

end Riesz1
