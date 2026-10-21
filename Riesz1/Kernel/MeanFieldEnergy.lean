/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.MeanFieldEnergyAlgebra
public import Riesz1.Kernel.MeanFieldEnergyFubini
public import Riesz1.Kernel.MeanFieldEnergyKernel
public import Riesz1.Kernel.MeanFieldEnergySeries
public import Riesz1.Kernel.Coefficients
public import Riesz1.Frozen.CircleSobolevSq
public import Riesz1.Frozen.RieszRepresentative

/-!
# The mean-field energy identity

For `0 < s < 1`, `β > 0` and a smooth real `ξ` on the circle with
transport `ψ` (the `L²` class with the coefficients `transportCoeffs`), the double integral
`∬ g''(x - y) (ψ x - ψ y)² dx dy` is absolutely convergent, and

`(2π)^{1-s} / (2βc_s) ‖ξ‖²_{H^{(1-s)/2}} = -β ∬ g''(x-y)(ψ x - ψ y)² + 2 ∫ ξ' ψ = ∫ ξ' ψ`.

The proof assembles the Fubini identity `MeanFieldEnergyFubini`, the integration by parts
`MeanFieldEnergyKernel`, the trigonometric series `MeanFieldEnergySeries` (the translation
autocorrelation of `ψ`), and the coefficient algebra `MeanFieldEnergyAlgebra`.
-/

public section

open MeasureTheory Set Complex Filter Topology
open scoped Real ComplexConjugate ENNReal ContDiff

namespace Riesz1

/-- The Riesz kernel is interval integrable on `[0, 1]` as a function of a real variable. -/
lemma intervalIntegrable_riesz (s : RieszExponent) :
    IntervalIntegrable (fun x : ℝ => rieszRepresentative s (x : UnitAddCircle)) volume 0 1 :=
  intervalIntegrable_hurwitzKernel s.val s.property.1 s.property.2

/-- The cosine integral of the Riesz kernel is its Fourier coefficient. -/
lemma integral_cos_mul_riesz (s : RieszExponent) (k : ℤ) :
    ∫ x in (0 : ℝ)..1, rieszRepresentative s (x : UnitAddCircle) * Real.cos (2 * π * k * x) =
      if k = 0 then 0 else rieszConstant s * (2 * π * |(k : ℝ)|) ^ ((s : ℝ) - 1) := by
  have h1 := fourierCoeff_rieszRepresentative s k
  rw [fourierCoeff_eq_lineCoeff] at h1
  unfold lineCoeff at h1
  have hG : IntervalIntegrable
      (fun x : ℝ => ((rieszRepresentative s (x : UnitAddCircle) : ℝ) : ℂ)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegrable_riesz s)).ofReal
  have hIoc : IntegrableOn (fun x : ℝ => cexp (-(2 * π * I * k * x)) *
      ((rieszRepresentative s (x : UnitAddCircle) : ℝ) : ℂ)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (intervalIntegrable_exp_mul hG k)
  have hre : (∫ x in (0 : ℝ)..1, cexp (-(2 * π * I * k * x)) *
      ((rieszRepresentative s (x : UnitAddCircle) : ℝ) : ℂ)).re =
      ∫ x in (0 : ℝ)..1, rieszRepresentative s (x : UnitAddCircle) * Real.cos (2 * π * k * x) := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    have := integral_re hIoc
    simp only [RCLike.re_to_complex] at this
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.exp_re]
    have hz : (-(2 * π * I * k * x) : ℂ).re = 0 := by simp
    have hzi : (-(2 * π * I * k * x) : ℂ).im = -(2 * π * k * x) := by simp
    rw [hz, hzi, Real.exp_zero, one_mul, Real.cos_neg]
    ring
  have h2 := congrArg Complex.re h1
  rw [hre] at h2
  rw [h2]
  split_ifs <;> simp

/-- Termwise integration of the kernel against the second derivative series. -/
lemma integral_mul_energySeries2 (s : RieszExponent) {a : ℤ → ℝ} (ha0 : ∀ k, 0 ≤ a k)
    (hM : Summable fun k : ℤ => (k : ℝ) ^ 2 * a k) :
    ∫ x in (0 : ℝ)..1, rieszRepresentative s (x : UnitAddCircle) * energySeries2 a x =
      ∑' k : ℤ, (a k * (8 * π ^ 2 * (k : ℝ) ^ 2)) *
        (if k = 0 then 0 else rieszConstant s * (2 * π * |(k : ℝ)|) ^ ((s : ℝ) - 1)) := by
  have hGi := intervalIntegrable_riesz s
  have hGabs : IntegrableOn (fun x : ℝ => |rieszRepresentative s (x : UnitAddCircle)|) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hGi.abs
  have hsum_eq : ∀ x : ℝ, rieszRepresentative s (x : UnitAddCircle) * energySeries2 a x =
      ∑' k : ℤ, (a k * (8 * π ^ 2 * (k : ℝ) ^ 2)) *
        (rieszRepresentative s (x : UnitAddCircle) * Real.cos (2 * π * k * x)) := by
    intro x
    simp only [energySeries2]
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    ring
  have hterm_ii : ∀ k : ℤ, IntervalIntegrable (fun x : ℝ =>
      (a k * (8 * π ^ 2 * (k : ℝ) ^ 2)) *
        (rieszRepresentative s (x : UnitAddCircle) * Real.cos (2 * π * k * x))) volume 0 1 := by
    intro k
    refine IntervalIntegrable.const_mul ?_ _
    exact hGi.mul_continuousOn
      (by fun_prop : Continuous fun x : ℝ => Real.cos (2 * π * k * x)).continuousOn
  have hterm_int : ∀ k : ℤ, Integrable (fun x : ℝ =>
      (a k * (8 * π ^ 2 * (k : ℝ) ^ 2)) *
        (rieszRepresentative s (x : UnitAddCircle) * Real.cos (2 * π * k * x)))
        (volume.restrict (Ioc 0 1)) :=
    fun k => (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (hterm_ii k)
  have hsumm : Summable fun k : ℤ =>
      ∫ x in Ioc (0 : ℝ) 1, ‖(a k * (8 * π ^ 2 * (k : ℝ) ^ 2)) *
        (rieszRepresentative s (x : UnitAddCircle) * Real.cos (2 * π * k * x))‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg _)
      (fun k => ?_) ((hM.mul_left (8 * π ^ 2)).mul_right (∫ x in Ioc (0 : ℝ) 1,
        |rieszRepresentative s (x : UnitAddCircle)|))
    have hc : 0 ≤ a k * (8 * π ^ 2 * (k : ℝ) ^ 2) := mul_nonneg (ha0 k) (by positivity)
    have hbound : ∫ x in Ioc (0 : ℝ) 1, ‖(a k * (8 * π ^ 2 * (k : ℝ) ^ 2)) *
        (rieszRepresentative s (x : UnitAddCircle) * Real.cos (2 * π * k * x))‖ ≤
        ∫ x in Ioc (0 : ℝ) 1, (a k * (8 * π ^ 2 * (k : ℝ) ^ 2)) *
          |rieszRepresentative s (x : UnitAddCircle)| := by
      refine integral_mono (hterm_int k).norm (hGabs.const_mul _) fun x => ?_
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hc, norm_mul, Real.norm_eq_abs,
        Real.norm_eq_abs]
      have hcos : |Real.cos (2 * π * k * x)| ≤ 1 := Real.abs_cos_le_one _
      have habs := abs_nonneg (rieszRepresentative s (x : UnitAddCircle))
      calc (a k * (8 * π ^ 2 * (k : ℝ) ^ 2)) *
            (|rieszRepresentative s (x : UnitAddCircle)| * |Real.cos (2 * π * k * x)|)
          ≤ (a k * (8 * π ^ 2 * (k : ℝ) ^ 2)) * (|rieszRepresentative s (x : UnitAddCircle)| * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcos habs) hc
        _ = _ := by ring
    have hint : ∫ x in Ioc (0 : ℝ) 1, (a k * (8 * π ^ 2 * (k : ℝ) ^ 2)) *
        |rieszRepresentative s (x : UnitAddCircle)| =
        (a k * (8 * π ^ 2 * (k : ℝ) ^ 2)) * ∫ x in Ioc (0 : ℝ) 1,
          |rieszRepresentative s (x : UnitAddCircle)| :=
      integral_const_mul _ _
    rw [hint] at hbound
    linarith [hbound]
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [setIntegral_congr_fun measurableSet_Ioc (fun x _ => hsum_eq x)]
  rw [← integral_tsum_of_summable_integral_norm hterm_int hsumm]
  refine tsum_congr fun k => ?_
  rw [integral_const_mul]
  congr 1
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_cos_mul_riesz]

/-- A continuous complex function is square integrable on one period. -/
lemma memLp_Ioc_of_continuous {f : ℝ → ℂ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hC x ⟨hx.1.le, hx.2⟩

/-- Parseval summability for a smooth one-periodic real profile. -/
lemma summable_sq_lineCoeff_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Summable (fun k : ℤ => ‖lineCoeff (fun x : ℝ => (f x : ℂ)) k‖ ^ 2) :=
  (hasSum_sq_lineCoeff (memLp_Ioc_of_continuous (Complex.continuous_ofReal.comp hf))).summable

/-- The one-periodic lift of a circle function. -/
lemma coe_add_one_eq (t : ℝ) : ((t + 1 : ℝ) : UnitAddCircle) = (t : UnitAddCircle) := by
  simp

/-- The square root of a positive Riesz constant is positive. -/
lemma rieszConstant_pos (s : RieszExponent) : 0 < rieszConstant s := by
  unfold rieszConstant
  have h1 := s.property.2
  have h2 := s.property.1
  have hg1 : 0 < Real.Gamma ((1 - s.val) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hg2 : 0 < Real.Gamma (s.val / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hp : 0 < (2 : ℝ) ^ (1 - s.val) := Real.rpow_pos_of_pos (by norm_num) _
  have hsq : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  positivity

/-- `2π |k| = |2π k|`. -/
lemma two_pi_abs_eq (k : ℤ) : 2 * π * |(k : ℝ)| = |2 * π * (k : ℝ)| := by
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]

/-- The mean-field energy identity for a measurable representative of the transport. -/
theorem energy_identity_of_measurable (P : Parameters) (ξ : Profile)
    (hξ : ContDiff ℝ ∞ (fun t : ℝ => ξ.val (t : UnitAddCircle)))
    (ψ : UnitAddCircle → ℝ) (hψm : Measurable ψ)
    (hψ : MemLp (fun x => (ψ x : ℂ)) 2 volume)
    (hψc : ∀ k : ℤ, fourierCoeff (fun x => (ψ x : ℂ)) k = transportCoeffs P ⟨1, one_pos⟩ ξ k) :
    Integrable (fun p : ℝ × ℝ => deriv (deriv fun t : ℝ =>
        rieszRepresentative (parametersExponent P) (t : UnitAddCircle)) (p.1 - p.2) *
        (ψ (p.1 : UnitAddCircle) - ψ (p.2 : UnitAddCircle)) ^ 2)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) ∧
    circleSobolevSq ((1 - (parametersExponent P).val) / 2) ⟨fun x => (ξ.val x : ℂ), ξ.property⟩ ≠ ⊤ ∧
    (2 * π) ^ (1 - (parametersExponent P).val) /
        (2 * P.val.1 * rieszConstant (parametersExponent P)) *
      (circleSobolevSq ((1 - (parametersExponent P).val) / 2)
        ⟨fun x => (ξ.val x : ℂ), ξ.property⟩).toReal =
      -P.val.1 * (∫ p : ℝ × ℝ, deriv (deriv fun t : ℝ =>
          rieszRepresentative (parametersExponent P) (t : UnitAddCircle)) (p.1 - p.2) *
          (ψ (p.1 : UnitAddCircle) - ψ (p.2 : UnitAddCircle)) ^ 2
        ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1)))) +
        2 * ∫ x in (0 : ℝ)..1, deriv (fun t : ℝ => ξ.val (t : UnitAddCircle)) x *
          ψ (x : UnitAddCircle) ∧
    -P.val.1 * (∫ p : ℝ × ℝ, deriv (deriv fun t : ℝ =>
          rieszRepresentative (parametersExponent P) (t : UnitAddCircle)) (p.1 - p.2) *
          (ψ (p.1 : UnitAddCircle) - ψ (p.2 : UnitAddCircle)) ^ 2
        ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1)))) +
        2 * (∫ x in (0 : ℝ)..1, deriv (fun t : ℝ => ξ.val (t : UnitAddCircle)) x *
          ψ (x : UnitAddCircle)) =
      ∫ x in (0 : ℝ)..1, deriv (fun t : ℝ => ξ.val (t : UnitAddCircle)) x * ψ (x : UnitAddCircle) := by
  set s : RieszExponent := parametersExponent P with hs_def
  have hs0 : 0 < s.val := s.property.1
  have hs1 : s.val < 1 := s.property.2
  have hβ : 0 < P.val.1 := P.property.1
  have hcs : 0 < rieszConstant s := rieszConstant_pos s
  obtain ⟨c, hc⟩ : ∃ c : ℤ → ℂ, ∀ k, c k = fourierCoeff (fun x : UnitAddCircle => (ψ x : ℂ)) k :=
    ⟨_, fun k => rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℤ → ℂ, ∀ k, z k = fourierCoeff (fun x : UnitAddCircle => (ξ.val x : ℂ)) k :=
    ⟨_, fun k => rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ → ℝ, ∀ k, a k = ‖c k‖ ^ 2 := ⟨_, fun k => rfl⟩
  obtain ⟨ξt, hξt⟩ : ∃ f : ℝ → ℝ, ∀ t, f t = ξ.val (t : UnitAddCircle) := ⟨_, fun t => rfl⟩
  have hξt_eq : ξt = fun t : ℝ => ξ.val (t : UnitAddCircle) := funext hξt
  rw [← hξt_eq]
  have ha0 : ∀ k, 0 ≤ a k := fun k => by rw [ha]; positivity
  have hcz : ∀ k : ℤ, k ≠ 0 → c k = -(((|2 * π * (k : ℝ)|) ^ (1 - s.val) : ℝ) : ℂ) /
      (((2 * P.val.1 * rieszConstant s) : ℝ) * (2 * π * I * (k : ℂ))) * z k := by
    intro k hk
    rw [hc, hz, hψc k, transportCoeffs_of_ne P ξ hk]
    rfl
  have hψL : MemLp (fun x : ℝ => (ψ (x : UnitAddCircle) : ℂ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    memLp_Ioc_of_circle hψ
  have hξC : MemLp (fun x : UnitAddCircle => (ξ.val x : ℂ)) 2 volume := ξ.property
  have hsa : Summable (fun k : ℤ => ‖c k‖ ^ 2) := by
    refine (hasSum_sq_lineCoeff hψL).summable.congr fun k => ?_
    rw [hc, fourierCoeff_eq_lineCoeff]
  have hsz : Summable (fun k : ℤ => ‖z k‖ ^ 2) := by
    refine (hasSum_sq_lineCoeff (memLp_Ioc_of_circle hξC)).summable.congr fun k => ?_
    rw [hz, fourierCoeff_eq_lineCoeff]
  have hsa' : Summable a := hsa.congr fun k => (ha k).symm
  have hξt1 : ContDiff ℝ 1 ξt := by rw [hξt_eq]; exact hξ.of_le (by simp)
  have hξt_per : Function.Periodic ξt 1 := fun t => by rw [hξt, hξt, coe_add_one_eq]
  have hz_line : ∀ k : ℤ, z k = lineCoeff (fun x : ℝ => (ξt x : ℂ)) k := by
    intro k
    rw [hz, fourierCoeff_eq_lineCoeff]
    congr 1
    funext x
    rw [hξt]
  have hsu : Summable (fun k : ℤ => ‖2 * π * I * (k : ℂ) * z k‖ ^ 2) := by
    refine (summable_sq_lineCoeff_of_continuous (f := deriv ξt)
      (hξt1.continuous_deriv (by norm_num))).congr fun k => ?_
    rw [lineCoeff_deriv hξt1 hξt_per k, hz_line k]
  -- the second moment and the energy function
  have hM_bound : ∀ k : ℤ, (k : ℝ) ^ 2 * a k ≤
      (‖z k‖ ^ 2 + ‖2 * π * I * (k : ℂ) * z k‖ ^ 2) /
        (4 * π ^ 2 * (2 * P.val.1 * rieszConstant s) ^ 2) := by
    intro k
    by_cases hk : k = 0
    · have h0 : ((k : ℤ) : ℝ) ^ 2 * a k = 0 := by rw [hk]; simp
      rw [h0]
      positivity
    · rw [ha, hcz k hk]
      exact sq_mul_norm_transport_le P.val.1 (rieszConstant s) s.val hβ hcs hs0 hs1 hk (z k)
  have hM : Summable (fun k : ℤ => (k : ℝ) ^ 2 * a k) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (sq_nonneg _) (ha0 k))
      hM_bound ?_
    exact ((hsz.add hsu).div_const _)
  have hAeq : ∀ r : ℝ, energySeries a r =
      ∫ x in (0 : ℝ)..1, (ψ (x : UnitAddCircle) - ψ ((x - r : ℝ) : UnitAddCircle)) ^ 2 := by
    intro r
    have h := hasSum_translate_sq (F := fun x : UnitAddCircle => (ψ x : ℂ)) hψ r
    have hfun : (fun k : ℤ => ‖fourierCoeff (fun x : UnitAddCircle => (ψ x : ℂ)) k‖ ^ 2 *
        (2 - 2 * Real.cos (2 * π * k * r))) =
        fun k : ℤ => a k * (2 - 2 * Real.cos (2 * π * k * r)) := by
      funext k
      rw [ha, hc]
    rw [hfun] at h
    have h2 : (∫ x in (0 : ℝ)..1, ‖(ψ (x : UnitAddCircle) : ℂ) -
        (ψ ((x - r : ℝ) : UnitAddCircle) : ℂ)‖ ^ 2) =
        ∫ x in (0 : ℝ)..1, (ψ (x : UnitAddCircle) - ψ ((x - r : ℝ) : UnitAddCircle)) ^ 2 := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    unfold energySeries
    rw [← h2]
    exact h.tsum_eq
  have hAeq' : ∀ r : ℝ, ∫ x in Ioc (0 : ℝ) 1, (ψ (x : UnitAddCircle) -
      ψ ((x - r : ℝ) : UnitAddCircle)) ^ 2 = energySeries a r := fun r => by
    rw [hAeq r, intervalIntegral.integral_of_le zero_le_one]
  have hAb : ∀ x : ℝ, |energySeries a x| ≤
      4 * π ^ 2 * (∑' k : ℤ, (k : ℝ) ^ 2 * a k) * dist (x : UnitAddCircle) 0 ^ 2 := by
    intro x
    have := abs_energySeries_le_sub_round ha0 hM x
    rw [dist_coe_zero_eq, sq_abs]
    exact this
  have hA1b : ∀ x : ℝ, |energySeries1 a x| ≤ 8 * π ^ 2 * (∑' k : ℤ, (k : ℝ) ^ 2 * a k) * |x| :=
    fun x => abs_energySeries1_le ha0 hM x
  have he : ∀ x : ℝ, energySeries a (-x) = energySeries a x := fun x => energySeries_neg a x
  have hp : ∀ x : ℝ, energySeries a (x + 1) = energySeries a x := fun x => by
    simpa using energySeries_add_int a 1 x
  have hA1 : ∀ x : ℝ, HasDerivAt (energySeries a) (energySeries1 a x) x :=
    fun x => hasDerivAt_energySeries ha0 hsa' hM x
  have hA2 : ∀ x : ℝ, HasDerivAt (energySeries1 a) (energySeries2 a x) x :=
    fun x => hasDerivAt_energySeries1 ha0 hM x
  have hA2c : Continuous (energySeries2 a) := continuous_energySeries2 ha0 hM
  have hAc : Continuous (energySeries a) :=
    continuous_iff_continuousAt.2 fun x => (hA1 x).continuousAt
  have hKIBP : ∫ x in (0 : ℝ)..1, deriv (deriv fun t : ℝ =>
        rieszRepresentative s (t : UnitAddCircle)) x * energySeries a x =
      ∫ x in (0 : ℝ)..1, rieszRepresentative s (x : UnitAddCircle) * energySeries2 a x :=
    integral_deriv_deriv_kernel_mul s.val hs0 hs1 (energySeries a) (energySeries1 a)
      (energySeries2 a) (4 * π ^ 2 * ∑' k : ℤ, (k : ℝ) ^ 2 * a k)
      (8 * π ^ 2 * ∑' k : ℤ, (k : ℝ) ^ 2 * a k) he hp hA1 hA2 hA2c hAb hA1b
  -- the Fubini step for the double integral
  have hmk : Measurable (fun t : ℝ => (t : UnitAddCircle)) := by fun_prop
  have hΨm : Measurable (fun t : ℝ => ψ (t : UnitAddCircle)) := hψm.comp hmk
  have hΨp : Function.Periodic (fun t : ℝ => ψ (t : UnitAddCircle)) 1 := fun t => by
    simp only
    rw [coe_add_one_eq]
  have hΨR : MemLp (fun t : ℝ => ψ (t : UnitAddCircle)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have h := hψL.re
    simpa using h
  have hΨ2 : ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (ψ (x : UnitAddCircle) ^ 2) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hΨR.integrable_sq
      (Eventually.of_forall fun x => sq_nonneg _)]
    exact ENNReal.ofReal_ne_top
  have hGper : Function.Periodic (fun t : ℝ => rieszRepresentative s (t : UnitAddCircle)) 1 :=
    fun t => by
      simp only
      rw [coe_add_one_eq]
  have hG2meas : Measurable (deriv (deriv fun t : ℝ =>
      rieszRepresentative s (t : UnitAddCircle))) := measurable_deriv _
  have hG2per : Function.Periodic (deriv (deriv fun t : ℝ =>
      rieszRepresentative s (t : UnitAddCircle))) 1 :=
    fun x => deriv_add_one_of_periodic (F := deriv fun t : ℝ =>
      rieszRepresentative s (t : UnitAddCircle))
      (fun y => deriv_add_one_of_periodic (F := fun t : ℝ =>
        rieszRepresentative s (t : UnitAddCircle)) hGper y) x
  have hint : IntegrableOn (fun r => |deriv (deriv fun t : ℝ =>
      rieszRepresentative s (t : UnitAddCircle)) r| *
      ∫ x in Ioc (0 : ℝ) 1, (ψ (x : UnitAddCircle) - ψ ((x - r : ℝ) : UnitAddCircle)) ^ 2)
      (Ioc (0 : ℝ) 1) := by
    have hkI := integrableOn_deriv_deriv_mul s.val hs0 hs1 (energySeries a)
      (4 * π ^ 2 * ∑' k : ℤ, (k : ℝ) ^ 2 * a k) hAc hAb
    have hIo : IntegrableOn (fun r => |deriv (deriv fun t : ℝ =>
        rieszRepresentative s (t : UnitAddCircle)) r| * energySeries a r) (Ioo 0 1) := by
      have hn : IntegrableOn (fun r => ‖deriv (deriv (hurwitzKernel s.val)) r * energySeries a r‖)
          (Ioo 0 1) := hkI.norm
      refine hn.congr_fun (fun r _ => ?_) measurableSet_Ioo
      dsimp only
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (energySeries_nonneg ha0 r)]
      rfl
    have hIc : IntegrableOn (fun r => |deriv (deriv fun t : ℝ =>
        rieszRepresentative s (t : UnitAddCircle)) r| * energySeries a r) (Ioc 0 1) :=
      hIo.congr_set_ae Ioo_ae_eq_Ioc.symm
    simp only [hAeq']
    exact hIc
  obtain ⟨hFint, hFeq⟩ := integrable_and_integral_translate hΨm hΨp hΨ2 hG2meas hG2per hint
  have hI : ∫ p : ℝ × ℝ, deriv (deriv fun t : ℝ =>
        rieszRepresentative s (t : UnitAddCircle)) (p.1 - p.2) *
        (ψ (p.1 : UnitAddCircle) - ψ (p.2 : UnitAddCircle)) ^ 2
        ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) =
      ∫ x in (0 : ℝ)..1, deriv (deriv fun t : ℝ =>
        rieszRepresentative s (t : UnitAddCircle)) x * energySeries a x := by
    rw [hFeq, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc fun r _ => ?_
    simp only [hAeq' r]
  -- the Fourier evaluation of the energy
  have hF := integral_mul_energySeries2 s ha0 hM
  have h1s : (1 - s.val) ≠ 0 := (sub_pos.mpr hs1).ne'
  obtain ⟨b, hb⟩ : ∃ b : ℤ → ℝ, ∀ k, b k = |2 * π * (k : ℝ)| ^ (1 - s.val) * ‖z k‖ ^ 2 /
      (2 * P.val.1 * rieszConstant s) := ⟨_, fun k => rfl⟩
  have hterm_energy : ∀ k : ℤ, P.val.1 * ((a k * (8 * π ^ 2 * (k : ℝ) ^ 2)) *
      (if k = 0 then 0 else rieszConstant s * (2 * π * |(k : ℝ)|) ^ (s.val - 1))) = b k := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [hb]
      simp [Real.zero_rpow h1s]
    · simp only [hk, ↓reduceIte]
      rw [ha, hcz k hk, norm_transport_term P.val.1 (rieszConstant s) s.val hβ hcs hk (z k),
        two_pi_abs_eq, hb]
      have key := energy_term_identity P.val.1 (rieszConstant s) s.val hβ hcs hk (z k)
      convert key using 1
      ring
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ p : ℝ × ℝ, deriv (deriv fun t : ℝ =>
        rieszRepresentative s (t : UnitAddCircle)) (p.1 - p.2) *
        (ψ (p.1 : UnitAddCircle) - ψ (p.2 : UnitAddCircle)) ^ 2
        ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := ⟨_, rfl⟩
  have hsum_energy : P.val.1 * I = ∑' k : ℤ, b k := by
    rw [hIdef, hI, hKIBP, hF, ← tsum_mul_left]
    exact tsum_congr hterm_energy
  -- the derivative pairing `∫ ξ' ψ`
  have hu_L2 : MemLp (fun x : ℝ => ((deriv ξt x : ℝ) : ℂ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    memLp_Ioc_of_continuous (Complex.continuous_ofReal.comp (hξt1.continuous_deriv (by norm_num)))
  have hRe := hasSum_re_conj_mul (u := deriv ξt) (v := fun t : ℝ => ψ (t : UnitAddCircle)) hu_L2 hψL
  have hcl : ∀ k : ℤ, lineCoeff (fun x : ℝ => (ψ (x : UnitAddCircle) : ℂ)) k = c k := fun k => by
    rw [hc, fourierCoeff_eq_lineCoeff]
  have hterm : ∀ k : ℤ, (conj (lineCoeff (fun x : ℝ => ((deriv ξt x : ℝ) : ℂ)) k) *
      lineCoeff (fun x : ℝ => (ψ (x : UnitAddCircle) : ℂ)) k).re = b k := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [lineCoeff_deriv hξt1 hξt_per 0, hb]
      simp [Real.zero_rpow h1s]
    · rw [lineCoeff_deriv hξt1 hξt_per k, ← hz_line k, hcl k, hcz k hk, hb]
      exact re_conj_mul_transport P.val.1 (rieszConstant s) s.val hβ hcs hk (z k)
  have hfun : (fun k : ℤ => (conj (lineCoeff (fun x : ℝ => ((deriv ξt x : ℝ) : ℂ)) k) *
      lineCoeff (fun x : ℝ => (ψ (x : UnitAddCircle) : ℂ)) k).re) = b := funext hterm
  have hJ : HasSum b (∫ x in (0 : ℝ)..1, deriv ξt x * ψ (x : UnitAddCircle)) := by
    rw [← hfun]
    exact hRe
  obtain ⟨J, hJdef⟩ : ∃ J : ℝ, J = ∫ x in (0 : ℝ)..1, deriv ξt x * ψ (x : UnitAddCircle) :=
    ⟨_, rfl⟩
  rw [← hJdef] at hJ
  -- the second moment of the transport in the Sobolev seminorm
  obtain ⟨F, hF'⟩ : ∃ F : ℤ → ℝ, ∀ k, F k = if k = 0 then 0 else
      |(k : ℝ)| ^ (1 - s.val) * ‖z k‖ ^ 2 := ⟨_, fun k => rfl⟩
  have hF_nonneg : ∀ k, 0 ≤ F k := fun k => by
    rw [hF' k]
    split_ifs <;> positivity
  have hP : (2 * π) ^ (1 - s.val) ≠ 0 := by positivity
  have hFb : ∀ k : ℤ, (2 * π) ^ (1 - s.val) / (2 * P.val.1 * rieszConstant s) * F k = b k := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [hF', hb]
      simp [Real.zero_rpow h1s]
    · simp only [hF' k, hk, ↓reduceIte]
      rw [hb, ← two_pi_abs_eq, Real.mul_rpow (by positivity) (abs_nonneg _)]
      ring
  have hFsum : Summable F := by
    refine (hJ.summable.mul_left ((2 * P.val.1 * rieszConstant s) / (2 * π) ^ (1 - s.val))).congr
      fun k => ?_
    rw [← hFb k]
    field_simp
  have hsob : circleSobolevSq ((1 - s.val) / 2) ⟨fun x => (ξ.val x : ℂ), ξ.property⟩ =
      ENNReal.ofReal (∑' k, F k) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hF_nonneg hFsum]
    unfold circleSobolevSq
    refine tsum_congr fun k => ?_
    rw [hF' k]
    by_cases hk : k = 0
    · subst hk
      simp
    · simp only [hk, ↓reduceIte]
      rw [← hz k]
      congr 1
      rw [show 2 * ((1 - s.val) / 2) = 1 - s.val by ring]
  have hLHS_ne : circleSobolevSq ((1 - s.val) / 2) ⟨fun x => (ξ.val x : ℂ), ξ.property⟩ ≠ ⊤ := by
    rw [hsob]
    exact ENNReal.ofReal_ne_top
  have hLHS_real : (2 * π) ^ (1 - s.val) / (2 * P.val.1 * rieszConstant s) *
      (circleSobolevSq ((1 - s.val) / 2) ⟨fun x => (ξ.val x : ℂ), ξ.property⟩).toReal =
      ∑' k : ℤ, b k := by
    rw [hsob, ENNReal.toReal_ofReal (tsum_nonneg hF_nonneg), ← tsum_mul_left]
    exact tsum_congr hFb
  have hβI : P.val.1 * I = J := by
    rw [hsum_energy, hJ.tsum_eq]
  rw [← hIdef, ← hJdef]
  refine ⟨hFint, hLHS_ne, ?_, ?_⟩
  · rw [hLHS_real, hJ.tsum_eq]
    linarith [hβI]
  · linarith [hβI]

/-- The mean-field energy identity: for a smooth real profile `ξ`
on the circle and its transport `ψ`, the double integral is absolutely convergent and the energy
identity holds. -/
theorem mean_field_energy_identity (P : Parameters) (ξ : Profile)
    (hξ : ContDiff ℝ ∞ (fun t : ℝ => ξ.val (t : UnitAddCircle)))
    (ψ : UnitAddCircle → ℝ)
    (hψ : MemLp (fun x => (ψ x : ℂ)) 2 volume)
    (hψc : ∀ k : ℤ, fourierCoeff (fun x => (ψ x : ℂ)) k = transportCoeffs P ⟨1, one_pos⟩ ξ k) :
    Integrable (fun p : ℝ × ℝ => deriv (deriv fun t : ℝ =>
        rieszRepresentative (parametersExponent P) (t : UnitAddCircle)) (p.1 - p.2) *
        (ψ (p.1 : UnitAddCircle) - ψ (p.2 : UnitAddCircle)) ^ 2)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) ∧
    circleSobolevSq ((1 - (parametersExponent P).val) / 2) ⟨fun x => (ξ.val x : ℂ), ξ.property⟩ ≠ ⊤ ∧
    (2 * π) ^ (1 - (parametersExponent P).val) /
        (2 * P.val.1 * rieszConstant (parametersExponent P)) *
      (circleSobolevSq ((1 - (parametersExponent P).val) / 2)
        ⟨fun x => (ξ.val x : ℂ), ξ.property⟩).toReal =
      -P.val.1 * (∫ p : ℝ × ℝ, deriv (deriv fun t : ℝ =>
          rieszRepresentative (parametersExponent P) (t : UnitAddCircle)) (p.1 - p.2) *
          (ψ (p.1 : UnitAddCircle) - ψ (p.2 : UnitAddCircle)) ^ 2
        ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1)))) +
        2 * ∫ x in (0 : ℝ)..1, deriv (fun t : ℝ => ξ.val (t : UnitAddCircle)) x *
          ψ (x : UnitAddCircle) ∧
    -P.val.1 * (∫ p : ℝ × ℝ, deriv (deriv fun t : ℝ =>
          rieszRepresentative (parametersExponent P) (t : UnitAddCircle)) (p.1 - p.2) *
          (ψ (p.1 : UnitAddCircle) - ψ (p.2 : UnitAddCircle)) ^ 2
        ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1)))) +
        2 * (∫ x in (0 : ℝ)..1, deriv (fun t : ℝ => ξ.val (t : UnitAddCircle)) x *
          ψ (x : UnitAddCircle)) =
      ∫ x in (0 : ℝ)..1, deriv (fun t : ℝ => ξ.val (t : UnitAddCircle)) x * ψ (x : UnitAddCircle) := by
  classical
  set F : UnitAddCircle → ℂ := fun x => (ψ x : ℂ) with hF_def
  have hG₀sm := hψ.aestronglyMeasurable.stronglyMeasurable_mk
  have hG₀ae : F =ᵐ[volume] hψ.aestronglyMeasurable.mk F := hψ.aestronglyMeasurable.ae_eq_mk
  set G₀ := hψ.aestronglyMeasurable.mk F with hG₀_def
  set ψ₀ : UnitAddCircle → ℝ := fun x => (G₀ x).re with hψ₀_def
  have hψ₀m : Measurable ψ₀ := Complex.measurable_re.comp hG₀sm.measurable
  have hψ₀ae : ψ₀ =ᵐ[volume] ψ := by
    filter_upwards [hG₀ae] with x hx
    simp only [hψ₀_def]
    rw [← hx, hF_def]
    simp
  have hcoe : (fun x => (ψ₀ x : ℂ)) =ᵐ[volume] F := by
    filter_upwards [hG₀ae] with x hx
    simp only [hψ₀_def]
    rw [← hx, hF_def]
    simp
  have hψ₀L : MemLp (fun x => (ψ₀ x : ℂ)) 2 volume := hψ.ae_eq hcoe.symm
  have hcoe' : (fun x => (ψ₀ x : ℂ)) =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)] F := by
    rw [show (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume by
      simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))).symm]
    exact hcoe
  have hψ₀c : ∀ k : ℤ, fourierCoeff (fun x => (ψ₀ x : ℂ)) k = transportCoeffs P ⟨1, one_pos⟩ ξ k := by
    intro k
    rw [congrFun (fourierCoeff_congr_ae hcoe') k]
    exact hψc k
  obtain ⟨h1, h2, h3, h4⟩ := energy_identity_of_measurable P ξ hξ ψ₀ hψ₀m hψ₀L hψ₀c
  have hxae : ∀ᵐ x : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ψ₀ (x : UnitAddCircle) = ψ (x : UnitAddCircle) := by
    have hmp := AddCircle.measurePreserving_mk (1 : ℝ) (0 : ℝ)
    have h := QuasiMeasurePreserving.ae hmp.quasiMeasurePreserving hψ₀ae
    simpa using h
  have hpae : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))),
      ψ₀ (p.1 : UnitAddCircle) = ψ (p.1 : UnitAddCircle) ∧ ψ₀ (p.2 : UnitAddCircle) = ψ (p.2 : UnitAddCircle) := by
    have h1' := QuasiMeasurePreserving.ae
      (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioc (0 : ℝ) 1))
        (ν := volume.restrict (Ioc (0 : ℝ) 1))) hxae
    have h2' := QuasiMeasurePreserving.ae
      (Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Ioc (0 : ℝ) 1))
        (ν := volume.restrict (Ioc (0 : ℝ) 1))) hxae
    filter_upwards [h1', h2'] with p hp1 hp2
    exact ⟨hp1, hp2⟩
  have hIeq : (∫ p : ℝ × ℝ, deriv (deriv fun t : ℝ =>
        rieszRepresentative (parametersExponent P) (t : UnitAddCircle)) (p.1 - p.2) *
        (ψ₀ (p.1 : UnitAddCircle) - ψ₀ (p.2 : UnitAddCircle)) ^ 2
        ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1)))) =
      ∫ p : ℝ × ℝ, deriv (deriv fun t : ℝ =>
        rieszRepresentative (parametersExponent P) (t : UnitAddCircle)) (p.1 - p.2) *
        (ψ (p.1 : UnitAddCircle) - ψ (p.2 : UnitAddCircle)) ^ 2
        ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    refine integral_congr_ae ?_
    filter_upwards [hpae] with p hp
    rw [hp.1, hp.2]
  have hJeq : (∫ x in (0 : ℝ)..1, deriv (fun t : ℝ => ξ.val (t : UnitAddCircle)) x *
        ψ₀ (x : UnitAddCircle)) =
      ∫ x in (0 : ℝ)..1, deriv (fun t : ℝ => ξ.val (t : UnitAddCircle)) x * ψ (x : UnitAddCircle) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hx' := (ae_restrict_iff' measurableSet_Ioc).mp hxae
    filter_upwards [hx'] with x hx hxI
    rw [uIoc_of_le zero_le_one] at hxI
    rw [hx hxI]
  rw [hIeq, hJeq] at h3 h4
  exact ⟨by
      refine h1.congr ?_
      filter_upwards [hpae] with p hp
      rw [hp.1, hp.2], h2, h3, h4⟩

end Riesz1
