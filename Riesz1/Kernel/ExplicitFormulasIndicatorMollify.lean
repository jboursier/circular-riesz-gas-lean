/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.ExplicitFormulasIndicatorEnergy
public import Riesz1.Kernel.ExplicitFormulasIndicatorTransport
public import Riesz1.Kernel.MeanFieldEnergy
public import Riesz1.ToMathlib.CircleMollifyBounds
public import Riesz1.ToMathlib.CircleMollifyFourier
public import Riesz1.ToMathlib.MollifierPointwise.Derivative
public import Riesz1.ToMathlib.PeriodicConvolutionSmoothing

/-!
# Mollified indicator and transport

For a smooth mollifier `ρ` and a scale `h ∈ (0, 1]`, this file mollifies the centred arc indicator
`ξ = 1_{(-a,a)} - 2a` and its transport `ψ` with the periodic kernel of `ρ` at scale `h`.
The mollified profile `ξ_h` is smooth, and its Fourier coefficients are those of `ξ` multiplied by
the Fourier transform of the kernel. The transport of `ξ_h` is the mollification of `ψ`. The file
proves the energy identity of each mollified pair `(ξ_h, ψ_h)`, with the explicit derivative
`ξ_h'(x) = ρ_h(x + a) - ρ_h(x - a)`. The limit as `h` tends to zero is taken in
`ExplicitFormulasIndicatorLimit`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped Real Interval ContDiff

namespace Riesz1

variable {ρ : ℝ → ℝ}

/-- The indicator `1_{(-a,a)}` on the real line, as a function of period one. -/
@[expose] noncomputable def indicatorLine (a : ℝ) (t : ℝ) : ℝ := indicatorArc a (t : UnitAddCircle)

/-- The centred arc indicator on the real line, as a function of period one. -/
@[expose] noncomputable def centredLine (a : ℝ) (t : ℝ) : ℝ :=
  centeredIndicatorArc a (t : UnitAddCircle)

lemma centredLine_eq_add (a : ℝ) : centredLine a = fun t => -(2 * a) + indicatorLine a t := by
  funext t
  simp only [centredLine, indicatorLine, centeredIndicatorArc]
  ring

lemma periodic_indicatorLine (a : ℝ) : Function.Periodic (indicatorLine a) 1 := fun t => by
  simp only [indicatorLine, coe_add_one_eq]

lemma periodic_centredLine (a : ℝ) : Function.Periodic (centredLine a) 1 := fun t => by
  simp only [centredLine, coe_add_one_eq]

lemma locallyIntegrable_indicatorLine (a : ℝ) : LocallyIntegrable (indicatorLine a) volume := by
  have hset : indicatorLine a = (((↑) : ℝ → UnitAddCircle) ⁻¹' arcImage a).indicator
      (fun _ => (1 : ℝ)) := by
    funext t
    simp only [indicatorLine, indicatorArc]
    rfl
  have hopen : IsOpen (((↑) : ℝ → UnitAddCircle) ⁻¹' arcImage a) :=
    (isOpen_arcImage a).preimage continuous_quotient_mk'
  rw [hset]
  exact (locallyIntegrable_const (1 : ℝ)).indicator hopen.measurableSet

lemma locallyIntegrable_centredLine (a : ℝ) : LocallyIntegrable (centredLine a) volume := by
  rw [centredLine_eq_add]
  exact (locallyIntegrable_const _).add (locallyIntegrable_indicatorLine a)

/-- The transport of the centred indicator on the real line, as a function of period one. -/
@[expose] noncomputable def transportLine (s : RieszExponent) (β a : ℝ) (t : ℝ) : ℝ :=
  transportFormula s β a (t : UnitAddCircle)

lemma periodic_transportLine (s : RieszExponent) (β a : ℝ) :
    Function.Periodic (transportLine s β a) 1 := fun t => by
  simp only [transportLine, coe_add_one_eq]

lemma continuous_transportLine (s : RieszExponent) (β a : ℝ) :
    Continuous (transportLine s β a) :=
  (continuous_transportFormula_real (s := s) β a).comp continuous_quotient_mk'

/-- The mollified centred indicator at scale `h`, as a function on the unit circle. -/
@[expose] noncomputable def smoothIndicator (hρ : IsMollifier ρ) (a : ℝ) {h : ℝ} (hh : 0 < h) :
    UnitAddCircle → ℝ :=
  Function.Periodic.lift (Internal.circleMollify_periodic hρ one_pos hh
    (locallyIntegrable_centredLine a) (periodic_centredLine a))

lemma smoothIndicator_coe (hρ : IsMollifier ρ) (a : ℝ) {h : ℝ} (hh : 0 < h) (t : ℝ) :
    smoothIndicator hρ a hh (t : UnitAddCircle) = circleMollify ρ 1 h (centredLine a) t :=
  Function.Periodic.lift_coe _ t

/-- The mollified transport at scale `h`, as a function on the unit circle. -/
@[expose] noncomputable def smoothTransport (hρ : IsMollifier ρ) (s : RieszExponent) (β a : ℝ)
    {h : ℝ} (hh : 0 < h) : UnitAddCircle → ℝ :=
  Function.Periodic.lift (Internal.circleMollify_periodic hρ one_pos hh
    (continuous_transportLine s β a).locallyIntegrable (periodic_transportLine s β a))

lemma smoothTransport_coe (hρ : IsMollifier ρ) (s : RieszExponent) (β a : ℝ) {h : ℝ} (hh : 0 < h)
    (t : ℝ) :
    smoothTransport hρ s β a hh (t : UnitAddCircle) = circleMollify ρ 1 h (transportLine s β a) t :=
  Function.Periodic.lift_coe _ t

lemma continuous_smoothIndicator (hρ : IsMollifier ρ) (a : ℝ) {h : ℝ} (hh : 0 < h) :
    Continuous (smoothIndicator hρ a hh) := by
  refine continuous_coinduced_dom.mpr ?_
  have hc : Continuous (circleMollify ρ 1 h (centredLine a)) :=
    (contDiff_circleMollify hρ one_pos hh (locallyIntegrable_centredLine a)
      (periodic_centredLine a)).continuous
  exact hc.congr fun t => (smoothIndicator_coe hρ a hh t).symm

lemma continuous_smoothTransport (hρ : IsMollifier ρ) (s : RieszExponent) (β a : ℝ) {h : ℝ}
    (hh : 0 < h) : Continuous (smoothTransport hρ s β a hh) := by
  refine continuous_coinduced_dom.mpr ?_
  have hc : Continuous (circleMollify ρ 1 h (transportLine s β a)) :=
    (contDiff_circleMollify hρ one_pos hh (continuous_transportLine s β a).locallyIntegrable
      (periodic_transportLine s β a)).continuous
  exact hc.congr fun t => (smoothTransport_coe hρ s β a hh t).symm

lemma memLp_smoothIndicator (hρ : IsMollifier ρ) (a : ℝ) {h : ℝ} (hh : 0 < h) :
    MemLp (fun x => (smoothIndicator hρ a hh x : ℂ)) 2 volume :=
  memLp_of_continuous_circle (Complex.continuous_ofReal.comp (continuous_smoothIndicator hρ a hh))

lemma memLp_smoothTransport (hρ : IsMollifier ρ) (s : RieszExponent) (β a : ℝ) {h : ℝ}
    (hh : 0 < h) : MemLp (fun x => (smoothTransport hρ s β a hh x : ℂ)) 2 volume :=
  memLp_of_continuous_circle (Complex.continuous_ofReal.comp
    (continuous_smoothTransport hρ s β a hh))

/-- The mollified centred indicator at scale `h`, as a profile of the form used by
`transportCoeffs` on the circle of length one. -/
@[expose] noncomputable def smoothProfile (hρ : IsMollifier ρ) (a : ℝ) {h : ℝ} (hh : 0 < h) :
    {f : Circle ⟨1, one_pos⟩ → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength ⟨1, one_pos⟩)} :=
  ⟨smoothIndicator hρ a hh, memLp_smoothIndicator hρ a hh⟩

/-- The mollified centred indicator is the integral of the kernel over the arc of length `2a`,
shifted by the constant `-2a`. -/
lemma circleMollify_centredLine (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (x : ℝ) :
    circleMollify ρ 1 h (centredLine a) x =
      (∫ u in (x - a)..(x + a), periodMollifier ρ 1 h u) - 2 * a := by
  have hsplit := circleMollify_const_add hρ one_pos hh (locallyIntegrable_indicatorLine a)
    (periodic_indicatorLine a) (-(2 * a)) x
  rw [← centredLine_eq_add] at hsplit
  rw [hsplit]
  have hsub : Ioo (-a) a ⊆ Ioc (-(1 / 2 : ℝ)) (1 / 2) := fun y hy =>
    ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hind : circleMollify ρ 1 h (indicatorLine a) x =
      ∫ u in (x - a)..(x + a), periodMollifier ρ 1 h u := by
    unfold circleMollify
    have hcongr : ∫ y in (-(1 / 2 : ℝ))..(1 / 2),
        indicatorLine a y * periodMollifier ρ 1 h (x - y) =
        ∫ y in (-(1 / 2 : ℝ))..(1 / 2),
          (Ioo (-a) a).indicator (fun y => periodMollifier ρ 1 h (x - y)) y := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with y hy'
      rw [uIoc_of_le (by norm_num)] at hy'
      have hy2 : y ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) :=
        ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
      have hI := indicatorArc_coe_eq_indicator ha1 hy2
      simp only [indicatorLine, hI]
      by_cases hya : y ∈ Ioo (-a) a
      · simp [Set.indicator_of_mem hya]
      · simp [Set.indicator_of_notMem hya]
    rw [hcongr, intervalIntegral.integral_of_le (by norm_num), setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr hsub, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_sub_left (fun u => periodMollifier ρ 1 h u) x,
      sub_neg_eq_add]
  rw [hind]
  ring

/-- The derivative of the mollified centred indicator is the difference of two shifted kernels. -/
lemma hasDerivAt_circleMollify_centredLine (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (x : ℝ) :
    HasDerivAt (circleMollify ρ 1 h (centredLine a))
      (periodMollifier ρ 1 h (x + a) - periodMollifier ρ 1 h (x - a)) x := by
  have hP : Continuous (periodMollifier ρ 1 h) := continuous_periodMollifier hρ one_pos hh hh1
  have hfun : circleMollify ρ 1 h (centredLine a) = fun t =>
      (∫ u in (0 : ℝ)..(t + a), periodMollifier ρ 1 h u) -
        (∫ u in (0 : ℝ)..(t - a), periodMollifier ρ 1 h u) - 2 * a := by
    funext t
    rw [circleMollify_centredLine hρ hh ha0 ha1 t,
      intervalIntegral.integral_interval_sub_left (hP.intervalIntegrable _ _)
        (hP.intervalIntegrable _ _)]
  rw [hfun]
  have hΦ : ∀ u : ℝ, HasDerivAt (fun v : ℝ => ∫ w in (0 : ℝ)..v, periodMollifier ρ 1 h w)
      (periodMollifier ρ 1 h u) u := fun u => (hP.integral_hasStrictDerivAt 0 u).hasDerivAt
  have h1 := (hΦ (x + a)).comp_add_const x a
  have h2 := (hΦ (x - a)).comp_sub_const x a
  exact ((h1.sub h2).sub_const (2 * a)).congr_deriv (by ring)

lemma hasDerivAt_smoothIndicator (hρ : IsMollifier ρ) (a : ℝ) {h : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1) (ha0 : 0 < a) (ha1 : a < 1 / 2) (x : ℝ) :
    HasDerivAt (fun t : ℝ => smoothIndicator hρ a hh (t : UnitAddCircle))
      (periodMollifier ρ 1 h (x + a) - periodMollifier ρ 1 h (x - a)) x := by
  have hfun : (fun t : ℝ => smoothIndicator hρ a hh (t : UnitAddCircle)) =
      circleMollify ρ 1 h (centredLine a) :=
    funext (smoothIndicator_coe hρ a hh)
  rw [hfun]
  exact hasDerivAt_circleMollify_centredLine hρ hh hh1 ha0 ha1 x

/-- The Fourier coefficients of the mollified indicator are those of the indicator times the
Fourier transform of the kernel. -/
lemma fourierCoeff_smoothProfile (hρ : IsMollifier ρ) (a : ℝ) {h : ℝ} (hh : 0 < h) (k : ℤ) :
    fourierCoeff (fun x => ((smoothProfile hρ a hh).val x : ℂ)) k =
      fourierCoeff (fun x : UnitAddCircle => (centeredIndicatorArc a x : ℂ)) k *
        (mollifierFT ρ (h * k) : ℂ) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have := Internal.fourierCoeff_circleMollify hρ hh (locallyIntegrable_centredLine a)
    (periodic_centredLine a) (fun x : UnitAddCircle => centeredIndicatorArc a x)
    (smoothIndicator hρ a hh) (fun x => rfl) (fun x => smoothIndicator_coe hρ a hh x) k
  rw [div_one] at this
  exact this

/-- The Fourier coefficients of the transport `ψ` of the centred indicator. -/
lemma fourierCoeff_transportFormula_circle (s : RieszExponent) (β a : ℝ) (k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => (transportFormula s β a x : ℂ)) k =
      transportSeriesCoeff s.val β a k := by
  rw [show (fun x : UnitAddCircle => (transportFormula s β a x : ℂ)) =
      fun x => ∑' n : ℤ, transportSeriesCoeff s.val β a n * fourier n x from
        funext fun x => transportFormula_coe β a x]
  exact fourierCoeff_tsum_fourier _ (summable_norm_transportSeriesCoeff s.2.1 β a) k

lemma fourierCoeff_smoothTransport (hρ : IsMollifier ρ) (s : RieszExponent) (β a : ℝ) {h : ℝ}
    (hh : 0 < h) (k : ℤ) :
    fourierCoeff (fun x => (smoothTransport hρ s β a hh x : ℂ)) k =
      transportSeriesCoeff s.val β a k * (mollifierFT ρ (h * k) : ℂ) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have := Internal.fourierCoeff_circleMollify hρ hh (continuous_transportLine s β a).locallyIntegrable
    (periodic_transportLine s β a) (fun x : UnitAddCircle => transportFormula s β a x)
    (smoothTransport hρ s β a hh) (fun x => rfl) (fun x => smoothTransport_coe hρ s β a hh x) k
  rw [div_one, fourierCoeff_transportFormula_circle] at this
  exact this

/-- The transport coefficient of a profile on the unit circle is the Fourier multiplier of the
transport times the Fourier coefficient of the profile. -/
lemma transportCoeffs_eq_mul_fourierCoeff (P : Parameters)
    (ξ : {f : Circle ⟨1, one_pos⟩ → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength ⟨1, one_pos⟩)})
    (k : ℤ) :
    transportCoeffs P ⟨1, one_pos⟩ ξ k = (if k = 0 then 0 else
      -((|2 * Real.pi * (k : ℝ) / 1| ^ (1 - P.val.2) : ℝ) : ℂ) /
        ((2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) *
          (2 * Real.pi * Complex.I * (k : ℂ) / 1))) *
      fourierCoeff (fun x => (ξ.val x : ℂ)) k := by
  unfold transportCoeffs
  split_ifs with hk
  · simp
  · rfl

/-- The transport coefficients of the mollified indicator are those of the indicator times the
Fourier transform of the kernel. -/
lemma transportCoeffs_smoothProfile (s : RieszExponent) (β : ℝ) (hβ : 0 < β) (hρ : IsMollifier ρ)
    (a : ℝ) {h : ℝ} (hh : 0 < h) (k : ℤ) :
    transportCoeffs ⟨(β, s.val), hβ, s.2.1, s.2.2⟩ ⟨1, one_pos⟩ (smoothProfile hρ a hh) k =
      transportCoeffs ⟨(β, s.val), hβ, s.2.1, s.2.2⟩ ⟨1, one_pos⟩
        ⟨centeredIndicatorArc a, memLp_centeredIndicatorArc a⟩ k *
        (mollifierFT ρ (h * k) : ℂ) := by
  rw [transportCoeffs_eq_mul_fourierCoeff, transportCoeffs_eq_mul_fourierCoeff,
    fourierCoeff_smoothProfile]
  split_ifs <;> ring

/-- The energy identity of the mollified pair `(ξ_h, ψ_h)`: the seminorm of the mollified indicator
equals the pairing of its derivative with the mollified transport. -/
theorem mollified_energy_identity (s : RieszExponent) (β : ℝ) (hβ : 0 < β) (a : ℝ) (ha0 : 0 < a)
    (ha1 : a < 1 / 2) (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    (2 * Real.pi) ^ (1 - s.val) / (2 * β * rieszConstant s) *
        (circleSobolevSq ((1 - s.val) / 2)
          ⟨fun x : UnitAddCircle => (smoothIndicator hρ a hh x : ℂ),
            memLp_smoothIndicator hρ a hh⟩).toReal =
      ∫ x in (0 : ℝ)..1, (periodMollifier ρ 1 h (x + a) - periodMollifier ρ 1 h (x - a)) *
        smoothTransport hρ s β a hh (x : UnitAddCircle) := by
  have hξ : ContDiff ℝ ∞ (fun t : ℝ => (smoothProfile hρ a hh).val (t : UnitAddCircle)) := by
    have hfun : (fun t : ℝ => (smoothProfile hρ a hh).val (t : UnitAddCircle)) =
        circleMollify ρ 1 h (centredLine a) :=
      funext (smoothIndicator_coe hρ a hh)
    rw [hfun]
    exact contDiff_circleMollify hρ one_pos hh (locallyIntegrable_centredLine a)
      (periodic_centredLine a)
  have hψc : ∀ k : ℤ,
      fourierCoeff (fun x : UnitAddCircle => (smoothTransport hρ s β a hh x : ℂ)) k =
        transportCoeffs ⟨(β, s.val), hβ, s.2.1, s.2.2⟩ ⟨1, one_pos⟩ (smoothProfile hρ a hh) k := by
    intro k
    rw [fourierCoeff_smoothTransport hρ s β a hh k,
      transportCoeffs_smoothProfile s β hβ hρ a hh k,
      transportCoeffs_centered s β a hβ ha0 ha1 k]
  have hm := mean_field_energy_identity ⟨(β, s.val), hβ, s.2.1, s.2.2⟩ (smoothProfile hρ a hh)
    hξ (fun x : UnitAddCircle => smoothTransport hρ s β a hh x)
    (memLp_smoothTransport hρ s β a hh) hψc
  have h3 := hm.2.2.1.trans hm.2.2.2
  have hd : ∀ x : ℝ, deriv (fun t : ℝ => (smoothProfile hρ a hh).val (t : UnitAddCircle)) x =
      periodMollifier ρ 1 h (x + a) - periodMollifier ρ 1 h (x - a) := fun x =>
    (hasDerivAt_smoothIndicator hρ a hh hh1 ha0 ha1 x).deriv
  simp only [hd] at h3
  exact h3

end Riesz1

end
