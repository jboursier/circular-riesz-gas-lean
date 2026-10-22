/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.ExplicitFormulasIndicatorMollify
public import Riesz1.ToMathlib.CircleSingularityLocalization
public import Riesz1.ToMathlib.Mollifier.RegularizationSobolev
public import Riesz1.ToMathlib.MollifierPointwise.Smoothing
public import Riesz1.ToMathlib.MollifierExistence

/-!
# The energy identity of the indicator by mollification

The energy identity of the centred arc indicator is the limit of the mollified identities of
`ExplicitFormulasIndicatorMollify`. The mollified seminorms converge to the seminorm of the
indicator, because the seminorm is finite at a slightly higher order. The mollified transports
converge uniformly to the transport, so the pairings with the derivatives of the mollified
indicators converge to the difference of the transport at `-a` and at `a`. This difference is
`2 V_s(2a)` divided by `4πβs tan(πs/2)`, which gives the closed form.
-/

public section

open MeasureTheory Set Filter Topology
open scoped Real Interval ContDiff

namespace Riesz1

variable {ρ : ℝ → ℝ}

/-- A mollifier is a circle mollifier. -/
lemma isCircleMollifier_of_isMollifier (hρ : IsMollifier ρ) : IsCircleMollifier ρ :=
  ⟨hρ.contDiff, hρ.2.2.1, hρ.nonneg, (subset_tsupport ρ).trans hρ.tsupport_subset,
    hρ.integral_eq_one⟩

lemma scaledMollifier_neg (hρ : IsMollifier ρ) (h y : ℝ) :
    scaledMollifier ρ h (-y) = scaledMollifier ρ h y := by
  unfold scaledMollifier
  rw [neg_div, hρ.2.2.1]

lemma periodMollifier_nonneg (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h) (z : ℝ) :
    0 ≤ periodMollifier ρ 1 h z :=
  tsum_nonneg fun n => by
    unfold scaledMollifier
    exact mul_nonneg (inv_nonneg.mpr hh.le) (hρ.nonneg _)

lemma periodMollifier_neg (hρ : IsMollifier ρ) (h z : ℝ) :
    periodMollifier ρ 1 h (-z) = periodMollifier ρ 1 h z := by
  unfold periodMollifier
  refine Eq.trans (tsum_congr fun n => ?_)
    ((Equiv.neg ℤ).tsum_eq (fun n : ℤ => scaledMollifier ρ h (z + n * 1)))
  show scaledMollifier ρ h (-z + n * 1) = scaledMollifier ρ h (z + ((-n : ℤ) : ℝ) * 1)
  rw [← scaledMollifier_neg hρ]
  congr 1
  push_cast
  ring

/-- The mollifier of the constant function `1` is `1`. -/
lemma circleMollify_const_one (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    circleMollify ρ 1 h (fun _ => 1) x = 1 := by
  rw [circleMollify_eq_mollifyLine hρ one_pos hh (locallyIntegrable_const (1 : ℝ))
    (fun _ => rfl) x]
  unfold mollifyLine
  simp only [one_mul]
  rw [integral_sub_left_eq_self (fun y => scaledMollifier ρ h y), integral_scaledMollifier hρ hh]

/-- Every period of the periodic kernel has integral one. -/
lemma intervalIntegral_periodMollifier (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h) (u : ℝ) :
    ∫ x in u..(u + 1), periodMollifier ρ 1 h x = 1 := by
  have hP : Function.Periodic (periodMollifier ρ 1 h) 1 := periodMollifier_periodic ρ 1 h
  have h0 : ∫ y in (-(1 / 2 : ℝ))..(1 / 2), periodMollifier ρ 1 h y = 1 := by
    have hc := circleMollify_const_one hρ hh 0
    unfold circleMollify at hc
    simp only [one_mul] at hc
    rw [intervalIntegral.integral_comp_sub_left (fun u => periodMollifier ρ 1 h u) 0] at hc
    norm_num at hc
    exact hc
  rw [hP.intervalIntegral_add_eq u (-(1 / 2 : ℝ))]
  norm_num
  exact h0

lemma intervalIntegral_periodMollifier_add (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h) (a : ℝ) :
    ∫ x in (0 : ℝ)..1, periodMollifier ρ 1 h (x + a) = 1 := by
  rw [intervalIntegral.integral_comp_add_right (periodMollifier ρ 1 h) a, zero_add,
    show (1 : ℝ) + a = a + 1 by ring]
  exact intervalIntegral_periodMollifier hρ hh a

lemma intervalIntegral_periodMollifier_sub (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h) (a : ℝ) :
    ∫ x in (0 : ℝ)..1, periodMollifier ρ 1 h (x - a) = 1 := by
  rw [intervalIntegral.integral_comp_sub_right (periodMollifier ρ 1 h) a, zero_sub,
    show (1 : ℝ) - a = -a + 1 by ring]
  exact intervalIntegral_periodMollifier hρ hh (-a)

/-- A continuous function of period one is uniformly continuous on the real line. -/
lemma exists_uniform_of_periodic {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u v : ℝ, |u - v| < δ → |g u - g v| < η := by
  have hGc : Continuous (Function.Periodic.lift hper) := by
    refine continuous_coinduced_dom.mpr ?_
    exact hg.congr fun t => (Function.Periodic.lift_coe hper t).symm
  obtain ⟨δ, hδ, hδG⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hGc) η hη
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), fun u v huv => ?_⟩
  have huv' : |u - v| ≤ 1 / 2 := by linarith [min_le_right δ (1 / 2 : ℝ)]
  have hdist : dist (u : UnitAddCircle) (v : UnitAddCircle) < δ := by
    rw [CircleSingularity.dist_coe_eq_abs_sub one_pos huv']
    exact lt_of_lt_of_le huv (min_le_left _ _)
  have hlt := hδG hdist
  rw [Real.dist_eq, Function.Periodic.lift_coe, Function.Periodic.lift_coe] at hlt
  exact hlt

/-- The mollification of a continuous periodic function converges uniformly to it. -/
lemma eventually_circleMollify_sub_le (hρ : IsMollifier ρ) {g : ℝ → ℝ} (hg : Continuous g)
    (hper : Function.Periodic g 1) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ x : ℝ, |circleMollify ρ 1 h g x - g x| ≤ η := by
  obtain ⟨δ, hδ, hgδ⟩ := exists_uniform_of_periodic hg hper hη
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min 1 (2 * δ) by positivity)] with h hh
  have hh0 : 0 < h := hh.1
  have hh2 : h < 2 * δ := lt_of_lt_of_le hh.2 (min_le_right _ _)
  intro x
  rw [circleMollify_eq_mollifyLine hρ one_pos hh0 hg.locallyIntegrable hper x]
  have hint : Integrable fun y => scaledMollifier ρ h (x - y) :=
    (integrable_scaledMollifier' hρ hh0).comp_sub_left x
  have hgi : Integrable fun y => g y * scaledMollifier ρ h (x - y) :=
    integrable_mul_scaled_sub hρ hh0 hg.locallyIntegrable x
  have hsub : mollifyLine ρ h g x - g x = ∫ y, (g y - g x) * scaledMollifier ρ h (x - y) := by
    have h2 : ∫ y, g x * scaledMollifier ρ h (x - y) = g x := by
      rw [integral_const_mul, integral_sub_left_eq_self (scaledMollifier ρ h),
        integral_scaledMollifier hρ hh0, mul_one]
    have h1 : ∫ y, (g y - g x) * scaledMollifier ρ h (x - y) =
        ∫ y, (g y * scaledMollifier ρ h (x - y) - g x * scaledMollifier ρ h (x - y)) := by
      congr 1
      funext y
      ring
    rw [h1, integral_sub hgi (hint.const_mul (g x)), h2]
    rfl
  have hmass : ∫ y, η * scaledMollifier ρ h (x - y) = η := by
    rw [integral_const_mul, integral_sub_left_eq_self (scaledMollifier ρ h),
      integral_scaledMollifier hρ hh0, mul_one]
  have hbound : ‖∫ y, (g y - g x) * scaledMollifier ρ h (x - y)‖ ≤
      ∫ y, η * scaledMollifier ρ h (x - y) := by
    refine norm_integral_le_of_norm_le (hint.const_mul η) (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (scaledMollifier_nonneg' hρ hh0 (x - y))]
    by_cases hS : scaledMollifier ρ h (x - y) = 0
    · simp [hS]
    · have hρne : ρ ((x - y) / h) ≠ 0 := by
        intro h0
        apply hS
        unfold scaledMollifier
        rw [h0, mul_zero]
      have hsupp := hρ.abs_lt_of_mem_tsupport (subset_tsupport ρ hρne)
      rw [abs_div, abs_of_pos hh0, div_lt_iff₀ hh0] at hsupp
      have hyx : |y - x| < δ := by rw [abs_sub_comm]; linarith
      exact mul_le_mul_of_nonneg_right (le_of_lt (hgδ y x hyx))
        (scaledMollifier_nonneg' hρ hh0 (x - y))
  rw [hsub]
  rw [Real.norm_eq_abs, hmass] at hbound
  exact hbound

/-- Pairing a translate of the periodic kernel with a periodic function gives the mollification. -/
lemma intervalIntegral_periodMollifier_mul (hρ : IsMollifier ρ) {h : ℝ} {g : ℝ → ℝ}
    (hper : Function.Periodic g 1) (c : ℝ) :
    ∫ x in (0 : ℝ)..1, periodMollifier ρ 1 h (x - c) * g x = circleMollify ρ 1 h g c := by
  have hP : Function.Periodic (fun x => periodMollifier ρ 1 h (x - c)) 1 := fun t => by
    simp only [show t + 1 - c = (t - c) + 1 by ring]
    exact periodMollifier_periodic ρ 1 h (t - c)
  have hF : Function.Periodic (fun x => periodMollifier ρ 1 h (x - c) * g x) 1 := fun t => by
    simp only [hP t, hper t]
  have hshift := hF.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  norm_num at hshift
  rw [← hshift]
  unfold circleMollify
  refine intervalIntegral.integral_congr fun y _ => ?_
  have hn := periodMollifier_neg hρ h (c - y)
  rw [show -(c - y) = y - c by ring] at hn
  show periodMollifier ρ 1 h (y - c) * g y = g y * periodMollifier ρ 1 h (c - y)
  rw [hn, mul_comm]

/-- The transport of the centred indicator, tested against the mollified indicator derivative,
converges to the difference of its values at `-a` and `a`. -/
lemma tendsto_pairing (hρ : IsMollifier ρ) (s : RieszExponent) (β a : ℝ) :
    Tendsto (fun h : ℝ => ∫ x in (0 : ℝ)..1,
        (periodMollifier ρ 1 h (x + a) - periodMollifier ρ 1 h (x - a)) *
          circleMollify ρ 1 h (transportLine s β a) x) (𝓝[>] 0)
      (𝓝 (transportLine s β a (-a) - transportLine s β a a)) := by
  have hψc := continuous_transportLine s β a
  have hψp := periodic_transportLine s β a
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [eventually_circleMollify_sub_le hρ hψc hψp (show 0 < ε / 5 by positivity),
    Ioo_mem_nhdsGT zero_lt_one] with h hu hh
  have hh0 : 0 < h := hh.1
  have hh1 : h ≤ 1 := hh.2.le
  have hPc : Continuous (periodMollifier ρ 1 h) := continuous_periodMollifier hρ one_pos hh0 hh1
  have hPa : Continuous fun x : ℝ => periodMollifier ρ 1 h (x + a) :=
    hPc.comp (continuous_id.add continuous_const)
  have hPb : Continuous fun x : ℝ => periodMollifier ρ 1 h (x - a) :=
    hPc.comp (continuous_id.sub continuous_const)
  have hcm : Continuous (circleMollify ρ 1 h (transportLine s β a)) :=
    (contDiff_circleMollify hρ one_pos hh0 hψc.locallyIntegrable hψp).continuous
  have hIa : IntervalIntegrable (fun x : ℝ => periodMollifier ρ 1 h (x + a) *
      transportLine s β a x) volume 0 1 := (hPa.mul hψc).intervalIntegrable 0 1
  have hIb : IntervalIntegrable (fun x : ℝ => periodMollifier ρ 1 h (x - a) *
      transportLine s β a x) volume 0 1 := (hPb.mul hψc).intervalIntegrable 0 1
  -- the mollified transport tested against the kernel translates
  have hA := intervalIntegral_periodMollifier_mul hρ hψp (-a) (h := h)
  have hB := intervalIntegral_periodMollifier_mul hρ hψp a (h := h)
  simp only [sub_neg_eq_add] at hA
  have hsplit : ∫ x in (0 : ℝ)..1,
        (periodMollifier ρ 1 h (x + a) - periodMollifier ρ 1 h (x - a)) *
          circleMollify ρ 1 h (transportLine s β a) x =
      (circleMollify ρ 1 h (transportLine s β a) (-a) - circleMollify ρ 1 h (transportLine s β a) a) +
        ∫ x in (0 : ℝ)..1, (periodMollifier ρ 1 h (x + a) - periodMollifier ρ 1 h (x - a)) *
          (circleMollify ρ 1 h (transportLine s β a) x - transportLine s β a x) := by
    rw [← hA, ← hB, ← intervalIntegral.integral_sub hIa hIb, ← intervalIntegral.integral_add]
    · congr 1
      funext x
      ring
    · exact (hIa.sub hIb)
    · exact ((hPa.sub hPb).mul (hcm.sub hψc)).intervalIntegrable 0 1
  have hI2 : ‖∫ x in (0 : ℝ)..1, (periodMollifier ρ 1 h (x + a) - periodMollifier ρ 1 h (x - a)) *
      (circleMollify ρ 1 h (transportLine s β a) x - transportLine s β a x)‖ ≤ 2 * (ε / 5) := by
    have hbnd : IntervalIntegrable (fun x : ℝ => (periodMollifier ρ 1 h (x + a) +
        periodMollifier ρ 1 h (x - a)) * (ε / 5)) volume 0 1 :=
      ((hPa.add hPb).mul continuous_const).intervalIntegrable 0 1
    have hmass : ∫ x in (0 : ℝ)..1, (periodMollifier ρ 1 h (x + a) +
        periodMollifier ρ 1 h (x - a)) * (ε / 5) = 2 * (ε / 5) := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_add
        (hPa.intervalIntegrable 0 1) (hPb.intervalIntegrable 0 1),
        intervalIntegral_periodMollifier_add hρ hh0 a, intervalIntegral_periodMollifier_sub hρ hh0 a]
      ring
    rw [← hmass]
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one (ae_of_all _ fun x _ => ?_) hbnd
    rw [Real.norm_eq_abs, abs_mul]
    have hPa0 := periodMollifier_nonneg hρ hh0 (x + a)
    have hPb0 := periodMollifier_nonneg hρ hh0 (x - a)
    have h1 : |periodMollifier ρ 1 h (x + a) - periodMollifier ρ 1 h (x - a)| ≤
        periodMollifier ρ 1 h (x + a) + periodMollifier ρ 1 h (x - a) := by
      rw [abs_le]
      constructor <;> linarith
    exact mul_le_mul h1 (hu x) (abs_nonneg _) (by linarith)
  rw [Real.norm_eq_abs] at hI2
  obtain ⟨e3, e3'⟩ := abs_le.mp hI2
  obtain ⟨e1, e1'⟩ := abs_le.mp (hu (-a))
  obtain ⟨e2, e2'⟩ := abs_le.mp (hu a)
  rw [hsplit, Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- The centred arc indicator as an element of `L²` on the unit circle. -/
@[expose] noncomputable def centredL2 (a : ℝ) : {f : UnitAddCircle → ℂ // MemLp f 2 volume} :=
  ⟨fun t => (centeredIndicatorArc a t : ℂ), memLp_centeredIndicatorArc a⟩

/-- The seminorm of the centred indicator at the slightly higher order `(1 - s)/2 + s/4` is
finite, since its Fourier coefficients are `sin(2πka)/(πk)`. -/
lemma circleSobolevSq_centredL2_lt_top {s : ℝ} (hs0 : 0 < s) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1 / 2) : circleSobolevSq ((1 - s) / 2 + s / 4) (centredL2 a) < ⊤ := by
  have hgs : Summable fun k : ℤ => |(k : ℝ)| ^ (-(1 + s / 2)) :=
    Real.summable_abs_int_rpow (by linarith)
  have hterm : ∀ k : ℤ, (if k = 0 then (0 : ENNReal) else ENNReal.ofReal
      (|(k : ℝ)| ^ (2 * ((1 - s) / 2 + s / 4)) * ‖fourierCoeff (centredL2 a).1 k‖ ^ 2)) ≤
      ENNReal.ofReal (|(k : ℝ)| ^ (-(1 + s / 2))) := by
    intro k
    by_cases hk : k = 0
    · simp only [hk, ↓reduceIte]
      exact zero_le
    · simp only [hk, ↓reduceIte]
      apply ENNReal.ofReal_le_ofReal
      have hc : fourierCoeff (centredL2 a).1 k =
          ((Real.sin (2 * Real.pi * k * a) / (Real.pi * k) : ℝ) : ℂ) := by
        show fourierCoeff (fun t : UnitAddCircle => (centeredIndicatorArc a t : ℂ)) k = _
        rw [fourierCoeff_centeredIndicatorArc ha0 ha1 k]
        simp only [hk, ↓reduceIte]
      rw [hc, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have hm : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
      have hk2 : (k : ℝ) ^ 2 = |(k : ℝ)| ^ 2 := (sq_abs _).symm
      have hsin : (Real.sin (2 * Real.pi * k * a) / (Real.pi * k)) ^ 2 ≤ 1 / (k : ℝ) ^ 2 := by
        have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
        have hk0 : (k : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hk)
        have hk0' : (0 : ℝ) < (k : ℝ) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hk0)
        rw [div_pow, mul_pow, div_le_div_iff₀ (by positivity) hk0']
        nlinarith [mul_nonneg (sub_nonneg.mpr (Real.sin_sq_le_one (2 * Real.pi * k * a)))
          hk0'.le, mul_nonneg (sub_nonneg.mpr hpi) hk0'.le]
      calc |(k : ℝ)| ^ (2 * ((1 - s) / 2 + s / 4)) *
            (Real.sin (2 * Real.pi * k * a) / (Real.pi * k)) ^ 2
          ≤ |(k : ℝ)| ^ (2 * ((1 - s) / 2 + s / 4)) * (1 / (k : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hsin (Real.rpow_nonneg (abs_nonneg _) _)
        _ = |(k : ℝ)| ^ (-(1 + s / 2)) := by
            have hinv : (1 : ℝ) / (k : ℝ) ^ 2 = |(k : ℝ)| ^ (-(2 : ℝ)) := by
              rw [← sq_abs, Real.rpow_neg hm.le, Real.rpow_two, one_div]
            rw [hinv, ← Real.rpow_add hm]
            congr 1
            ring
  unfold circleSobolevSq
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm) ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => Real.rpow_nonneg (abs_nonneg _) _) hgs]
  exact ENNReal.ofReal_lt_top

/-- The mollified seminorms satisfy `0 ≤ ‖ξ‖² - ‖ξ_h‖² ≤ C h^{s/2}`, so they converge to `‖ξ‖²`
as the scale `h` tends to zero. -/
lemma seminorm_smooth_bound (hρ : IsMollifier ρ) (s : RieszExponent) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1 / 2) :
    ∃ C : ℝ, ∀ h : ℝ, ∀ hh : 0 < h, h ≤ 1 →
      0 ≤ (circleSobolevSq ((1 - s.val) / 2) (centredL2 a)).toReal -
          (circleSobolevSq ((1 - s.val) / 2)
            ⟨fun x : UnitAddCircle => (smoothIndicator hρ a hh x : ℂ),
              memLp_smoothIndicator hρ a hh⟩).toReal ∧
        (circleSobolevSq ((1 - s.val) / 2) (centredL2 a)).toReal -
          (circleSobolevSq ((1 - s.val) / 2)
            ⟨fun x : UnitAddCircle => (smoothIndicator hρ a hh x : ℂ),
              memLp_smoothIndicator hρ a hh⟩).toReal ≤ C * h ^ (s.val / 2) := by
  obtain ⟨Creg, -, hreg⟩ := regularization_sobolev (isCircleMollifier_of_isMollifier hρ)
  have hs0 := s.2.1
  have hs1 := s.2.2
  have hδ1 : s.val / 4 ≤ 1 := by linarith
  refine ⟨Creg * (circleSobolevSq ((1 - s.val) / 2 + s.val / 4) (centredL2 a)).toReal,
    fun h hh hh1 => ?_⟩
  have hfin := circleSobolevSq_centredL2_lt_top hs0 ha0 ha1
  obtain ⟨-, hB, hC⟩ := hreg s.val (s.val / 4) h hh hh1 (centredL2 a) hs0 hs1 (by linarith) hfin
  have hF : ∀ k : ℤ, fourierCoeff (fun x : UnitAddCircle => (smoothIndicator hρ a hh x : ℂ)) k =
      fourierCoeff (centredL2 a).1 k * (mollifierFT ρ (h * k) : ℂ) :=
    fun k => fourierCoeff_smoothProfile hρ a hh k
  have hsub : circleSobolevSq ((1 - s.val) / 2)
        ⟨fun x : UnitAddCircle => (smoothIndicator hρ a hh x : ℂ),
          memLp_smoothIndicator hρ a hh⟩ =
      circleSobolevSq ((1 - s.val) / 2)
        (regularizeL2 (isCircleMollifier_of_isMollifier hρ) ⟨h, hh⟩ hh1 (centredL2 a)) := by
    unfold circleSobolevSq
    congr 1
    funext k
    by_cases hk : k = 0
    · simp only [hk, ↓reduceIte]
    · simp only [hk, ↓reduceIte]
      rw [fourierCoeff_regularizeL2 (isCircleMollifier_of_isMollifier hρ) ⟨h, hh⟩ hh1
        (centredL2 a) k]
      exact congrArg _ (by rw [hF k])
  rw [← hsub] at hB hC
  rw [min_eq_left hδ1, show 2 * (s.val / 4) = s.val / 2 by ring] at hC
  refine ⟨hB, ?_⟩
  linarith [hC, show Creg * h ^ (s.val / 2) * (circleSobolevSq ((1 - s.val) / 2 + s.val / 4)
    (centredL2 a)).toReal = Creg * (circleSobolevSq ((1 - s.val) / 2 + s.val / 4)
    (centredL2 a)).toReal * h ^ (s.val / 2) by ring]

/-- The transport of the centred indicator at `-a` minus its value at `a` is the periodic zeta
value at `2a`, up to the factor `4πβs tan(πs/2)`. -/
lemma transportLine_neg_sub (s : RieszExponent) (β a : ℝ) :
    transportLine s β a (-a) - transportLine s β a a =
      2 * periodicZeta s ((2 * a : ℝ) : UnitAddCircle) /
        (4 * Real.pi * β * s.val * Real.tan (Real.pi * s.val / 2)) := by
  have h0 : periodicZeta s (0 : UnitAddCircle) = 0 := periodicZeta_zero_point s
  unfold transportLine transportFormula
  have e1 : ((-a : ℝ) : UnitAddCircle) + (a : UnitAddCircle) = 0 := by
    rw [← AddCircle.coe_add]
    simp
  have e2 : ((-a : ℝ) : UnitAddCircle) - (a : UnitAddCircle) =
      ((-(2 * a) : ℝ) : UnitAddCircle) := by
    rw [← AddCircle.coe_sub]
    congr 1
    ring
  have e3 : (a : UnitAddCircle) + (a : UnitAddCircle) = ((2 * a : ℝ) : UnitAddCircle) := by
    rw [← AddCircle.coe_add]
    congr 1
    ring
  have e4 : (a : UnitAddCircle) - (a : UnitAddCircle) = 0 := by simp
  rw [e1, e2, e3, e4, h0, periodicZeta_neg s (2 * a)]
  ring

/-- The energy identity of the centred arc indicator (Lemma 2.3, equation (2.18)):
`(2π)^{1-s} / (2β c_s) ‖ξ‖² = cot(πs/2) V_s(2a) / (2πβs)`, with `ξ` the centred
arc indicator, `‖ξ‖²` the `H^{(1-s)/2}` seminorm, and `cot(πs/2) = cos(πs/2)/sin(πs/2)`. -/
theorem energy_identity_indicator (s : RieszExponent) (β : ℝ) (hβ : 0 < β) (a : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    circleSobolevSq ((1 - s.val) / 2)
        ⟨fun t : UnitAddCircle => (centeredIndicatorArc a t : ℂ), memLp_centeredIndicatorArc a⟩ ≠ ⊤ ∧
    (2 * Real.pi) ^ (1 - s.val) / (2 * β * rieszConstant s) *
        (circleSobolevSq ((1 - s.val) / 2)
          ⟨fun t : UnitAddCircle => (centeredIndicatorArc a t : ℂ),
            memLp_centeredIndicatorArc a⟩).toReal =
      Real.cos (Real.pi * s.val / 2) / Real.sin (Real.pi * s.val / 2) /
          (2 * Real.pi * β * s.val) * periodicZeta s ((2 * a : ℝ) : UnitAddCircle) := by
  obtain ⟨ρ, hρ⟩ := exists_isMollifier
  have hs0 := s.2.1
  have hs1 := s.2.2
  have hfin : circleSobolevSq ((1 - s.val) / 2) (centredL2 a) ≠ ⊤ :=
    ne_top_of_le_ne_top (circleSobolevSq_centredL2_lt_top hs0 ha0 ha1).ne
      (circleSobolevSq_mono (by linarith) _)
  have hC0pos : 0 < (2 * Real.pi) ^ (1 - s.val) / (2 * β * rieszConstant s) := by
    have := rieszConstant_pos s
    positivity
  obtain ⟨C, hC⟩ := seminorm_smooth_bound hρ s ha0 ha1
  have hR := tendsto_pairing hρ s β a
  -- the mollified energy identity, for each scale `h ∈ (0, 1]`
  have hmf : ∀ h : ℝ, ∀ hh : 0 < h, h ≤ 1 →
      (2 * Real.pi) ^ (1 - s.val) / (2 * β * rieszConstant s) *
        (circleSobolevSq ((1 - s.val) / 2)
          ⟨fun x : UnitAddCircle => (smoothIndicator hρ a hh x : ℂ),
            memLp_smoothIndicator hρ a hh⟩).toReal =
        ∫ x in (0 : ℝ)..1, (periodMollifier ρ 1 h (x + a) - periodMollifier ρ 1 h (x - a)) *
          circleMollify ρ 1 h (transportLine s β a) x := by
    intro h hh hh1
    rw [mollified_energy_identity s β hβ a ha0 ha1 hρ hh hh1]
    simp only [smoothTransport_coe]
  have hup : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∫ x in (0 : ℝ)..1,
      (periodMollifier ρ 1 h (x + a) - periodMollifier ρ 1 h (x - a)) *
        circleMollify ρ 1 h (transportLine s β a) x ≤
      (2 * Real.pi) ^ (1 - s.val) / (2 * β * rieszConstant s) *
        (circleSobolevSq ((1 - s.val) / 2) (centredL2 a)).toReal := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with h hh
    rw [← hmf h hh.1 hh.2.le]
    have := hC h hh.1 hh.2.le
    exact mul_le_mul_of_nonneg_left (by linarith [this.1]) hC0pos.le
  have hlow : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (2 * Real.pi) ^ (1 - s.val) / (2 * β * rieszConstant s) *
        ((circleSobolevSq ((1 - s.val) / 2) (centredL2 a)).toReal - C * h ^ (s.val / 2)) ≤
      ∫ x in (0 : ℝ)..1, (periodMollifier ρ 1 h (x + a) - periodMollifier ρ 1 h (x - a)) *
        circleMollify ρ 1 h (transportLine s β a) x := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with h hh
    rw [← hmf h hh.1 hh.2.le]
    have := hC h hh.1 hh.2.le
    exact mul_le_mul_of_nonneg_left (by linarith [this.2]) hC0pos.le
  -- the lower bound tends to the seminorm of the indicator
  have hp : Tendsto (fun h : ℝ => h ^ (s.val / 2)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : (0 : ℝ) ^ (s.val / 2) = 0 := Real.zero_rpow (div_pos hs0 two_pos).ne'
    have hc : Continuous fun h : ℝ => h ^ (s.val / 2) :=
      Real.continuous_rpow_const (div_pos hs0 two_pos).le
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [h0] at this
  have hlim : Tendsto (fun h : ℝ => (2 * Real.pi) ^ (1 - s.val) / (2 * β * rieszConstant s) *
      ((circleSobolevSq ((1 - s.val) / 2) (centredL2 a)).toReal - C * h ^ (s.val / 2)))
      (𝓝[>] 0) (𝓝 ((2 * Real.pi) ^ (1 - s.val) / (2 * β * rieszConstant s) *
        (circleSobolevSq ((1 - s.val) / 2) (centredL2 a)).toReal)) := by
    have := ((tendsto_const_nhds (x := (circleSobolevSq ((1 - s.val) / 2) (centredL2 a)).toReal)).sub
      (hp.const_mul C)).const_mul ((2 * Real.pi) ^ (1 - s.val) / (2 * β * rieszConstant s))
    simpa using this
  have hL1 := le_of_tendsto_of_tendsto hlim hR hlow
  have hL2 := le_of_tendsto_of_tendsto hR tendsto_const_nhds hup
  have hLeq := le_antisymm hL1 hL2
  have key : (2 * Real.pi) ^ (1 - s.val) / (2 * β * rieszConstant s) *
      (circleSobolevSq ((1 - s.val) / 2) (centredL2 a)).toReal =
        2 * periodicZeta s ((2 * a : ℝ) : UnitAddCircle) /
          (4 * Real.pi * β * s.val * Real.tan (Real.pi * s.val / 2)) := by
    rw [hLeq, transportLine_neg_sub]
  refine ⟨hfin, key.trans ?_⟩
  have hsin : 0 < Real.sin (Real.pi * s.val / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hcos : 0 < Real.cos (Real.pi * s.val / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

end Riesz1

end
