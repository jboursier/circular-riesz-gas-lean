/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.Interchange
public import Riesz1.ToMathlib.HurwitzKernel.ThetaFourier
public import Riesz1.ToMathlib.HeatKernel.OperatorsHeat

/-!
# The heat integral and its Fourier coefficients

The heat integral `g_s(x) = (c_s / Γ((1-s)/2)) ∫_{(0,∞)} (W_t(x) - 1) t^{-(1+s)/2} dt` is an
integrable function on the circle, where `W_t` is the heat kernel. Its Fourier coefficients are
computed by exchanging the integral over the circle with the time integral. The time integral of
`e^{-4π²k²t} t^{-(1+s)/2}` is a Gamma integral, which gives the Fourier coefficients of the
fundamental solution.

The integrability of `(x, t) ↦ (W_t(x) - 1) t^{-(1+s)/2}` on the circle times `(0, ∞)` comes from
two bounds on the spatial mean of `|W_t - 1|`: it is at most `2` for every time, since
`W_t ≥ 0` has mean one, and it is at most a constant times `e^{-4π²(t-1)}` for `t ≥ 1`.

Main results:
* `Riesz1.heatIntegral`: the heat integral on the circle.
* `Riesz1.fourierCoeff_heatIntegral`: its Fourier coefficients are those of the fundamental
  solution.
-/

public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace Riesz1

/-- The heat integral `(c_s / Γ((1-s)/2)) ∫_{(0,∞)} (W_t(x) - 1) t^{-(1+s)/2} dt` on the
circle, where `W_t(x) = HurwitzZeta.cosKernel x (4πt)` is the heat kernel. -/
noncomputable def heatIntegral (s : RieszExponent) (x : UnitAddCircle) : ℝ :=
  rieszConstant s / Real.Gamma ((1 - s.val) / 2) *
    ∫ t in Ioi (0 : ℝ), (HurwitzZeta.cosKernel x (4 * π * t) - 1) * t ^ (-(1 + s.val) / 2)

/-- The heat kernel at time `t`, on the real line, is the cosine theta kernel at `4πt`. -/
lemma cosKernel_four_pi_eq_circleHeatKernel {t : ℝ} (ht : 0 < t) (a : ℝ) :
    HurwitzZeta.cosKernel (a : UnitAddCircle) (4 * π * t) = circleHeatKernel t ht a := by
  apply Complex.ofReal_injective
  have h := (hasSum_cosKernel_fourier (a : UnitAddCircle) (by positivity : 0 < 4 * π * t)).tsum_eq
  rw [← circleHeatKernel_eq_complex_tsum t ht a, ← h]
  apply tsum_congr
  intro k
  rw [fourier_coe_apply]
  push_cast
  congr 2 <;> ring

/-- The heat kernel is nonnegative on the whole circle. -/
lemma cosKernel_four_pi_nonneg {t : ℝ} (ht : 0 < t) (x : UnitAddCircle) :
    0 ≤ HurwitzZeta.cosKernel x (4 * π * t) := by
  induction x using QuotientAddGroup.induction_on with
  | H a => rw [cosKernel_four_pi_eq_circleHeatKernel ht a]; exact (circleHeatKernel_pos t ht a).le

/-- The heat kernel has mean one on the circle. -/
lemma integral_cosKernel_four_pi {t : ℝ} (ht : 0 < t) :
    ∫ x : UnitAddCircle, HurwitzZeta.cosKernel x (4 * π * t) ∂AddCircle.haarAddCircle = 1 := by
  have h := fourierCoeff_cosKernel (4 * π * t) (by positivity) 0
  have h1 : ∫ x : UnitAddCircle, ((HurwitzZeta.cosKernel x (4 * π * t) : ℝ) : ℂ)
      ∂AddCircle.haarAddCircle = 1 := by
    simpa [fourierCoeff, fourier_zero] using h
  exact_mod_cast h1

/-- The spatial mean of `|W_t - 1|` is at most `2`, for every positive time. -/
lemma integral_abs_cosKernel_sub_one_le {t : ℝ} (ht : 0 < t) :
    ∫ x : UnitAddCircle, |HurwitzZeta.cosKernel x (4 * π * t) - 1| ∂AddCircle.haarAddCircle ≤ 2 := by
  have hcont : Continuous fun x : UnitAddCircle => HurwitzZeta.cosKernel x (4 * π * t) := by
    simpa [Function.comp_def] using
      Complex.continuous_re.comp (continuous_cosKernel_complex (4 * π * t) (by positivity))
  have hle : ∀ x : UnitAddCircle, |HurwitzZeta.cosKernel x (4 * π * t) - 1| ≤
      HurwitzZeta.cosKernel x (4 * π * t) + 1 := fun x => by
    have h0 := cosKernel_four_pi_nonneg ht x
    rw [abs_le]
    constructor <;> linarith
  have hi : Integrable (fun x : UnitAddCircle => HurwitzZeta.cosKernel x (4 * π * t))
      AddCircle.haarAddCircle := hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc ∫ x : UnitAddCircle, |HurwitzZeta.cosKernel x (4 * π * t) - 1| ∂AddCircle.haarAddCircle
      ≤ ∫ x : UnitAddCircle, (HurwitzZeta.cosKernel x (4 * π * t) + 1) ∂AddCircle.haarAddCircle :=
        integral_mono ((hcont.sub continuous_const).abs.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)) ((hi.add (integrable_const 1))) hle
    _ = 2 := by
        rw [integral_add hi (integrable_const 1), integral_cosKernel_four_pi ht]
        norm_num


/-- The heat kernel is continuous on the circle, at every positive time. -/
lemma continuous_cosKernel_four_pi {t : ℝ} (ht : 0 < t) :
    Continuous fun x : UnitAddCircle => HurwitzZeta.cosKernel x (4 * π * t) := by
  simpa [Function.comp_def] using
    Complex.continuous_re.comp (continuous_cosKernel_complex (4 * π * t) (by positivity))

/-- The heat kernel is jointly continuous in the spatial and the time variable on `(0, ∞)`. -/
lemma continuousOn_cosKernel_four_pi :
    ContinuousOn (fun p : UnitAddCircle × ℝ => (HurwitzZeta.cosKernel p.1 (4 * π * p.2) : ℂ))
      {p : UnitAddCircle × ℝ | 0 < p.2} := by
  intro p hp
  have hp' : 0 < p.2 := hp
  set δ : ℝ := p.2 / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hcont : ContinuousOn (fun q : UnitAddCircle × ℝ =>
      ∑' n : ℤ, (Real.exp (-Real.pi * (n : ℝ) ^ 2 * (4 * π * q.2)) : ℂ) * fourier n q.1)
      {q : UnitAddCircle × ℝ | δ < q.2} := by
    refine continuousOn_tsum (u := fun n : ℤ => Real.exp (-4 * π ^ 2 * (n : ℝ) ^ 2 * δ))
      (fun n => ?_) (summable_exp_neg_mul_sq δ hδpos) (fun n q hq => ?_)
    · exact ((Complex.continuous_ofReal.comp (by fun_prop)).mul
        ((fourier n).continuous.comp continuous_fst)).continuousOn
    · have hq' : δ < q.2 := hq
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        fourier_apply, Circle.norm_coe, mul_one]
      apply Real.exp_le_exp.2
      have hn : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
      nlinarith [Real.pi_pos, mul_nonneg (mul_nonneg Real.pi_pos.le hn) Real.pi_pos.le]
  have hnhds : {q : UnitAddCircle × ℝ | δ < q.2} ∈ 𝓝 p :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds (by
      show δ < p.2
      rw [hδ]
      linarith)
  have hcongr : ContinuousOn (fun q : UnitAddCircle × ℝ =>
      (HurwitzZeta.cosKernel q.1 (4 * π * q.2) : ℂ))
      {q : UnitAddCircle × ℝ | δ < q.2} := by
    refine hcont.congr (fun q hq => ?_)
    have hq' : 0 < q.2 := lt_trans (by rw [hδ]; positivity) hq
    exact (hasSum_cosKernel_fourier q.1 (by positivity : 0 < 4 * π * q.2)).tsum_eq.symm
  exact (hcongr.continuousAt hnhds).continuousWithinAt


/-- At times `t ≥ 1` the spatial deviation of the heat kernel is at most the deviation at time one,
times `e^{-4π²(t-1)}`: each term of the series decays at least by this factor. -/
lemma cosKernel_zero_sub_one_le_exp {t : ℝ} (ht : 1 ≤ t) :
    HurwitzZeta.cosKernel 0 (4 * π * t) - 1 ≤
      Real.exp (-(4 * π ^ 2) * (t - 1)) * (HurwitzZeta.cosKernel 0 (4 * π * 1) - 1) := by
  have h1 := HurwitzZeta.hasSum_nat_cosKernel₀ 0 (t := 4 * π * t) (by positivity)
  have h2 := (HurwitzZeta.hasSum_nat_cosKernel₀ 0 (t := 4 * π * 1) (by positivity)).mul_left
    (Real.exp (-(4 * π ^ 2) * (t - 1)))
  simp only [AddCircle.coe_zero] at h1 h2
  refine hasSum_le (fun n => ?_) h1 h2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg (n : ℝ)]
  have hexp : Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * (4 * π * t)) ≤
      Real.exp (-(4 * π ^ 2) * (t - 1)) *
        Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * (4 * π)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_pos, mul_nonneg (sub_nonneg.2 hm) (sub_nonneg.2 ht),
      mul_pos Real.pi_pos Real.pi_pos]
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
  linarith [hexp]

/-- The pointwise tail bound `|W_t(x) - 1| ≤ e^{-4π²(t-1)} (W_1(0) - 1)` for `t ≥ 1`. -/
lemma abs_cosKernel_sub_one_le_tail {t : ℝ} (ht : 1 ≤ t) (x : UnitAddCircle) :
    |HurwitzZeta.cosKernel x (4 * π * t) - 1| ≤
      Real.exp (-(4 * π ^ 2) * (t - 1)) * (HurwitzZeta.cosKernel 0 (4 * π * 1) - 1) :=
  (abs_cosKernel_sub_one_le x (4 * π * t) (by positivity)).trans
    (cosKernel_zero_sub_one_le_exp ht)

/-- The spatial mean of `|W_t - 1|` is at most `(2 + K) e^{-4π²(t-1)}` at every positive time,
where `K = W_1(0) - 1 ≥ 0`. -/
lemma integral_abs_cosKernel_sub_one_le_exp {t : ℝ} (ht : 0 < t) :
    ∫ x : UnitAddCircle, |HurwitzZeta.cosKernel x (4 * π * t) - 1| ∂AddCircle.haarAddCircle ≤
      (2 + (HurwitzZeta.cosKernel 0 (4 * π * 1) - 1)) * Real.exp (-(4 * π ^ 2) * (t - 1)) := by
  have hK : 0 ≤ HurwitzZeta.cosKernel 0 (4 * π * 1) - 1 :=
    (abs_nonneg _).trans (abs_cosKernel_sub_one_le 0 (4 * π * 1) (by positivity))
  have hE : 0 < Real.exp (-(4 * π ^ 2) * (t - 1)) := Real.exp_pos _
  rcases le_total t 1 with h | h
  · have h1 : 1 ≤ Real.exp (-(4 * π ^ 2) * (t - 1)) := by
      have h0 : 0 ≤ -(4 * π ^ 2) * (t - 1) := by
        nlinarith [mul_nonneg (sq_nonneg π) (sub_nonneg.2 h)]
      exact Real.one_le_exp h0
    have h2 := integral_abs_cosKernel_sub_one_le ht
    nlinarith
  · calc ∫ x : UnitAddCircle, |HurwitzZeta.cosKernel x (4 * π * t) - 1| ∂AddCircle.haarAddCircle
        ≤ ∫ _x : UnitAddCircle, Real.exp (-(4 * π ^ 2) * (t - 1)) *
            (HurwitzZeta.cosKernel 0 (4 * π * 1) - 1) ∂AddCircle.haarAddCircle :=
          integral_mono
            ((((continuous_cosKernel_four_pi ht).sub continuous_const).abs).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _))
            (integrable_const _) (fun x => abs_cosKernel_sub_one_le_tail h x)
      _ = Real.exp (-(4 * π ^ 2) * (t - 1)) * (HurwitzZeta.cosKernel 0 (4 * π * 1) - 1) := by
          simp
      _ ≤ (2 + (HurwitzZeta.cosKernel 0 (4 * π * 1) - 1)) * Real.exp (-(4 * π ^ 2) * (t - 1)) := by
          nlinarith

/-- The time weight `(2 + K) e^{-4π²(t-1)} t^{-(1+s)/2}` is integrable on `(0, ∞)`. -/
lemma integrableOn_heat_decay (s : RieszExponent) (K : ℝ) :
    IntegrableOn (fun t : ℝ => K * Real.exp (-(4 * π ^ 2) * (t - 1)) * t ^ (-(1 + s.val) / 2))
      (Ioi (0 : ℝ)) := by
  have hs1 : s.val < 1 := s.2.2
  have hs0 : 0 < s.val := s.2.1
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 + s.val) / 2)
    (b := 4 * π ^ 2) (by linarith) one_pos (by positivity)
  have h2 : IntegrableOn (fun t : ℝ => (K * Real.exp (4 * π ^ 2)) *
      (t ^ (-(1 + s.val) / 2) * Real.exp (-(4 * π ^ 2) * t ^ (1 : ℝ)))) (Ioi (0 : ℝ)) :=
    h.const_mul _
  refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  rw [show -(4 * π ^ 2) * (t - 1) = -(4 * π ^ 2) * t + 4 * π ^ 2 by ring, Real.exp_add]
  ring


/-- The Fourier mode of the constant function, against `e^{-2πik·}`, is the Kronecker delta. -/
lemma integral_fourier_neg_eq_ite (k : ℤ) :
    ∫ x : UnitAddCircle, fourier (-k) x ∂AddCircle.haarAddCircle = if k = 0 then 1 else 0 := by
  have h : fourierCoeff (fun _ : UnitAddCircle => (1 : ℂ)) k = if k = 0 then 1 else 0 := by
    have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) 0) k
    simpa [fourierCoeff, fourier_zero, smul_eq_mul, Pi.single_apply, eq_comm] using h
  simpa [fourierCoeff, smul_eq_mul] using h

/-- The Fourier coefficient of `W_t - 1` is the Gaussian `e^{-4π²k²t}` minus the Kronecker delta. -/
lemma integral_fourier_mul_cosKernel_sub_one {t : ℝ} (ht : 0 < t) (k : ℤ) :
    ∫ x : UnitAddCircle, fourier (-k) x * ((HurwitzZeta.cosKernel x (4 * π * t) - 1 : ℝ) : ℂ)
        ∂AddCircle.haarAddCircle =
      ((Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t) : ℝ) : ℂ) - if k = 0 then 1 else 0 := by
  have hW : Continuous fun x : UnitAddCircle =>
      fourier (-k) x * ((HurwitzZeta.cosKernel x (4 * π * t) : ℝ) : ℂ) :=
    (fourier (-k)).continuous.mul (Complex.continuous_ofReal.comp (continuous_cosKernel_four_pi ht))
  have hone : Continuous fun x : UnitAddCircle => fourier (-k) x := (fourier (-k)).continuous
  have hc : ∫ x : UnitAddCircle, fourier (-k) x * ((HurwitzZeta.cosKernel x (4 * π * t) : ℝ) : ℂ)
      ∂AddCircle.haarAddCircle = ((Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t) : ℝ) : ℂ) := by
    have h := fourierCoeff_cosKernel (4 * π * t) (by positivity) k
    simp only [fourierCoeff, smul_eq_mul] at h
    rw [h]
    congr 2
    ring
  simp only [Complex.ofReal_sub, Complex.ofReal_one, mul_sub, mul_one]
  rw [integral_sub (hW.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hone.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)), hc]
  congr 1
  exact integral_fourier_neg_eq_ite k


/-- The integrand `e^{-2πikx} (W_t(x) - 1) t^{-(1+s)/2}` is integrable on the circle times
`(0, ∞)`. The spatial mean of `|W_t - 1|` is at most `(2 + K) e^{-4π²(t-1)}`, and the time weight
`t^{-(1+s)/2}` is integrable against this bound. -/
lemma integrable_fourier_heatIntegrand (s : RieszExponent) (k : ℤ) :
    Integrable (fun p : UnitAddCircle × ℝ => fourier (-k) p.1 *
        (((HurwitzZeta.cosKernel p.1 (4 * π * p.2) - 1 : ℝ) : ℂ) *
          ((p.2 ^ (-(1 + s.val) / 2) : ℝ) : ℂ)))
      (AddCircle.haarAddCircle.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  set F : UnitAddCircle × ℝ → ℂ := fun p => fourier (-k) p.1 *
      (((HurwitzZeta.cosKernel p.1 (4 * π * p.2) - 1 : ℝ) : ℂ) *
        ((p.2 ^ (-(1 + s.val) / 2) : ℝ) : ℂ)) with hF
  have hcontOn : ContinuousOn F {p : UnitAddCircle × ℝ | 0 < p.2} := by
    have hW : ContinuousOn (fun p : UnitAddCircle × ℝ =>
        ((HurwitzZeta.cosKernel p.1 (4 * π * p.2) - 1 : ℝ) : ℂ)) {p : UnitAddCircle × ℝ | 0 < p.2} := by
      have h : ContinuousOn (fun p : UnitAddCircle × ℝ =>
          (HurwitzZeta.cosKernel p.1 (4 * π * p.2) : ℂ) - 1) {p : UnitAddCircle × ℝ | 0 < p.2} :=
        ContinuousOn.sub continuousOn_cosKernel_four_pi continuousOn_const
      simpa only [Complex.ofReal_sub, Complex.ofReal_one] using h
    have hT : ContinuousOn (fun p : UnitAddCircle × ℝ => ((p.2 ^ (-(1 + s.val) / 2) : ℝ) : ℂ))
        {p : UnitAddCircle × ℝ | 0 < p.2} :=
      Complex.continuous_ofReal.comp_continuousOn
        (ContinuousOn.rpow_const continuous_snd.continuousOn
          (fun p hp => Or.inl (ne_of_gt hp)))
    have hE : Continuous fun p : UnitAddCircle × ℝ => fourier (-k) p.1 :=
      (fourier (-k)).continuous.comp continuous_fst
    exact (hE.continuousOn.mul (hW.mul hT))
  have hS : MeasurableSet {p : UnitAddCircle × ℝ | 0 < p.2} :=
    measurableSet_lt measurable_const measurable_snd
  have hmeasEq : AddCircle.haarAddCircle.prod (volume.restrict (Ioi (0 : ℝ))) =
      (AddCircle.haarAddCircle.prod volume).restrict {p : UnitAddCircle × ℝ | 0 < p.2} := by
    have hset : {p : UnitAddCircle × ℝ | 0 < p.2} = univ ×ˢ Ioi (0 : ℝ) := by
      ext p
      simp
    have h := Measure.prod_restrict (μ := AddCircle.haarAddCircle) (ν := volume)
      (univ : Set UnitAddCircle) (Ioi (0 : ℝ))
    rw [Measure.restrict_univ] at h
    rw [hset, h]
  have hmeas : AEStronglyMeasurable F
      (AddCircle.haarAddCircle.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [hmeasEq]
    exact hcontOn.aestronglyMeasurable hS
  rw [integrable_prod_iff' hmeas]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t := ht
    have hcx : Continuous fun x : UnitAddCircle => F (x, t) := by
      have hW : Continuous fun x : UnitAddCircle =>
          ((HurwitzZeta.cosKernel x (4 * π * t) - 1 : ℝ) : ℂ) :=
        Complex.continuous_ofReal.comp ((continuous_cosKernel_four_pi ht').sub continuous_const)
      show Continuous fun x : UnitAddCircle => fourier (-k) x *
        (((HurwitzZeta.cosKernel x (4 * π * t) - 1 : ℝ) : ℂ) * ((t ^ (-(1 + s.val) / 2) : ℝ) : ℂ))
      exact (fourier (-k)).continuous.mul (hW.mul continuous_const)
    exact hcx.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · have hnorm : ∀ t ∈ Ioi (0 : ℝ), ∫ x : UnitAddCircle, ‖F (x, t)‖ ∂AddCircle.haarAddCircle ≤
        (2 + (HurwitzZeta.cosKernel 0 (4 * π * 1) - 1)) * Real.exp (-(4 * π ^ 2) * (t - 1)) *
          t ^ (-(1 + s.val) / 2) := by
      intro t ht
      have ht' : 0 < t := ht
      have hfun : ∀ x : UnitAddCircle, ‖F (x, t)‖ =
          |HurwitzZeta.cosKernel x (4 * π * t) - 1| * t ^ (-(1 + s.val) / 2) := by
        intro x
        simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, fourier_apply,
          Circle.norm_coe, one_mul]
        rw [abs_of_nonneg (Real.rpow_nonneg ht'.le _)]
      simp only [hfun]
      rw [integral_mul_const]
      exact mul_le_mul_of_nonneg_right (integral_abs_cosKernel_sub_one_le_exp ht')
        (Real.rpow_nonneg ht'.le _)
    refine Integrable.mono' (integrableOn_heat_decay s (2 + (HurwitzZeta.cosKernel 0 (4 * π * 1) - 1)))
      (AEStronglyMeasurable.integral_prod_right' (f := fun q : ℝ × UnitAddCircle =>
        ‖F (q.2, q.1)‖) hmeas.norm.prod_swap) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
    exact hnorm t ht


/-- The Fourier coefficients of the heat integral. The zero coefficient vanishes, and every other
coefficient is the Riesz constant times `(2π|k|)^{s-1}`, the multiplier of the fundamental equation.
The circle integral is exchanged with the time integral, and the time integral of the Gaussian
against `t^{-(1+s)/2}` is a Gamma integral. -/
theorem fourierCoeff_heatIntegral (s : RieszExponent) (k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => (heatIntegral s x : ℂ)) k =
      if k = 0 then 0 else ((rieszConstant s * (2 * π * |(k : ℝ)|) ^ (s.val - 1) : ℝ) : ℂ) := by
  have hs0 : 0 < s.val := s.2.1
  have hs1 : s.val < 1 := s.2.2
  have hΓ : Real.Gamma ((1 - s.val) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hA : ∀ x : UnitAddCircle, (heatIntegral s x : ℂ) =
      ((rieszConstant s / Real.Gamma ((1 - s.val) / 2) : ℝ) : ℂ) *
        ∫ t in Ioi (0 : ℝ), ((HurwitzZeta.cosKernel x (4 * π * t) - 1 : ℝ) : ℂ) *
          ((t ^ (-(1 + s.val) / 2) : ℝ) : ℂ) := by
    intro x
    rw [heatIntegral, Complex.ofReal_mul]
    congr 1
    simp only [← Complex.ofReal_mul]
    exact integral_complex_ofReal.symm
  simp only [fourierCoeff, smul_eq_mul]
  simp_rw [hA]
  have hC : ∀ x : UnitAddCircle,
      fourier (-k) x * (((rieszConstant s / Real.Gamma ((1 - s.val) / 2) : ℝ) : ℂ) *
        ∫ t in Ioi (0 : ℝ), ((HurwitzZeta.cosKernel x (4 * π * t) - 1 : ℝ) : ℂ) *
          ((t ^ (-(1 + s.val) / 2) : ℝ) : ℂ)) =
      ((rieszConstant s / Real.Gamma ((1 - s.val) / 2) : ℝ) : ℂ) *
        ∫ t in Ioi (0 : ℝ), fourier (-k) x * (((HurwitzZeta.cosKernel x (4 * π * t) - 1 : ℝ) : ℂ) *
          ((t ^ (-(1 + s.val) / 2) : ℝ) : ℂ)) := by
    intro x
    rw [integral_const_mul]
    ring
  simp_rw [hC]
  rw [integral_const_mul, integral_integral_swap (integrable_fourier_heatIntegrand s k)]
  have hD : ∀ t ∈ Ioi (0 : ℝ),
      ∫ x : UnitAddCircle, fourier (-k) x * (((HurwitzZeta.cosKernel x (4 * π * t) - 1 : ℝ) : ℂ) *
          ((t ^ (-(1 + s.val) / 2) : ℝ) : ℂ)) ∂AddCircle.haarAddCircle =
        (((Real.exp (-(4 * π ^ 2 * (k : ℝ) ^ 2) * t) : ℝ) : ℂ) - if k = 0 then 1 else 0) *
          ((t ^ (-(1 + s.val) / 2) : ℝ) : ℂ) := by
    intro t ht
    have ht' : 0 < t := ht
    simp_rw [← mul_assoc]
    rw [integral_mul_const, integral_fourier_mul_cosKernel_sub_one ht' k]
  rw [setIntegral_congr_fun measurableSet_Ioi hD]
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · have hγ : 0 < (1 - s.val) / 2 := by linarith
    have he : -(1 + s.val) / 2 = (1 - s.val) / 2 - 1 := by ring
    simp only [hk, ite_false, sub_zero, he]
    simp_rw [← Complex.ofReal_mul]
    rw [integral_complex_ofReal, integral_heat_rpow hγ k hk, ← Complex.ofReal_mul]
    congr 1
    have habs : |2 * π * (k : ℝ)| = 2 * π * |(k : ℝ)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    have hexp : (2 : ℝ) * (-((1 - s.val) / 2)) = s.val - 1 := by ring
    rw [habs, hexp]
    field_simp


/-- On `(0, 1)` the heat integral is the periodic Riesz kernel. The Poisson summation, the exchange
of sum and time integral, the Gamma integrals and the Euler summation are the steps of
`Riesz1.fundamental_interchange`, applied to the heat kernel written as its Fourier series. -/
theorem heatIntegral_eq_rieszRepresentative (s : RieszExponent) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1) :
    heatIntegral s (x : UnitAddCircle) = rieszRepresentative s (x : UnitAddCircle) := by
  have hint : heatIntegral s (x : UnitAddCircle) = rieszConstant s / Real.Gamma ((1 - s.val) / 2) *
      ∫ t in Ioi (0 : ℝ), (∑' k : ℤ, Real.exp (-4 * π ^ 2 * (k : ℝ) ^ 2 * t) *
        Real.cos (2 * π * k * x) - 1) * t ^ (-(1 + s.val) / 2) := by
    unfold heatIntegral
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : 0 < t := ht
    rw [cosKernel_four_pi_eq_circleHeatKernel ht' x, circleHeatKernel_eq_series]
  rw [hint]
  exact (fundamental_interchange s x hx0 hx1).2.2.1.trans (fundamental_interchange s x hx0 hx1).2.2.2

end Riesz1

end
