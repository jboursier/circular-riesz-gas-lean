/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.CircleSobolevSq
public import Riesz1.Kernel.ExplicitFormulasIndicatorTransport

/-!
# Energy of the centred arc indicator

The energy identity of Lemma 2.3, equation (2.18). The centred
arc indicator `ξ = 1_{(-a,a)} - 2a` has Fourier coefficients `sin(2πka)/(πk)`, so its `H^{(1-s)/2}`
seminorm is a series in `|k|^{-(1+s)} (1 - cos(4πka))`. The periodic zeta combination at `2a` is the
same cosine series, which gives the closed form of the energy.
-/

public section

open MeasureTheory Set Filter Topology
open scoped Real Interval

namespace Riesz1

/-- The centred arc indicator `1_{(-a,a)} - 2a` on the circle, with mean zero. -/
@[expose] noncomputable def centeredIndicatorArc (a : ℝ) (t : UnitAddCircle) : ℝ :=
  indicatorArc a t - 2 * a

/-- The Haar measure is the volume on the circle of length one. -/
lemma volume_eq_haar_circle : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

lemma integrable_indicatorArc (a : ℝ) :
    Integrable (fun t : UnitAddCircle => (indicatorArc a t : ℂ)) AddCircle.haarAddCircle := by
  rw [← volume_eq_haar_circle]
  exact (memLp_indicatorArc a).integrable one_le_two

lemma centeredIndicatorArc_eq (a : ℝ) :
    (fun t : UnitAddCircle => (centeredIndicatorArc a t : ℂ)) =
      fun t => (indicatorArc a t : ℂ) - ((2 * a : ℝ) : ℂ) := by
  funext t
  simp [centeredIndicatorArc]

lemma memLp_centeredIndicatorArc (a : ℝ) :
    MemLp (fun t : UnitAddCircle => (centeredIndicatorArc a t : ℂ)) 2 volume := by
  rw [centeredIndicatorArc_eq]
  exact (memLp_indicatorArc a).sub (memLp_const _)

/-- The Fourier coefficients of the centred arc indicator: zero at `k = 0`, and
`sin(2πka)/(πk)` for `k ≠ 0`. -/
lemma fourierCoeff_centeredIndicatorArc {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (k : ℤ) :
    fourierCoeff (fun t : UnitAddCircle => (centeredIndicatorArc a t : ℂ)) k =
      if k = 0 then 0 else ((Real.sin (2 * Real.pi * k * a) / (Real.pi * k) : ℝ) : ℂ) := by
  rw [centeredIndicatorArc_eq, fourierCoeff_sub_const (integrable_indicatorArc a),
    fourierCoeff_indicatorArc ha0 ha1, fourierCoeff_one]
  by_cases hk : k = 0
  · subst hk
    simp
  · simp [hk]

/-- The sine squared as a cosine. -/
lemma sin_sq_eq_half_one_sub_cos (θ : ℝ) :
    Real.sin θ ^ 2 = (1 - Real.cos (2 * θ)) / 2 := by
  have h1 := Real.cos_two_mul θ
  have h2 := Real.sin_sq_add_cos_sq θ
  linarith

/-- The periodic zeta combination is the real cosine series `∑_n K |n|^{-(1+s)} (cos(2πnx) - 1)`. -/
lemma periodicZeta_eq_tsum_cos {s : RieszExponent} (x : ℝ) :
    periodicZeta s (x : UnitAddCircle) = ∑' n : ℤ,
      periodicZetaConst s.val * |(n : ℝ)| ^ (-(1 + s.val)) * (Real.cos (2 * Real.pi * n * x) - 1) := by
  have hs0 := s.2.1
  have hs1 := s.2.2
  have hP := Complex.hasSum_re (hasSum_periodicZetaWeight_circle hs0 hs1 (x : UnitAddCircle))
  have h0 := Complex.hasSum_re (hasSum_periodicZetaWeight_circle hs0 hs1 (0 : UnitAddCircle))
  have hterm : ∀ n : ℤ, ((periodicZetaWeight s.val n : ℂ) * fourier n (x : UnitAddCircle)).re =
      periodicZetaWeight s.val n * Real.cos (2 * Real.pi * n * x) := by
    intro n
    rw [fourier_coe_apply, Complex.ofReal_one, div_one, Complex.re_ofReal_mul]
    congr 1
    rw [show 2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ) =
      ((2 * Real.pi * n * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re]
  have hterm0 : ∀ n : ℤ, ((periodicZetaWeight s.val n : ℂ) * fourier n (0 : UnitAddCircle)).re =
      periodicZetaWeight s.val n := by
    intro n
    rw [fourier_eval_zero, mul_one, Complex.ofReal_re]
  have hsum := (hP.sub h0).mul_left 2
  simp only [hterm, hterm0] at hsum
  have hV : periodicZeta s (x : UnitAddCircle) = 2 *
      ((HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (-(s.val : ℂ))).re -
        (HurwitzZeta.hurwitzZetaEven 0 (-(s.val : ℂ))).re) := rfl
  rw [hV, ← hsum.tsum_eq]
  congr 1
  funext n
  unfold periodicZetaWeight
  ring

/-- The term of the seminorm at `k`, as a multiple of `|k|^{-(1+s)} (1 - cos(2πk·2a))`. -/
@[expose] noncomputable def energyKernel (s a : ℝ) (k : ℤ) : ℝ :=
  |(k : ℝ)| ^ (-(1 + s)) * (1 - Real.cos (2 * Real.pi * k * (2 * a)))

lemma summable_energyKernel {s : ℝ} (hs : 0 < s) (a : ℝ) : Summable (energyKernel s a) := by
  refine Summable.of_norm_bounded ((Real.summable_abs_int_rpow (b := 1 + s) (by linarith)).mul_left 2)
    (fun k => ?_)
  unfold energyKernel
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hc : ‖1 - Real.cos (2 * Real.pi * k * (2 * a))‖ ≤ 2 := by
    rw [Real.norm_eq_abs]
    have := Real.neg_one_le_cos (2 * Real.pi * k * (2 * a))
    have := Real.cos_le_one (2 * Real.pi * k * (2 * a))
    rw [abs_le]
    constructor <;> linarith
  have hr : 0 ≤ |(k : ℝ)| ^ (-(1 + s)) := Real.rpow_nonneg (abs_nonneg _) _
  calc |(k : ℝ)| ^ (-(1 + s)) * ‖1 - Real.cos (2 * Real.pi * k * (2 * a))‖
      ≤ |(k : ℝ)| ^ (-(1 + s)) * 2 := mul_le_mul_of_nonneg_left hc hr
    _ = 2 * |(k : ℝ)| ^ (-(1 + s)) := by ring

lemma periodicZetaConst_neg {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : periodicZetaConst s < 0 := by
  unfold periodicZetaConst
  have hcos : Real.cos (Real.pi * (1 + s) / 2) < 0 := by
    apply Real.cos_neg_of_pi_div_two_lt_of_lt
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hpos : 0 < 2 * (2 * Real.pi) ^ (-(1 + s)) * Real.Gamma (1 + s) := by
    have := Real.Gamma_pos_of_pos (show 0 < 1 + s by linarith)
    positivity
  nlinarith

/-- The term of the seminorm: `|k|^{1-s} (sin(2πka)/(πk))² = (1/(2π²)) energyKernel`. -/
lemma seminorm_term_eq {s : ℝ} (a : ℝ) (k : ℤ) :
    (if k = 0 then 0 else |(k : ℝ)| ^ (1 - s) * (Real.sin (2 * Real.pi * k * a) / (Real.pi * k)) ^ 2) =
      (1 / (2 * Real.pi ^ 2)) * energyKernel s a k := by
  by_cases hk : k = 0
  · subst hk
    simp [energyKernel]
  · have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hk2 : |(k : ℝ)| ^ (-(1 + s)) * (k : ℝ) ^ 2 = |(k : ℝ)| ^ (1 - s) := by
      have hk0' : (0 : ℝ) < |(k : ℝ)| := abs_pos.mpr hk0
      rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_add hk0']
      congr 1
      push_cast
      ring
    have hcos : Real.cos (2 * Real.pi * k * (2 * a)) = Real.cos (2 * (2 * Real.pi * k * a)) := by
      congr 1
      ring
    have hsin : 1 - Real.cos (2 * (2 * Real.pi * k * a)) = 2 * Real.sin (2 * Real.pi * k * a) ^ 2 := by
      linarith [sin_sq_eq_half_one_sub_cos (2 * Real.pi * k * a)]
    simp only [hk, ↓reduceIte]
    rw [energyKernel, hcos, hsin, ← hk2, div_pow]
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp

/-- The `H^{(1-s)/2}` seminorm of the centred arc indicator, as a series in `energyKernel`. -/
lemma tsum_seminorm_eq {s : ℝ} (a : ℝ) :
    ∑' k : ℤ, (if k = 0 then 0 else |(k : ℝ)| ^ (1 - s) *
      (Real.sin (2 * Real.pi * k * a) / (Real.pi * k)) ^ 2) =
      (1 / (2 * Real.pi ^ 2)) * ∑' k : ℤ, energyKernel s a k := by
  rw [← tsum_mul_left]
  congr 1
  funext k
  exact seminorm_term_eq a k

/-- The seminorm of the centred arc indicator, as an extended real: `(1/(2π²)) ∑_k energyKernel`. -/
lemma circleSobolevSq_centeredIndicatorArc {s : RieszExponent} {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1 / 2) :
    circleSobolevSq ((1 - s.val) / 2)
        ⟨fun t : UnitAddCircle => (centeredIndicatorArc a t : ℂ), memLp_centeredIndicatorArc a⟩ =
      ENNReal.ofReal ((1 / (2 * Real.pi ^ 2)) * ∑' k : ℤ, energyKernel s.val a k) := by
  have hs0 := s.2.1
  have hnn : ∀ k : ℤ, 0 ≤ (if k = 0 then 0 else
      |(k : ℝ)| ^ (1 - s.val) * (Real.sin (2 * Real.pi * k * a) / (Real.pi * k)) ^ 2) := by
    intro k
    by_cases hk : k = 0
    · simp [hk]
    · simp only [hk, ↓reduceIte]
      positivity
  have hsum : Summable (fun k : ℤ => if k = 0 then 0 else
      |(k : ℝ)| ^ (1 - s.val) * (Real.sin (2 * Real.pi * k * a) / (Real.pi * k)) ^ 2) := by
    have : (fun k : ℤ => if k = 0 then 0 else
        |(k : ℝ)| ^ (1 - s.val) * (Real.sin (2 * Real.pi * k * a) / (Real.pi * k)) ^ 2) =
        fun k => (1 / (2 * Real.pi ^ 2)) * energyKernel s.val a k :=
      funext fun k => seminorm_term_eq a k
    rw [this]
    exact (summable_energyKernel hs0 a).mul_left _
  have key : ∀ k : ℤ, (if k = 0 then (0 : ENNReal) else ENNReal.ofReal
      (|(k : ℝ)| ^ (2 * ((1 - s.val) / 2)) *
        ‖fourierCoeff (fun t : UnitAddCircle => (centeredIndicatorArc a t : ℂ)) k‖ ^ 2)) =
      ENNReal.ofReal (if k = 0 then 0 else
        |(k : ℝ)| ^ (1 - s.val) * (Real.sin (2 * Real.pi * k * a) / (Real.pi * k)) ^ 2) := by
    intro k
    by_cases hk : k = 0
    · simp [hk]
    · rw [fourierCoeff_centeredIndicatorArc ha0 ha1 k]
      simp only [hk, ↓reduceIte]
      congr 1
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, show 2 * ((1 - s.val) / 2) = 1 - s.val by ring]
  unfold circleSobolevSq
  simp_rw [key]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  congr 1
  exact tsum_seminorm_eq a

/-- The sum of the cosine kernel at `2a` is the periodic zeta combination at `2a`. -/
lemma tsum_energyKernel {s : RieszExponent} {a : ℝ} :
    ∑' k : ℤ, energyKernel s.val a k =
      -(1 / periodicZetaConst s.val) * periodicZeta s ((2 * a : ℝ) : UnitAddCircle) := by
  have hK : periodicZetaConst s.val ≠ 0 := (periodicZetaConst_neg s.2.1 s.2.2).ne
  have hterm : ∀ n : ℤ, energyKernel s.val a n =
      -(1 / periodicZetaConst s.val) * (periodicZetaConst s.val * |(n : ℝ)| ^ (-(1 + s.val)) *
        (Real.cos (2 * Real.pi * n * (2 * a)) - 1)) := by
    intro n
    unfold energyKernel
    field_simp
    ring
  rw [tsum_congr hterm, tsum_mul_left, periodicZeta_eq_tsum_cos]

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
  have hs0 := s.2.1
  have hs1 := s.2.2
  have hK : periodicZetaConst s.val ≠ 0 := (periodicZetaConst_neg hs0 hs1).ne
  have hV : 0 < periodicZeta s ((2 * a : ℝ) : UnitAddCircle) :=
    periodicZeta_pos s (by linarith) (by linarith)
  have hconst := rieszConstant_mul_periodicZetaConst s
  rw [circleSobolevSq_centeredIndicatorArc ha0 ha1, tsum_energyKernel]
  refine ⟨ENNReal.ofReal_ne_top, ?_⟩
  have hc : 0 < rieszConstant s := by
    unfold rieszConstant
    have h1 : 0 < Real.Gamma (s.val / 2) := Real.Gamma_pos_of_pos (by linarith)
    have h2 : 0 < Real.Gamma ((1 - s.val) / 2) := Real.Gamma_pos_of_pos (by linarith)
    have h3 : (0 : ℝ) < 2 ^ (1 - s.val) := by positivity
    positivity
  have hnonneg : 0 ≤ (1 / (2 * Real.pi ^ 2)) *
      (-(1 / periodicZetaConst s.val) * periodicZeta s ((2 * a : ℝ) : UnitAddCircle)) := by
    have hKneg := periodicZetaConst_neg hs0 hs1
    have : 0 ≤ -(1 / periodicZetaConst s.val) := by
      rw [neg_nonneg]
      exact (one_div_neg.mpr hKneg).le
    exact mul_nonneg (by positivity) (mul_nonneg this hV.le)
  rw [ENNReal.toReal_ofReal hnonneg, Real.tan_eq_sin_div_cos] at *
  have hsin : 0 < Real.sin (Real.pi * s.val / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hcos : 0 < Real.cos (Real.pi * s.val / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hcos' := hcos.ne'
  have hsin' := hsin.ne'
  have hsc : Real.sin (Real.pi * s.val / 2) / Real.cos (Real.pi * s.val / 2) *
      Real.cos (Real.pi * s.val / 2) = Real.sin (Real.pi * s.val / 2) :=
    div_mul_cancel₀ _ hcos'
  have hconst' : -(2 * Real.pi) * rieszConstant s * periodicZetaConst s.val *
      Real.cos (Real.pi * s.val / 2) = (2 * Real.pi) ^ (1 - s.val) * s.val *
        Real.sin (Real.pi * s.val / 2) := by
    linear_combination (Real.cos (Real.pi * s.val / 2)) * hconst +
      ((2 * Real.pi) ^ (1 - s.val) * s.val) * hsc
  have hP : (2 * Real.pi) ^ (1 - s.val) = -(2 * Real.pi) * rieszConstant s *
      periodicZetaConst s.val * Real.cos (Real.pi * s.val / 2) /
        (s.val * Real.sin (Real.pi * s.val / 2)) := by
    rw [eq_div_iff (mul_pos hs0 hsin).ne']
    linear_combination (-1 : ℝ) * hconst'
  rw [hP]
  field_simp

end Riesz1

end
