/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.TransportCoeffs
public import Riesz1.Kernel.PeriodicZetaFourier
public import Riesz1.Kernel.ExplicitFormulasIndicatorCoeffs

/-!
# Indicator transport as a Fourier series

Part of Lemma 2.3, the transport identity (equation (2.17)). The
transport `ψ` of the centred arc indicator is `-(V_s(x + a) - V_s(x - a)) / (4πβ s tan(πs/2))`.
This file writes `ψ` as an absolutely convergent Fourier series, identifies its coefficients with
`transportCoeffs`, and proves that an `L²` function with those coefficients equals `ψ`
almost everywhere.
-/

public section

open MeasureTheory Set Filter Topology ComplexConjugate
open scoped Real Interval

namespace Riesz1

/-- The coefficient of `ψ` at the mode `n`, as a multiple of `c_n`. -/
@[expose] noncomputable def transportSeriesCoeff (s : ℝ) (β a : ℝ) (n : ℤ) : ℂ :=
  ((-(2 / (4 * Real.pi * β * s * Real.tan (Real.pi * s / 2))) * periodicZetaWeight s n : ℝ) : ℂ) *
    (fourier n (a : UnitAddCircle) - fourier n (-(a : UnitAddCircle)))

lemma norm_fourier_sub_le (n : ℤ) (a : ℝ) :
    ‖fourier n (a : UnitAddCircle) - fourier n (-(a : UnitAddCircle))‖ ≤ 2 := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_fourier_point, norm_fourier_point]
  norm_num

lemma summable_norm_transportSeriesCoeff {s : ℝ} (hs : 0 < s) (β a : ℝ) :
    Summable fun n : ℤ => ‖transportSeriesCoeff s β a n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_norm_periodicZetaWeight hs).mul_left (2 * |-(2 / (4 * Real.pi * β * s *
      Real.tan (Real.pi * s / 2)))|))
  unfold transportSeriesCoeff
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |-(2 / (4 * Real.pi * β * s * Real.tan (Real.pi * s / 2)))| * |periodicZetaWeight s n| *
        ‖fourier n (a : UnitAddCircle) - fourier n (-(a : UnitAddCircle))‖
      ≤ |-(2 / (4 * Real.pi * β * s * Real.tan (Real.pi * s / 2)))| * |periodicZetaWeight s n| * 2 :=
        mul_le_mul_of_nonneg_left (norm_fourier_sub_le n a) (by positivity)
    _ = 2 * |-(2 / (4 * Real.pi * β * s * Real.tan (Real.pi * s / 2)))| * |periodicZetaWeight s n| :=
        by ring

/-- Fourier modes are multiplicative for the addition on the circle. -/
lemma fourier_add_point (n : ℤ) (x y : UnitAddCircle) :
    fourier n (x + y) = fourier n x * fourier n y := by
  obtain ⟨x', rfl⟩ := exists_real_coe x
  obtain ⟨y', rfl⟩ := exists_real_coe y
  rw [← AddCircle.coe_add, fourier_coe_apply, fourier_coe_apply, fourier_coe_apply,
    Complex.ofReal_one, div_one, div_one, div_one, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The series `ψ(t) = ∑_n d_n e_n(t)` equals `-(V_s(t + a) - V_s(t - a)) / τ`, where
`τ = 4πβ s tan(πs/2)`. -/
lemma transportSeries_eq {s : RieszExponent} (β a : ℝ) (t : UnitAddCircle) :
    (((-(periodicZeta s (t + (a : UnitAddCircle)) - periodicZeta s (t - (a : UnitAddCircle))) /
        (4 * Real.pi * β * s.val * Real.tan (Real.pi * s.val / 2)) : ℝ)) : ℂ) =
      ∑' n : ℤ, transportSeriesCoeff s.val β a n * fourier n t := by
  have hs0 := s.2.1
  have hs1 := s.2.2
  have hH : ∀ u : UnitAddCircle, HurwitzZeta.hurwitzZetaEven u (-(s.val : ℂ)) =
      ∑' n : ℤ, (periodicZetaWeight s.val n : ℂ) * fourier n u :=
    fun u => (hasSum_periodicZetaWeight_circle hs0 hs1 u).tsum_eq.symm
  have hsum : ∀ u : UnitAddCircle, Summable fun n : ℤ =>
      (periodicZetaWeight s.val n : ℂ) * fourier n u :=
    fun u => (hasSum_periodicZetaWeight_circle hs0 hs1 u).summable
  have hdiff : HurwitzZeta.hurwitzZetaEven (t + (a : UnitAddCircle)) (-(s.val : ℂ)) -
      HurwitzZeta.hurwitzZetaEven (t - (a : UnitAddCircle)) (-(s.val : ℂ)) =
      ∑' n : ℤ, (periodicZetaWeight s.val n : ℂ) * fourier n t *
        (fourier n (a : UnitAddCircle) - fourier n (-(a : UnitAddCircle))) := by
    rw [hH, hH, ← Summable.tsum_sub (hsum _) (hsum _)]
    congr 1
    funext n
    rw [sub_eq_add_neg t (a : UnitAddCircle), fourier_add_point, fourier_add_point]
    ring
  have hV : ∀ u : UnitAddCircle, (periodicZeta s u : ℂ) =
      2 * (HurwitzZeta.hurwitzZetaEven u (-(s.val : ℂ)) -
        HurwitzZeta.hurwitzZetaEven 0 (-(s.val : ℂ))) :=
    fun u => periodicZeta_eq_hurwitzZetaEven s u
  have key : ∀ A B C τ : ℂ, -(2 * (A - C) - 2 * (B - C)) / τ = -(2 / τ) * (A - B) :=
    fun A B C τ => by ring
  rw [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_sub, hV, hV, key, hdiff,
    ← tsum_mul_left]
  congr 1
  funext n
  unfold transportSeriesCoeff
  push_cast
  ring

/-- The transport `ψ` of the centred arc indicator, as a real function on the circle. -/
@[expose] noncomputable def transportFormula (s : RieszExponent) (β a : ℝ) (t : UnitAddCircle) : ℝ :=
  -(periodicZeta s (t + (a : UnitAddCircle)) - periodicZeta s (t - (a : UnitAddCircle))) /
    (4 * Real.pi * β * s.val * Real.tan (Real.pi * s.val / 2))

lemma transportFormula_coe {s : RieszExponent} (β a : ℝ) (t : UnitAddCircle) :
    (transportFormula s β a t : ℂ) = ∑' n : ℤ, transportSeriesCoeff s.val β a n * fourier n t :=
  transportSeries_eq β a t

/-- Continuous functions on the circle are square integrable. -/
lemma memLp_of_continuous_circle {f : UnitAddCircle → ℂ} (hf : Continuous f) :
    MemLp f 2 volume := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun t => hC t (mem_univ t))

/-- The transport  is continuous on the circle, and it is given by its absolutely convergent
Fourier series. -/
lemma continuous_transportFormula {s : RieszExponent} (β a : ℝ) :
    Continuous fun t : UnitAddCircle => (transportFormula s β a t : ℂ) := by
  simp_rw [transportFormula_coe]
  exact continuous_tsum (fun n => continuous_const.mul (fourier n).continuous)
    (summable_norm_transportSeriesCoeff s.2.1 β a)
    (fun n t => by rw [norm_mul, norm_fourier_point, mul_one])

lemma continuous_transportFormula_real {s : RieszExponent} (β a : ℝ) :
    Continuous fun t : UnitAddCircle => transportFormula s β a t :=
  (Complex.continuous_re.comp (continuous_transportFormula (s := s) β a)).congr
    fun _ => Complex.ofReal_re _

/-- The Fourier coefficients of a constant shift of an integrable function. -/
lemma fourierCoeff_sub_const {f : UnitAddCircle → ℂ} (hf : Integrable f AddCircle.haarAddCircle)
    (b : ℂ) (k : ℤ) :
    fourierCoeff (fun t : UnitAddCircle => f t - b) k =
      fourierCoeff f k - b * fourierCoeff (fun _ : UnitAddCircle => (1 : ℂ)) k := by
  have h1 : Integrable (fun t : UnitAddCircle => fourier (-k) t • f t) AddCircle.haarAddCircle :=
    hf.fourier_smul (-k)
  have h3 : Integrable (fun t : UnitAddCircle => b * fourier (-k) t) AddCircle.haarAddCircle :=
    integrable_of_continuous_circle (continuous_const.mul (fourier (-k)).continuous)
  unfold fourierCoeff
  have e : ∀ t : UnitAddCircle, fourier (-k) t • (f t - b) =
      fourier (-k) t • f t - b * fourier (-k) t := fun t => by
    rw [smul_eq_mul, smul_eq_mul, mul_sub, mul_comm (fourier (-k) t) b]
  simp only [e]
  rw [integral_sub h1 h3, integral_const_mul]
  simp only [smul_eq_mul, mul_one]

/-- Two square integrable functions on the circle with the same Fourier coefficients agree almost
everywhere: the Fourier basis of `L²` is complete. -/
lemma ae_eq_of_fourierCoeff_eq {f g : UnitAddCircle → ℂ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (h : ∀ k : ℤ, fourierCoeff f k = fourierCoeff g k) :
    f =ᵐ[volume] g := by
  have hvol : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
  rw [hvol] at hf hg ⊢
  have hrepr : fourierBasis.repr (hf.toLp f) = fourierBasis.repr (hg.toLp g) := by
    ext i
    rw [fourierBasis_repr, fourierBasis_repr, congrFun (fourierCoeff_congr_ae hf.coeFn_toLp) i,
      congrFun (fourierCoeff_congr_ae hg.coeFn_toLp) i]
    exact h i
  have hLeq := fourierBasis.repr.injective hrepr
  calc f =ᵐ[AddCircle.haarAddCircle] ⇑(hf.toLp f) := hf.coeFn_toLp.symm
    _ = ⇑(hg.toLp g) := by rw [hLeq]
    _ =ᵐ[AddCircle.haarAddCircle] g := hg.coeFn_toLp

/-- The Riesz constant and the periodic zeta constant are linked by
`-2π c_s K_s = (2π)^{1-s} s tan(πs/2)`, where `K_s` is the functional equation constant. -/
lemma rieszConstant_mul_periodicZetaConst (s : RieszExponent) :
    -(2 * Real.pi) * rieszConstant s * periodicZetaConst s.val =
      (2 * Real.pi) ^ (1 - s.val) * s.val * Real.tan (Real.pi * s.val / 2) := by
  have hs0 := s.2.1
  have hs1 := s.2.2
  have hG := gamma_mul_rieszConstant_mul_cos s
  have hcos : 0 < Real.cos (Real.pi * s.val / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hGc : Real.Gamma s.val * rieszConstant s = Real.pi / Real.cos (Real.pi * s.val / 2) := by
    rw [eq_div_iff hcos.ne']
    exact hG
  have hP : (2 * Real.pi) ^ (1 - s.val) =
      (2 * Real.pi) ^ (2 : ℝ) * (2 * Real.pi) ^ (-(s.val + 1)) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  unfold periodicZetaConst
  rw [show 1 + s.val = s.val + 1 by ring, Real.Gamma_add_one hs0.ne',
    show Real.pi * (s.val + 1) / 2 = Real.pi * s.val / 2 + Real.pi / 2 by ring,
    Real.cos_add_pi_div_two, hP, Real.tan_eq_sin_div_cos]
  have key : -(2 * Real.pi) * rieszConstant s * (2 * (2 * Real.pi) ^ (-(s.val + 1)) *
      (s.val * Real.Gamma s.val) * -Real.sin (Real.pi * s.val / 2)) =
      4 * Real.pi * (2 * Real.pi) ^ (-(s.val + 1)) * s.val * Real.sin (Real.pi * s.val / 2) *
        (Real.Gamma s.val * rieszConstant s) := by ring
  rw [key, hGc, Real.rpow_two]
  field_simp
  ring

/-- The difference of the two exponentials `e^{±iθ}` is `2i sin θ`. -/
lemma exp_sub_exp_neg_mul_I (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) - Complex.exp (-((θ : ℂ) * Complex.I)) =
      2 * Complex.I * ((Real.sin θ : ℝ) : ℂ) := by
  rw [Complex.ofReal_sin, Complex.sin]
  have e1 : Complex.exp (-(θ : ℂ) * Complex.I) = Complex.exp (-((θ : ℂ) * Complex.I)) := by
    congr 1
    ring
  rw [e1]
  have h2 : (2 : ℂ) * Complex.I * ((Complex.exp (-((θ : ℂ) * Complex.I)) -
      Complex.exp ((θ : ℂ) * Complex.I)) * Complex.I / 2) =
      -(Complex.exp (-((θ : ℂ) * Complex.I)) - Complex.exp ((θ : ℂ) * Complex.I)) := by
    linear_combination (Complex.exp (-((θ : ℂ) * Complex.I)) -
      Complex.exp ((θ : ℂ) * Complex.I)) * Complex.I_mul_I
  rw [h2]
  ring

/-- The difference of the two exponentials at `±a` is `2i sin(2πka)`. -/
lemma fourier_sub_neg_eq (k : ℤ) (a : ℝ) :
    fourier k (a : UnitAddCircle) - fourier k (-(a : UnitAddCircle)) =
      2 * Complex.I * ((Real.sin (2 * Real.pi * k * a) : ℝ) : ℂ) := by
  have hneg : -(a : UnitAddCircle) = ((-a : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_neg]
  rw [hneg, fourier_coe_apply, fourier_coe_apply, Complex.ofReal_one, div_one, div_one]
  have h1 : (2 * Real.pi * Complex.I * (k : ℂ) * ((-a : ℝ) : ℂ)) =
      -(((2 * Real.pi * k * a : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  have h2 : (2 * Real.pi * Complex.I * (k : ℂ) * (a : ℂ)) =
      ((2 * Real.pi * k * a : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h1, h2, exp_sub_exp_neg_mul_I]

/-- The `k`-th Fourier coefficient of the transport series at `k = 0` vanishes. -/
lemma transportSeriesCoeff_zero (s : ℝ) (hs : 0 < s) (β a : ℝ) :
    transportSeriesCoeff s β a 0 = 0 := by
  have hz : periodicZetaWeight s 0 = 0 := by
    unfold periodicZetaWeight
    rw [Int.cast_zero, abs_zero, Real.zero_rpow (ne_of_lt (by linarith)), mul_zero]
  unfold transportSeriesCoeff
  simp [hz]

/-- Real identity behind the transport coefficient: with `R = |k|^{-(1+s)}`, the constant
`-2 K_s / τ` equals `(2π)^{1-s} / (4π² β c_s k²)`, where `τ = 4πβ s tan(πs/2)`. -/
lemma transport_real_identity (s : RieszExponent) (β : ℝ) (hβ : 0 < β) (k : ℤ) (hk : k ≠ 0) :
    -2 * periodicZetaConst s.val * |(k : ℝ)| ^ (-(1 + s.val)) /
        (4 * Real.pi * β * s.val * Real.tan (Real.pi * s.val / 2)) =
      |2 * Real.pi * (k : ℝ)| ^ (1 - s.val) /
        (4 * Real.pi ^ 2 * β * rieszConstant s * (k : ℝ) ^ 2) := by
  have hs0 := s.2.1
  have hs1 := s.2.2
  have hk0 : (0 : ℝ) < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
  have hkk : (k : ℝ) ^ 2 = |(k : ℝ)| ^ 2 := (sq_abs _).symm
  have hA : |2 * Real.pi * (k : ℝ)| ^ (1 - s.val) =
      (2 * Real.pi) ^ (1 - s.val) * |(k : ℝ)| ^ (1 - s.val) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), Real.mul_rpow (by positivity)
      (by positivity)]
  have hR : |(k : ℝ)| ^ (-(1 + s.val)) * (k : ℝ) ^ 2 = |(k : ℝ)| ^ (1 - s.val) := by
    rw [hkk, ← Real.rpow_natCast, ← Real.rpow_add hk0]
    congr 1
    push_cast
    ring
  have hconst := rieszConstant_mul_periodicZetaConst s
  have htan : 0 < Real.tan (Real.pi * s.val / 2) := by
    apply Real.tan_pos_of_pos_of_lt_pi_div_two
    · positivity
    · nlinarith [Real.pi_pos]
  have hτ : (4 * Real.pi * β * s.val * Real.tan (Real.pi * s.val / 2)) ≠ 0 := by
    have : 0 < s.val := hs0
    positivity
  have hden : (4 * Real.pi ^ 2 * β * rieszConstant s * (k : ℝ) ^ 2) ≠ 0 := by
    have hc : 0 < rieszConstant s := by
      unfold rieszConstant
      have h1 : 0 < Real.Gamma (s.val / 2) := Real.Gamma_pos_of_pos (by linarith)
      have h2 : 0 < Real.Gamma ((1 - s.val) / 2) := Real.Gamma_pos_of_pos (by linarith)
      positivity
    have hk2 : (k : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hk)
    have : 0 < 4 * Real.pi ^ 2 * β * rieszConstant s := by positivity
    exact mul_ne_zero this.ne' hk2
  rw [div_eq_div_iff hτ hden, hA]
  linear_combination (-8 * Real.pi ^ 2 * β * rieszConstant s * periodicZetaConst s.val) * hR +
    (4 * Real.pi * β * |(k : ℝ)| ^ (1 - s.val)) * hconst

/-- The transport coefficient of the centred arc indicator at `k ≠ 0`: the series coefficient
equals the transport formula `-|2πk|^{1-s} / (2β c_s · 2πik) · ξ̂(k)` with
`ξ̂(k) = sin(2πka)/(πk)`. -/
lemma transportSeriesCoeff_eq (s : RieszExponent) (β a : ℝ) (hβ : 0 < β) (k : ℤ) (hk : k ≠ 0) :
    transportSeriesCoeff s.val β a k =
      -((|2 * Real.pi * (k : ℝ)| ^ (1 - s.val) : ℝ) : ℂ) /
        (((2 * β * rieszConstant s : ℝ) : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ))) *
        ((Real.sin (2 * Real.pi * k * a) / (Real.pi * k) : ℝ) : ℂ) := by
  have hre := transport_real_identity s β hβ k hk
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hπC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hβC : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have hcC : (rieszConstant s : ℂ) ≠ 0 := by
    have hc : 0 < rieszConstant s := by
      unfold rieszConstant
      have h1 : 0 < Real.Gamma (s.val / 2) := Real.Gamma_pos_of_pos (by linarith [s.2.1])
      have h2 : 0 < Real.Gamma ((1 - s.val) / 2) := Real.Gamma_pos_of_pos (by linarith [s.2.2])
      have h3 : (0 : ℝ) < 2 ^ (1 - s.val) := by positivity
      positivity
    exact_mod_cast hc.ne'
  unfold transportSeriesCoeff
  rw [fourier_sub_neg_eq]
  have hLHS : ((-(2 / (4 * Real.pi * β * s.val * Real.tan (Real.pi * s.val / 2))) *
      periodicZetaWeight s.val k : ℝ) : ℂ) * (2 * Complex.I * ((Real.sin (2 * Real.pi * k * a) : ℝ) : ℂ)) =
      ((-2 * periodicZetaConst s.val * |(k : ℝ)| ^ (-(1 + s.val)) /
        (4 * Real.pi * β * s.val * Real.tan (Real.pi * s.val / 2)) : ℝ) : ℂ) *
        Complex.I * ((Real.sin (2 * Real.pi * k * a) : ℝ) : ℂ) := by
    unfold periodicZetaWeight
    push_cast
    ring
  rw [hLHS, hre]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

end Riesz1

end
