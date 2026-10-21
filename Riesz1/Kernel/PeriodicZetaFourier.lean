/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.PeriodicZeta
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Fourier coefficients of the periodic zeta combination

This is part of the proof of Lemma 2.3. For `0 < s < 1` the Hurwitz functional
equation at `1 + s` writes `V_s = 2 (G - G(0))`, where `G = ∑_n c_n e_n` is an absolutely convergent
Fourier series with weights `c_n = (K_s / 2) |n|^{-(1+s)}`. Termwise integration against the Fourier
basis then gives the coefficients of `V_s`: the coefficient at `k ≠ 0` is `K_s |k|^{-(1+s)}`, and
the zero coefficient is `-2 G(0)`.
-/

public section

open MeasureTheory Complex Set Filter Topology
open scoped Real Interval ComplexConjugate

namespace Riesz1

/-- The constant `K_s` of the Hurwitz functional equation at `1 + s`: `hurwitzZetaEven x (-s)` is
`K_s` times `cosZeta x (1 + s)`. -/
@[expose] noncomputable def periodicZetaConst (s : ℝ) : ℝ :=
  2 * (2 * Real.pi) ^ (-(1 + s)) * Real.Gamma (1 + s) * Real.cos (Real.pi * (1 + s) / 2)

/-- The Fourier weight `c_n = (K_s / 2) |n|^{-(1+s)}` of `G`. At `n = 0` it is zero. -/
@[expose] noncomputable def periodicZetaWeight (s : ℝ) (n : ℤ) : ℝ :=
  periodicZetaConst s / 2 * |(n : ℝ)| ^ (-(1 + s))

lemma periodicZetaWeight_neg (s : ℝ) (n : ℤ) :
    periodicZetaWeight s (-n) = periodicZetaWeight s n := by
  simp [periodicZetaWeight]

lemma summable_norm_periodicZetaWeight {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℤ => ‖(periodicZetaWeight s n : ℂ)‖) := by
  have h := (Real.summable_abs_int_rpow (b := 1 + s) (by linarith)).mul_left
    |periodicZetaConst s / 2|
  refine h.congr fun n => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, periodicZetaWeight, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]

/-- The Hurwitz functional equation at `1 + s` as a sum of the weights against Fourier modes: the
series defining `hurwitzZetaEven x (-s)` converges absolutely and equals `G`. -/
lemma hasSum_periodicZetaWeight {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ) :
    HasSum (fun n : ℤ => (periodicZetaWeight s n : ℂ) * fourier n (x : UnitAddCircle))
      (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (-(s : ℂ))) := by
  have hw : (1 : ℝ) < 1 + s := by linarith
  have hwC : 1 < (1 + (s : ℂ)).re := by simpa using hw
  have hFE := HurwitzZeta.hurwitzZetaEven_one_sub (x : UnitAddCircle) (s := 1 + (s : ℂ))
    (fun n h => by
      have h' := congrArg Complex.re h
      simp at h'
      have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      linarith)
    (Or.inr fun h => by
      have h' := congrArg Complex.re h
      simp at h'
      linarith)
  rw [show (1 : ℂ) - (1 + (s : ℂ)) = -(s : ℂ) by ring] at hFE
  have hK : 2 * (2 * (Real.pi : ℂ)) ^ (-(1 + (s : ℂ))) * Complex.Gamma (1 + (s : ℂ)) *
      Complex.cos (Real.pi * (1 + (s : ℂ)) / 2) = (periodicZetaConst s : ℂ) := by
    unfold periodicZetaConst
    have h2 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have hcos : Complex.cos (Real.pi * (1 + (s : ℂ)) / 2) =
        ((Real.cos (Real.pi * (1 + s) / 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cos]; push_cast; ring_nf
    have hgam : Complex.Gamma (1 + (s : ℂ)) = ((Real.Gamma (1 + s) : ℝ) : ℂ) := by
      rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
    have hpow : (2 * (Real.pi : ℂ)) ^ (-(1 + (s : ℂ))) =
        (((2 * Real.pi) ^ (-(1 + s)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow h2]; push_cast; ring_nf
    rw [hcos, hgam, hpow]
    push_cast
    ring
  rw [hFE, hK]
  have hS := (HurwitzZeta.hasSum_int_cosZeta (x : ℝ) hwC).mul_left (periodicZetaConst s : ℂ)
  have hterm : ∀ n : ℤ, (periodicZetaWeight s n : ℂ) * fourier n (x : UnitAddCircle) =
      (periodicZetaConst s : ℂ) *
        (cexp (2 * π * I * x * n) / ((|n| : ℤ) : ℂ) ^ (1 + (s : ℂ)) / 2) := by
    intro n
    have hn : ((|n| : ℤ) : ℂ) = ((|(n : ℝ)| : ℝ) : ℂ) := by
      rw [← Complex.ofReal_intCast, Int.cast_abs]
    have hm : ((|n| : ℤ) : ℂ) ^ (1 + (s : ℂ)) = ((|(n : ℝ)| ^ (1 + s) : ℝ) : ℂ) := by
      rw [hn, Complex.ofReal_cpow (abs_nonneg _)]
      push_cast
      rfl
    rw [hm, fourier_coe_apply, Complex.ofReal_one, div_one, periodicZetaWeight,
      Real.rpow_neg (abs_nonneg _)]
    push_cast
    rw [show 2 * π * I * n * x = 2 * π * I * x * n by ring]
    ring
  have hfun : (fun n : ℤ => (periodicZetaWeight s n : ℂ) * fourier n (x : UnitAddCircle)) =
      fun n : ℤ => (periodicZetaConst s : ℂ) *
        (cexp (2 * π * I * x * n) / ((|n| : ℤ) : ℂ) ^ (1 + (s : ℂ)) / 2) :=
    funext hterm
  rw [hfun]
  exact hS


/-- Every point of `UnitAddCircle` is the image of a real number. -/
lemma exists_real_coe (t : UnitAddCircle) : ∃ x : ℝ, (x : UnitAddCircle) = t :=
  QuotientAddGroup.mk_surjective t

/-- The Fourier series `G_s = ∑_n c_n e_n` of the Hurwitz functional equation converges at every
point of the circle, and its sum is `hurwitzZetaEven t (-s)`. -/
lemma hasSum_periodicZetaWeight_circle {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (t : UnitAddCircle) :
    HasSum (fun n : ℤ => (periodicZetaWeight s n : ℂ) * fourier n t)
      (HurwitzZeta.hurwitzZetaEven t (-(s : ℂ))) := by
  obtain ⟨x, rfl⟩ := exists_real_coe t
  exact hasSum_periodicZetaWeight hs0 hs1 x

/-- The Fourier series `G_s` is real: its sum is fixed by complex conjugation. -/
lemma conj_hurwitzZetaEven_neg {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (t : UnitAddCircle) :
    conj (HurwitzZeta.hurwitzZetaEven t (-(s : ℂ))) = HurwitzZeta.hurwitzZetaEven t (-(s : ℂ)) := by
  have h := hasSum_periodicZetaWeight_circle hs0 hs1 t
  have h1 := Complex.hasSum_conj'.mpr h
  have h2 := (Equiv.neg ℤ).hasSum_iff.mpr h
  have h1' : HasSum (fun n : ℤ => (periodicZetaWeight s (-n) : ℂ) * fourier (-n) t)
      (conj (HurwitzZeta.hurwitzZetaEven t (-(s : ℂ)))) := by
    convert h1 using 2 with n
    rw [map_mul, Complex.conj_ofReal, fourier_neg, periodicZetaWeight_neg]
  exact h1'.unique h2

/-- The periodic zeta combination as a complex Fourier series: `V_s = 2 (G_s - G_s(0))`. -/
lemma periodicZeta_eq_hurwitzZetaEven (s : RieszExponent) (t : UnitAddCircle) :
    (periodicZeta s t : ℂ) = 2 * (HurwitzZeta.hurwitzZetaEven t (-(s.val : ℂ)) -
      HurwitzZeta.hurwitzZetaEven 0 (-(s.val : ℂ))) := by
  have ht := Complex.conj_eq_iff_re.mp (conj_hurwitzZetaEven_neg s.2.1 s.2.2 t)
  have h0 := Complex.conj_eq_iff_re.mp (conj_hurwitzZetaEven_neg s.2.1 s.2.2 0)
  unfold periodicZeta
  push_cast
  rw [ht, h0]

/-- Fourier coefficients of a uniformly absolutely convergent series of Fourier modes. -/
lemma fourierCoeff_tsum_fourier (c : ℤ → ℂ) (hc : Summable fun n => ‖c n‖) (k : ℤ) :
    fourierCoeff (fun t : UnitAddCircle => ∑' n : ℤ, c n * fourier n t) k = c k := by
  have hcont : ∀ n : ℤ, Continuous fun t : UnitAddCircle => c n * fourier n t :=
    fun n => continuous_const.mul (fourier n).continuous
  have hint : ∀ n : ℤ, Integrable (fun t : UnitAddCircle => c n * (fourier (-k) t * fourier n t))
      AddCircle.haarAddCircle := fun n =>
    (continuous_const.mul ((fourier (-k)).continuous.mul (fourier n).continuous)).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  have hnorm' : ∀ (n : ℤ) (t : UnitAddCircle), ‖fourier n t‖ = 1 := fun n t => by
    rw [fourier_apply, Circle.norm_coe]
  have hnorm : ∀ n : ℤ, ∀ t : UnitAddCircle,
      ‖c n * (fourier (-k) t * fourier n t)‖ = ‖c n‖ := fun n t => by
    rw [norm_mul, norm_mul, hnorm', hnorm', mul_one, mul_one]
  have hsum : Summable fun n : ℤ => ∫ t : UnitAddCircle,
      ‖c n * (fourier (-k) t * fourier n t)‖ ∂AddCircle.haarAddCircle := by
    refine hc.congr fun n => ?_
    simp
  have hfc : ∀ n : ℤ, ∫ t : UnitAddCircle, fourier (-k) t * fourier n t
      ∂AddCircle.haarAddCircle = (Pi.single n (1 : ℂ) : ℤ → ℂ) k := fun n => by
    rw [← congrFun (fourierCoeff_fourier (T := 1) n) k]
    simp only [fourierCoeff, smul_eq_mul]
  unfold fourierCoeff
  calc ∫ t : UnitAddCircle, fourier (-k) t • ∑' n : ℤ, c n * fourier n t ∂AddCircle.haarAddCircle
      = ∫ t : UnitAddCircle, ∑' n : ℤ, c n * (fourier (-k) t * fourier n t)
          ∂AddCircle.haarAddCircle := by
        congr 1
        funext t
        rw [smul_eq_mul, ← tsum_mul_left]
        congr 1
        funext n
        ring
    _ = ∑' n : ℤ, ∫ t : UnitAddCircle, c n * (fourier (-k) t * fourier n t)
          ∂AddCircle.haarAddCircle :=
        (integral_tsum_of_summable_integral_norm hint hsum).symm
    _ = ∑' n : ℤ, c n * (Pi.single n (1 : ℂ) : ℤ → ℂ) k := by
        congr 1
        funext n
        rw [integral_const_mul, hfc n]
    _ = c k := by
        rw [tsum_eq_single k (fun n hn => by simp [hn])]
        simp


/-- The Fourier modes have modulus one at every point of the circle. -/
lemma norm_fourier_point (n : ℤ) (t : UnitAddCircle) : ‖fourier n t‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

/-- Continuous functions on the circle are integrable for the Haar probability measure. -/
lemma integrable_of_continuous_circle {f : UnitAddCircle → ℂ} (hf : Continuous f) :
    Integrable f AddCircle.haarAddCircle :=
  hf.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset (isClosed_tsupport _)
    (subset_univ _))

/-- The Fourier coefficients of the constant function `1`. -/
lemma fourierCoeff_one (k : ℤ) :
    fourierCoeff (fun _ : UnitAddCircle => (1 : ℂ)) k = (Pi.single 0 (1 : ℂ) : ℤ → ℂ) k := by
  have h : (fun _ : UnitAddCircle => (1 : ℂ)) = ⇑(fourier 0 : C(UnitAddCircle, ℂ)) :=
    funext fun _ => fourier_zero.symm
  rw [h]
  exact congrFun (fourierCoeff_fourier (T := 1) 0) k

/-- Fourier coefficients of an affine expression `a f - b` in a continuous `f`. -/
lemma fourierCoeff_affine (f : UnitAddCircle → ℂ) (hf : Continuous f) (a b : ℂ) (k : ℤ) :
    fourierCoeff (fun t : UnitAddCircle => a * f t - b) k =
      a * fourierCoeff f k - b * fourierCoeff (fun _ : UnitAddCircle => (1 : ℂ)) k := by
  have hint1 : Integrable (fun t : UnitAddCircle => a * (fourier (-k) t * f t))
      AddCircle.haarAddCircle :=
    integrable_of_continuous_circle (continuous_const.mul ((fourier (-k)).continuous.mul hf))
  have hint2 : Integrable (fun t : UnitAddCircle => b * fourier (-k) t)
      AddCircle.haarAddCircle :=
    integrable_of_continuous_circle (continuous_const.mul (fourier (-k)).continuous)
  unfold fourierCoeff
  simp only [smul_eq_mul, mul_one]
  have e : ∀ t : UnitAddCircle, fourier (-k) t * (a * f t - b) =
      a * (fourier (-k) t * f t) - b * fourier (-k) t := fun t => by ring
  simp only [e]
  rw [integral_sub hint1 hint2, integral_const_mul, integral_const_mul]

/-- The periodic zeta combination has the Fourier coefficients of the explicit series: the
coefficient at `k ≠ 0` is `K_s |k|^{-(1+s)}`, and the zero coefficient is `-2 ∑_n c_n`. -/
theorem fourierCoeff_periodicZeta (s : RieszExponent) (k : ℤ) :
    fourierCoeff (fun t : UnitAddCircle => (periodicZeta s t : ℂ)) k =
      if k = 0 then -2 * ∑' n : ℤ, (periodicZetaWeight s.val n : ℂ)
      else (periodicZetaConst s.val : ℂ) * ((|(k : ℝ)| ^ (-(1 + s.val)) : ℝ) : ℂ) := by
  have hc : Summable fun n : ℤ => ‖(periodicZetaWeight s.val n : ℂ)‖ :=
    summable_norm_periodicZetaWeight s.2.1
  have hG : Continuous fun t : UnitAddCircle =>
      ∑' n : ℤ, (periodicZetaWeight s.val n : ℂ) * fourier n t :=
    continuous_tsum (fun n => continuous_const.mul (fourier n).continuous) hc
      (fun n t => by rw [norm_mul, norm_fourier_point, mul_one])
  have hfun : (fun t : UnitAddCircle => (periodicZeta s t : ℂ)) =
      fun t => 2 * (∑' n : ℤ, (periodicZetaWeight s.val n : ℂ) * fourier n t) -
        2 * ∑' n : ℤ, (periodicZetaWeight s.val n : ℂ) * fourier n (0 : UnitAddCircle) := by
    funext t
    rw [periodicZeta_eq_hurwitzZetaEven,
      (hasSum_periodicZetaWeight_circle s.2.1 s.2.2 t).tsum_eq,
      (hasSum_periodicZetaWeight_circle s.2.1 s.2.2 (0 : UnitAddCircle)).tsum_eq]
    ring
  simp only [fourier_eval_zero, mul_one] at hfun
  have h0 : (periodicZetaWeight s.val 0 : ℂ) = 0 := by
    have hz : periodicZetaWeight s.val 0 = 0 := by
      unfold periodicZetaWeight
      rw [Int.cast_zero, abs_zero, Real.zero_rpow (ne_of_lt (by linarith [s.2.1])), mul_zero]
    rw [hz, Complex.ofReal_zero]
  rw [hfun, fourierCoeff_affine _ hG, fourierCoeff_tsum_fourier _ hc, fourierCoeff_one]
  by_cases hk : k = 0
  · subst hk
    simp only [↓reduceIte, h0, Pi.single_eq_same]
    ring
  · simp only [hk, ↓reduceIte, Pi.single_apply, mul_zero, sub_zero]
    simp only [periodicZetaWeight]
    push_cast
    ring

/-- The weights sum to `K_s ζ(1+s)`: the zero Fourier coefficient is `-2 K_s ζ(1+s)`. -/
lemma hasSum_periodicZetaWeight_riemannZeta {s : ℝ} (hs0 : 0 < s) :
    HasSum (fun n : ℤ => (periodicZetaWeight s n : ℂ))
      (periodicZetaConst s * riemannZeta (1 + (s : ℂ))) := by
  have hw : 1 < (1 + (s : ℂ)).re := by simp; linarith
  have hcos := HurwitzZeta.hasSum_int_cosZeta (0 : ℝ) hw
  have h0 : ((0 : ℝ) : UnitAddCircle) = 0 := by simp
  rw [h0, congrFun HurwitzZeta.cosZeta_zero] at hcos
  have h2 := hcos.mul_left (periodicZetaConst s : ℂ)
  convert h2 using 1
  funext n
  have hn : ((|n| : ℤ) : ℂ) = ((|(n : ℝ)| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_intCast, Int.cast_abs]
  have hm : ((|n| : ℤ) : ℂ) ^ (1 + (s : ℂ)) = ((|(n : ℝ)| ^ (1 + s) : ℝ) : ℂ) := by
    rw [hn, Complex.ofReal_cpow (abs_nonneg _)]
    push_cast
    rfl
  rw [hm, Complex.ofReal_zero]
  simp only [mul_zero, zero_mul, Complex.exp_zero]
  rw [periodicZetaWeight, Real.rpow_neg (abs_nonneg _)]
  push_cast
  ring

/-- The zero Fourier coefficient of the periodic zeta combination: `-2 K_s ζ(1+s)`. -/
theorem fourierCoeff_periodicZeta_zero (s : RieszExponent) :
    fourierCoeff (fun t : UnitAddCircle => (periodicZeta s t : ℂ)) 0 =
      -2 * (periodicZetaConst s.val : ℂ) * riemannZeta (1 + (s.val : ℂ)) := by
  rw [fourierCoeff_periodicZeta]
  simp only [↓reduceIte]
  rw [(hasSum_periodicZetaWeight_riemannZeta s.2.1).tsum_eq]
  ring

end Riesz1

end
