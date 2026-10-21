/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleFourierPairing
public import Riesz1.Variance.LoopMasterScaling
public import Riesz1.Variance.LoopMasterTransport
public import Riesz1.Variance.AuxiliaryMixedApprox
public import Riesz1.Frozen.CircleSobolevSq

/-!
# The Sobolev form of the covariance in the mixed mean-field variance

For real `L²` profiles `f` and `η` on the unit circle, with `φ` the unit transport of `η`, the
covariance pairing `-∫ f φ'` is a weighted sum of Fourier coefficient products. Polarization
turns that sum into the circle variance parameters:

`-∫ f φ' = ((2π)^{1-s}/(2βR)) · (H(f) + H(η) - H(f - η)) / 2`,

where `H(g) = Σ_k |k|^{1-s} |ĝ_k|²` is the seminorm of `circleSobolevSq`.

The main results are `Riesz1.hasSum_covariance_pairing`, `Riesz1.hasSum_sobolev_polarization` and
`Riesz1.toReal_circleSobolevSq_eq_tsum`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology ComplexConjugate Real
open scoped ContDiff ENNReal

namespace Riesz1

/-- The derivative of a constant multiple of a smooth circle function. -/
lemma loopMasterCircleDeriv_const_mul (c : ℝ) (f : UnitAddCircle → ℝ) (hf : IsSmoothCircle f) :
    loopMasterCircleDeriv (fun w => c * f w)
        (show IsSmoothCircle (fun w => c * f w) by unfold IsSmoothCircle at hf ⊢; exact contDiff_const.mul hf) =
      fun z => c * loopMasterCircleDeriv f hf z := by
  funext z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [loopMasterCircleDeriv_coe, loopMasterCircleDeriv_coe]
  have hd : DifferentiableAt ℝ (fun u : ℝ => f (u : UnitAddCircle)) x :=
    (hf.differentiable (by simp)).differentiableAt
  exact deriv_const_mul c hd

/-- The modulus of `2πk` is `2π` times the modulus of `k`, so the transport weight factors. -/
lemma abs_two_pi_mul_rpow (s : ℝ) (k : ℤ) :
    |2 * π * (k : ℝ)| ^ s = (2 * π) ^ s * |(k : ℝ)| ^ s := by
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), Real.mul_rpow (by positivity)
    (abs_nonneg _)]

/-- **Covariance pairing in Sobolev form (unit circle).** For a real `L²` function `f` and a
smooth transport `φ` of a smooth `η`, the sum over `k` of the weighted real parts of
`conj(f̂_k) η̂_k` has sum `-∫ f φ'`, with the prefactor `(2π)^{1-s}/(2βR)`. -/
theorem hasSum_covariance_pairing (P : Parameters) (f η φ : UnitAddCircle → ℝ)
    (hf : MemLp (fun x : UnitAddCircle => (f x : ℂ)) 2 volume)
    (hη : IsSmoothCircle η) (hφ : IsSmoothCircle φ)
    (htr : ∀ k : ℤ, circleCoeff φ k = transportCoeffs P unitLength (loopMasterTest η hη) k) :
    HasSum (fun k : ℤ => ((2 * π) ^ (1 - P.val.2) /
        (2 * P.val.1 * rieszConstant (parametersExponent P))) *
        (|(k : ℝ)| ^ (1 - P.val.2) * (conj (circleCoeff f k) * circleCoeff η k).re))
      (-∫ x, f x * loopMasterCircleDeriv φ hφ x) := by
  have h := hasSum_neg_integral_mul_deriv_transport P f η φ hf hη hφ htr
  convert h using 1
  funext k
  rw [abs_two_pi_mul_rpow]
  ring

/-- The Sobolev seminorm of a real `L²` function, as a real series: `H(g) = Σ_k |k|^{1-s} |ĝ_k|²`. -/
lemma circleSobolevSq_eq_tsum_ofReal {s : ℝ} (hs : s < 1) (g : UnitAddCircle → ℝ)
    (hg : MemLp (fun x : UnitAddCircle => (g x : ℂ)) 2 volume) :
    circleSobolevSq ((1 - s) / 2) ⟨fun x : UnitAddCircle => (g x : ℂ), hg⟩ =
      ∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff g k‖ ^ 2) := by
  have hs1 : (1 - s) ≠ 0 := (by linarith : (0 : ℝ) < 1 - s).ne'
  unfold circleSobolevSq
  congr 1
  funext k
  by_cases hk : k = 0
  · subst hk
    simp [Real.zero_rpow hs1]
  · simp only [hk, ↓reduceIte]
    rw [show 2 * ((1 - s) / 2) = 1 - s by ring]
    rfl

/-- The real part identity for two complex numbers: `2 Re(conj a b) = |a|² + |b|² - |a - b|²`. -/
lemma two_mul_re_conj_mul (a b : ℂ) :
    2 * (conj a * b).re = ‖a‖ ^ 2 + ‖b‖ ^ 2 - ‖a - b‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
  ring

/-- The difference of two real `L²` functions on the unit circle, in the complex lift. -/
lemma memLp_sub_complex {f g : UnitAddCircle → ℝ}
    (hf : MemLp (fun x : UnitAddCircle => (f x : ℂ)) 2 volume)
    (hg : MemLp (fun x : UnitAddCircle => (g x : ℂ)) 2 volume) :
    MemLp (fun x : UnitAddCircle => ((fun y => f y - g y) x : ℂ)) 2 volume := by
  refine MemLp.ae_eq (Filter.Eventually.of_forall fun x => ?_) (hf.sub hg)
  simp [Complex.ofReal_sub]

/-- A real `L²` function on the unit circle with finite Sobolev seminorm has the real series of
its weighted squared coefficients, with sum the seminorm. -/
lemma hasSum_sobolevTerm_of_ne_top {s : ℝ} (hs : s < 1) (g : UnitAddCircle → ℝ)
    (hg : MemLp (fun x : UnitAddCircle => (g x : ℂ)) 2 volume)
    (hfin : circleSobolevSq ((1 - s) / 2) ⟨fun x : UnitAddCircle => (g x : ℂ), hg⟩ ≠ ⊤) :
    HasSum (fun k : ℤ => |(k : ℝ)| ^ (1 - s) * ‖circleCoeff g k‖ ^ 2)
      (circleSobolevSq ((1 - s) / 2) ⟨fun x : UnitAddCircle => (g x : ℂ), hg⟩).toReal := by
  rw [circleSobolevSq_eq_tsum_ofReal hs g hg] at hfin ⊢
  have hnn : ∀ k : ℤ, 0 ≤ |(k : ℝ)| ^ (1 - s) * ‖circleCoeff g k‖ ^ 2 := fun k =>
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)
  have key : (∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff g k‖ ^ 2)).toReal =
      ∑' k : ℤ, |(k : ℝ)| ^ (1 - s) * ‖circleCoeff g k‖ ^ 2 := by
    rw [ENNReal.tsum_toReal_eq (fun k => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun k => ENNReal.toReal_ofReal (hnn k)
  rw [key]
  have hsum := ENNReal.summable_toReal hfin
  have hfun : (fun k : ℤ => (ENNReal.ofReal (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff g k‖ ^ 2)).toReal) =
      fun k : ℤ => |(k : ℝ)| ^ (1 - s) * ‖circleCoeff g k‖ ^ 2 :=
    funext fun k => ENNReal.toReal_ofReal (hnn k)
  rw [hfun] at hsum
  exact hsum.hasSum

/-- **Sobolev form of the covariance pairing.** For real `L²` functions `f` and the smooth `η`
with finite seminorms, the pairing `-∫ f φ'` against the unit transport `φ` of `η` equals
`(2π)^{1-s}/(2βR)` times half the polarized seminorm `H(f) + H(η) - H(f - η)`. -/
theorem neg_integral_mul_deriv_eq_sobolev (P : Parameters) (f η φ : UnitAddCircle → ℝ)
    (hf : MemLp (fun x : UnitAddCircle => (f x : ℂ)) 2 volume)
    (hη : IsSmoothCircle η) (hφ : IsSmoothCircle φ)
    (htr : ∀ k : ℤ, circleCoeff φ k = transportCoeffs P unitLength (loopMasterTest η hη) k)
    (hfin_f : circleSobolevSq ((1 - P.val.2) / 2) ⟨fun x : UnitAddCircle => (f x : ℂ), hf⟩ ≠ ⊤)
    (hfin_η : circleSobolevSq ((1 - P.val.2) / 2)
      ⟨fun x : UnitAddCircle => (η x : ℂ), memLp_unitCircle_of_isSmoothCircle hη⟩ ≠ ⊤)
    (hfin_fη : circleSobolevSq ((1 - P.val.2) / 2)
      ⟨fun x : UnitAddCircle => ((fun y => f y - η y) x : ℂ),
        memLp_sub_complex hf (memLp_unitCircle_of_isSmoothCircle hη)⟩ ≠ ⊤) :
    -∫ x, f x * loopMasterCircleDeriv φ hφ x =
      ((2 * π) ^ (1 - P.val.2) / (2 * P.val.1 * rieszConstant (parametersExponent P))) *
        (((circleSobolevSq ((1 - P.val.2) / 2) ⟨fun x : UnitAddCircle => (f x : ℂ), hf⟩).toReal +
          (circleSobolevSq ((1 - P.val.2) / 2)
            ⟨fun x : UnitAddCircle => (η x : ℂ), memLp_unitCircle_of_isSmoothCircle hη⟩).toReal -
          (circleSobolevSq ((1 - P.val.2) / 2)
            ⟨fun x : UnitAddCircle => ((fun y => f y - η y) x : ℂ),
              memLp_sub_complex hf (memLp_unitCircle_of_isSmoothCircle hη)⟩).toReal) / 2) := by
  have hs : P.val.2 < 1 := P.property.2.2
  have hηL2 := memLp_unitCircle_of_isSmoothCircle hη
  have hfη := memLp_sub_complex hf hηL2
  set s := P.val.2 with hsdef
  set c := (2 * π) ^ (1 - s) / (2 * P.val.1 * rieszConstant (parametersExponent P)) with hc
  have hA := hasSum_sobolevTerm_of_ne_top hs f hf hfin_f
  have hB := hasSum_sobolevTerm_of_ne_top hs η hηL2 hfin_η
  have hC := hasSum_sobolevTerm_of_ne_top hs (fun y => f y - η y) hfη hfin_fη
  -- The coefficients of the difference are the difference of the coefficients.
  have hcoeffC : ∀ k : ℤ, circleCoeff (fun y => f y - η y) k = circleCoeff f k - circleCoeff η k :=
    fun k => circleCoeff_sub_of_memLp f η hf hηL2 k
  simp only [hcoeffC] at hC
  have hcomb := (hA.add hB).sub hC
  have hD2 : HasSum (fun k : ℤ => 2 * (|(k : ℝ)| ^ (1 - s) *
      (conj (circleCoeff f k) * circleCoeff η k).re))
      ((circleSobolevSq ((1 - s) / 2) ⟨fun x : UnitAddCircle => (f x : ℂ), hf⟩).toReal +
        (circleSobolevSq ((1 - s) / 2) ⟨fun x : UnitAddCircle => (η x : ℂ), hηL2⟩).toReal -
        (circleSobolevSq ((1 - s) / 2) ⟨fun x : UnitAddCircle => ((fun y => f y - η y) x : ℂ),
          hfη⟩).toReal) := by
    convert hcomb using 1
    funext k
    have h2 := two_mul_re_conj_mul (circleCoeff f k) (circleCoeff η k)
    linear_combination (|(k : ℝ)| ^ (1 - s)) * h2
  have hD : HasSum (fun k : ℤ => |(k : ℝ)| ^ (1 - s) *
      (conj (circleCoeff f k) * circleCoeff η k).re)
      (((circleSobolevSq ((1 - s) / 2) ⟨fun x : UnitAddCircle => (f x : ℂ), hf⟩).toReal +
        (circleSobolevSq ((1 - s) / 2) ⟨fun x : UnitAddCircle => (η x : ℂ), hηL2⟩).toReal -
        (circleSobolevSq ((1 - s) / 2) ⟨fun x : UnitAddCircle => ((fun y => f y - η y) x : ℂ),
          hfη⟩).toReal) / 2) := by
    have h := hD2.div_const 2
    convert h using 1
    · funext k
      ring
  have hpair := hasSum_covariance_pairing P f η φ hf hη hφ htr
  have hmul := hD.mul_left c
  exact hpair.unique hmul

/-- The Sobolev seminorm of a difference is finite when those of the two terms are. -/
theorem circleSobolevSq_sub_ne_top {s : ℝ} (hs : s < 1) (f g : UnitAddCircle → ℝ)
    (hf : MemLp (fun x : UnitAddCircle => (f x : ℂ)) 2 volume)
    (hg : MemLp (fun x : UnitAddCircle => (g x : ℂ)) 2 volume)
    (hfin_f : circleSobolevSq ((1 - s) / 2) ⟨fun x : UnitAddCircle => (f x : ℂ), hf⟩ ≠ ⊤)
    (hfin_g : circleSobolevSq ((1 - s) / 2) ⟨fun x : UnitAddCircle => (g x : ℂ), hg⟩ ≠ ⊤) :
    circleSobolevSq ((1 - s) / 2)
      ⟨fun x : UnitAddCircle => ((fun y => f y - g y) x : ℂ), memLp_sub_complex hf hg⟩ ≠ ⊤ := by
  have hfg := memLp_sub_complex hf hg
  rw [circleSobolevSq_eq_tsum_ofReal hs (fun y => f y - g y) hfg]
  rw [circleSobolevSq_eq_tsum_ofReal hs f hf] at hfin_f
  rw [circleSobolevSq_eq_tsum_ofReal hs g hg] at hfin_g
  have hnn : ∀ (h : UnitAddCircle → ℝ) (k : ℤ), 0 ≤ |(k : ℝ)| ^ (1 - s) * ‖circleCoeff h k‖ ^ 2 :=
    fun h k => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)
  have hle : ∀ k : ℤ, ENNReal.ofReal (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff (fun y => f y - g y) k‖ ^ 2) ≤
      2 * ENNReal.ofReal (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff f k‖ ^ 2) +
        2 * ENNReal.ofReal (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff g k‖ ^ 2) := by
    intro k
    rw [circleCoeff_sub_of_memLp f g hf hg k]
    have hineq : ‖circleCoeff f k - circleCoeff g k‖ ^ 2 ≤
        2 * ‖circleCoeff f k‖ ^ 2 + 2 * ‖circleCoeff g k‖ ^ 2 := by
      have h1 := norm_sub_le (circleCoeff f k) (circleCoeff g k)
      have h2 : ‖circleCoeff f k - circleCoeff g k‖ ^ 2 ≤ (‖circleCoeff f k‖ + ‖circleCoeff g k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖circleCoeff f k‖ - ‖circleCoeff g k‖)]
    have hw : 0 ≤ |(k : ℝ)| ^ (1 - s) := Real.rpow_nonneg (abs_nonneg _) _
    have hval : |(k : ℝ)| ^ (1 - s) * ‖circleCoeff f k - circleCoeff g k‖ ^ 2 ≤
        2 * (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff f k‖ ^ 2) +
          2 * (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff g k‖ ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hineq hw]
    have e2 : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal (2 * t) = 2 * ENNReal.ofReal t := fun t ht => by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    have ht1 : 0 ≤ |(k : ℝ)| ^ (1 - s) * ‖circleCoeff f k‖ ^ 2 := hnn f k
    have ht2 : 0 ≤ |(k : ℝ)| ^ (1 - s) * ‖circleCoeff g k‖ ^ 2 := hnn g k
    calc ENNReal.ofReal (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff f k - circleCoeff g k‖ ^ 2)
        ≤ ENNReal.ofReal (2 * (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff f k‖ ^ 2) +
          2 * (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff g k‖ ^ 2)) := ENNReal.ofReal_le_ofReal hval
      _ = ENNReal.ofReal (2 * (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff f k‖ ^ 2)) +
          ENNReal.ofReal (2 * (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff g k‖ ^ 2)) :=
          ENNReal.ofReal_add (by linarith) (by linarith)
      _ = 2 * ENNReal.ofReal (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff f k‖ ^ 2) +
          2 * ENNReal.ofReal (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff g k‖ ^ 2) := by
          rw [e2 _ ht1, e2 _ ht2]
  have hbound : ∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff (fun y => f y - g y) k‖ ^ 2) ≤
      2 * ∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff f k‖ ^ 2) +
        2 * ∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff g k‖ ^ 2) := by
    calc _ ≤ ∑' k : ℤ, (2 * ENNReal.ofReal (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff f k‖ ^ 2) +
          2 * ENNReal.ofReal (|(k : ℝ)| ^ (1 - s) * ‖circleCoeff g k‖ ^ 2)) := ENNReal.tsum_le_tsum hle
      _ = _ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  refine ne_top_of_le_ne_top ?_ hbound
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top hfin_f,
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top hfin_g⟩

end Riesz1

end
