/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopMasterTransport
public import Riesz1.ToMathlib.Mollifier.Periodization
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Parseval pairing on the unit circle

For real square integrable `f` on the unit circle and a smooth real `φ`, the integral `∫ f φ'`
equals the sum of the products of the Fourier coefficients `conj(f̂_k) φ̂'_k`. This is Parseval's
identity for the Hilbert basis `fourierBasis`. With the transport coefficients
`transportCoeffs` this gives the weighted sum that identifies the covariance
in Proposition 5.6.

The main results are `Riesz1.hasSum_circleCoeff_conj_mul`, the pairing of two real `L²` functions,
and `Riesz1.hasSum_neg_integral_mul_deriv_transport`, the transport form of `-∫ f φ'`.
-/

@[expose] public section

open MeasureTheory Complex ComplexConjugate Real
open scoped ContDiff

namespace Riesz1

/-- A smooth real function on the unit circle is square integrable. -/
lemma memLp_unitCircle_of_isSmoothCircle {g : UnitAddCircle → ℝ} (hg : IsSmoothCircle g) :
    MemLp (fun x : UnitAddCircle => (g x : ℂ)) 2 volume := by
  have hc : Continuous g :=
    (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 hg.continuous
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine MemLp.of_bound (Complex.continuous_ofReal.comp hc).aestronglyMeasurable C ?_
  exact Filter.Eventually.of_forall fun z => by
    rw [Complex.norm_real]
    exact hC z (Set.mem_univ _)

/-- The Haar probability measure on the unit circle is the Lebesgue measure `volume`. -/
lemma volume_unitAddCircle_eq_haar :
    (volume : Measure UnitAddCircle) = (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

/-- Parseval's identity for the pairing of two real `L²` functions on the unit circle: the sum of
the products of their Fourier coefficients `conj(f̂_k) ĝ_k` is `∫ f g`. -/
theorem hasSum_circleCoeff_conj_mul (f g : UnitAddCircle → ℝ)
    (hf : MemLp (fun x : UnitAddCircle => (f x : ℂ)) 2 volume)
    (hg : MemLp (fun x : UnitAddCircle => (g x : ℂ)) 2 volume) :
    HasSum (fun k : ℤ => conj (circleCoeff f k) * circleCoeff g k)
      ((∫ x, f x * g x : ℝ) : ℂ) := by
  have hf' : MemLp (fun x : UnitAddCircle => (f x : ℂ)) 2
      (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    rw [← volume_unitAddCircle_eq_haar]; exact hf
  have hg' : MemLp (fun x : UnitAddCircle => (g x : ℂ)) 2
      (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    rw [← volume_unitAddCircle_eq_haar]; exact hg
  set F := hf'.toLp (fun x : UnitAddCircle => (f x : ℂ)) with hFdef
  set G := hg'.toLp (fun x : UnitAddCircle => (g x : ℂ)) with hGdef
  have hsum := (fourierBasis (T := 1)).hasSum_inner_mul_inner F G
  have hcoeffF : ∀ i : ℤ, fourierCoeff (⇑F) i = circleCoeff f i := fun i =>
    congrFun (fourierCoeff_congr_ae (hf'.coeFn_toLp)) i
  have hcoeffG : ∀ i : ℤ, fourierCoeff (⇑G) i = circleCoeff g i := fun i =>
    congrFun (fourierCoeff_congr_ae (hg'.coeFn_toLp)) i
  have hterm : ∀ i : ℤ, inner ℂ F ((fourierBasis (T := 1)) i) *
      inner ℂ ((fourierBasis (T := 1)) i) G = conj (circleCoeff f i) * circleCoeff g i := by
    intro i
    have hF : inner ℂ ((fourierBasis (T := 1)) i) F = circleCoeff f i := by
      rw [← (fourierBasis (T := 1)).repr_apply_apply, fourierBasis_repr, hcoeffF]
    have hG : inner ℂ ((fourierBasis (T := 1)) i) G = circleCoeff g i := by
      rw [← (fourierBasis (T := 1)).repr_apply_apply, fourierBasis_repr, hcoeffG]
    rw [← inner_conj_symm, hF, hG]
  have hinner : inner ℂ F G = ((∫ x, f x * g x : ℝ) : ℂ) := by
    have hae : ∀ᵐ x ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
        inner ℂ (F x) (G x) = ((f x * g x : ℝ) : ℂ) := by
      filter_upwards [hf'.coeFn_toLp, hg'.coeFn_toLp] with x h1 h2
      rw [hFdef, hGdef, h1, h2]
      simp only [RCLike.inner_apply, Complex.conj_ofReal, Complex.ofReal_mul]
      ring
    rw [L2.inner_def, integral_congr_ae hae, volume_unitAddCircle_eq_haar, integral_complex_ofReal]
  have key : (fun i : ℤ => inner ℂ F ((fourierBasis (T := 1)) i) *
      inner ℂ ((fourierBasis (T := 1)) i) G) =
        fun k : ℤ => conj (circleCoeff f k) * circleCoeff g k := funext hterm
  rw [key, hinner] at hsum
  exact hsum

/-- Parseval's identity in real form: the squared moduli of the Fourier coefficients of a real
`L²` function on the unit circle sum to its squared `L²` integral. -/
theorem hasSum_norm_sq_circleCoeff (f : UnitAddCircle → ℝ)
    (hf : MemLp (fun x : UnitAddCircle => (f x : ℂ)) 2 volume) :
    HasSum (fun k : ℤ => ‖circleCoeff f k‖ ^ 2) (∫ x, f x * f x) := by
  have h := hasSum_circleCoeff_conj_mul f f hf hf
  have hc : (fun k : ℤ => conj (circleCoeff f k) * circleCoeff f k) =
      fun k : ℤ => ((‖circleCoeff f k‖ ^ 2 : ℝ) : ℂ) := by
    funext k
    rw [Complex.conj_mul', Complex.ofReal_pow]
  rw [hc] at h
  exact Complex.hasSum_ofReal.mp h

/-- The Fourier coefficients of the derivative of a unit transport. -/
lemma circleCoeff_deriv_transport (P : Parameters) (η φ : UnitAddCircle → ℝ)
    (hη : IsSmoothCircle η) (hφ : IsSmoothCircle φ)
    (htr : ∀ k : ℤ, circleCoeff φ k = transportCoeffs P unitLength (loopMasterTest η hη) k)
    (k : ℤ) :
    circleCoeff (loopMasterCircleDeriv φ hφ) k =
      -((((1 / (2 * P.val.1 * rieszConstant (parametersExponent P))) *
        |2 * π * (k : ℝ)| ^ (1 - P.val.2) : ℝ) : ℂ) * circleCoeff η k) := by
  have hs : (1 - P.val.2) ≠ 0 := (by linarith [P.property.2.2] : (0 : ℝ) < 1 - P.val.2).ne'
  rw [loopMaster_transport_derivative_coeff P η φ hη hφ htr k, fractionalLaplacianCoeffs_unit]
  by_cases hk : k = 0
  · subst hk
    simp [Real.zero_rpow hs]
  · simp only [hk, ite_false, show 2 * ((1 - P.val.2) / 2) = 1 - P.val.2 by ring]
    push_cast
    ring

/-- The transport form of `-∫ f φ'`: the real parts of the weighted coefficient products have
sum `-∫ f φ'`, with the weight `(1/(2βR)) |2πk|^{1-s}`. -/
theorem hasSum_neg_integral_mul_deriv_transport (P : Parameters) (f η φ : UnitAddCircle → ℝ)
    (hf : MemLp (fun x : UnitAddCircle => (f x : ℂ)) 2 volume)
    (hη : IsSmoothCircle η) (hφ : IsSmoothCircle φ)
    (htr : ∀ k : ℤ, circleCoeff φ k = transportCoeffs P unitLength (loopMasterTest η hη) k) :
    HasSum (fun k : ℤ => (1 / (2 * P.val.1 * rieszConstant (parametersExponent P))) *
        |2 * π * (k : ℝ)| ^ (1 - P.val.2) * (conj (circleCoeff f k) * circleCoeff η k).re)
      (-∫ x, f x * loopMasterCircleDeriv φ hφ x) := by
  have hd := hasSum_circleCoeff_conj_mul f (loopMasterCircleDeriv φ hφ) hf
    (memLp_unitCircle_of_isSmoothCircle (loopMasterCircleDeriv_smooth hφ))
  have hc : (fun k : ℤ => conj (circleCoeff f k) * circleCoeff (loopMasterCircleDeriv φ hφ) k) =
      fun k : ℤ => -(((1 / (2 * P.val.1 * rieszConstant (parametersExponent P))) *
        |2 * π * (k : ℝ)| ^ (1 - P.val.2) : ℝ) : ℂ) * (conj (circleCoeff f k) * circleCoeff η k) := by
    funext k
    rw [circleCoeff_deriv_transport P η φ hη hφ htr k]
    ring
  rw [hc] at hd
  have hneg := hd.neg
  have hre := Complex.hasSum_re hneg
  simpa only [neg_neg, Complex.re_ofReal_mul, neg_mul, Complex.neg_re, Complex.ofReal_re] using hre

end Riesz1

end
