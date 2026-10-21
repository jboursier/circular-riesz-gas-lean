/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.SeminormScalingConverse
public import Riesz1.Frozen.CircleSobolev
public import Riesz1.Frozen.CircleVariance
public import Riesz1.Frozen.LineVariance
public import Riesz1.Frozen.TestAtScale
public import Riesz1.Frozen.TestAtScaleL2
public import Riesz1.Frozen.ZeroExtensionL2
public import Riesz1.Frozen.CompactProfile
public import Riesz1.Frozen.RepresentsZeroExtension

/-!
# Scale comparison of the variance parameters for a compact profile

Assertion 4 of the admissibility regularity lemma and the variance finiteness it implies,
reduced to the line Sobolev membership of the zero extension. Let `ξ₀` be the zero extension
of a compact profile `p`, supported in `[-ρ, ρ]` with `0 < ρ < 1/2`. The unit-circle test at
scale `a` agrees almost everywhere with the pullback of the periodization of `ξ₀`
(`Riesz1.testAtScale_ae_eq_pullback`).
Hence the circle seminorm at scale `a` is the seminorm of that pullback, and the comparison of
`Riesz1.seminorm_scaling_full` gives `|σ_a² − σ_0²| ≤ C a^{2−s}`.

Theorem: `Riesz1.Internal.compact_variance_of_line_membership`. Its hypothesis, that the zero
extension lies in `H^{(1-s)/2}(ℝ)`, is the line membership assertion of the admissibility
regularity lemma. It is not proved here.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

/-- The zero extension vanishes outside `(-1/2, 1/2)`. -/
theorem zeroExtension_eq_zero_of_half_le {p : Profile} {z : ℝ} (hz : 1 / 2 ≤ |z|) :
    zeroExtension p z = 0 := by
  unfold zeroExtension
  split_ifs with h
  · exact absurd h (not_lt.mpr hz)
  · rfl

/-- The pullback periodization of the zero extension at a point with `|z| < 1/2` is the zero
extension at `z / ℓ`, for a scale `0 < ℓ ≤ 1`: the other lattice translates vanish. -/
theorem pullbackPeriodization_coe_of_abs_lt (p : Profile) {ell z : ℝ} (hell0 : 0 < ell)
    (hell1 : ell ≤ 1) (hz : |z| < 1 / 2) :
    pullbackPeriodization (zeroExtension p) ell (z : UnitAddCircle) =
      ((zeroExtension p (z / ell) : ℝ) : ℂ) := by
  unfold pullbackPeriodization
  rw [AddCircle.liftIoc_coe_apply]
  · rw [tsum_eq_single 0]
    · simp
    · intro n hn
      rw [zeroExtension_eq_zero_of_half_le]
      · simp
      · -- For a nonzero integer `n`, `|z + n| ≥ 1/2`, and dividing by `ell ≤ 1` only grows it.
        have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
          have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
          exact_mod_cast this
        have hsum : 1 / 2 ≤ |z + n| := by
          have h1 : |(n : ℝ)| ≤ |z + n| + |z| := by
            have := abs_sub (z + n) z
            simp only [add_sub_cancel_left] at this
            linarith [abs_sub_comm (z + n) z]
          linarith
        have hdiv : |z + n| ≤ |(z + n) / ell| := by
          rw [abs_div, abs_of_pos hell0]
          exact (le_div_iff₀ hell0).mpr (by nlinarith [abs_nonneg (z + n)])
        exact le_trans (by linarith) hdiv
  · -- `z` lies in the central interval `(-1/2, 1/2]` of the periodization.
    exact ⟨by linarith [neg_abs_le z], by linarith [le_abs_self z]⟩

/-- The unit-circle test at scale `ℓ` is the rescaled zero extension at every point with
`|z| < 1/2`. -/
theorem testAtScale_coe_of_abs_lt (p : Profile) {ell : Scale} {z : ℝ} (hz : |z| < 1 / 2) :
    testAtScale p ell (z : UnitAddCircle) = zeroExtension p (z / ell.val) := by
  unfold testAtScale
  split_ifs with h1
  · rw [h1, div_one]
    unfold zeroExtension
    split_ifs with h
    · rfl
    · exact absurd hz h
  · unfold rescaledProfile
    congr 1
    -- The central representative of `z` is `z` itself.
    have hmem : z ∈ Ico (-(unitLength.val) / 2) (-(unitLength.val) / 2 + unitLength.val) := by
      change z ∈ Ico (-(1 : ℝ) / 2) (-(1 : ℝ) / 2 + 1)
      exact ⟨by linarith [neg_abs_le z], by linarith [le_abs_self z]⟩
    have hc : centralRep unitLength (z : UnitAddCircle) = z := by
      have : Fact (0 < unitLength.val) := ⟨unitLength.property⟩
      unfold centralRep
      exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hmem)
    rw [hc]

/-- The normalized Haar measure on the unit circle is the Lebesgue measure `volume`. -/
theorem haarAddCircle_eq_volume :
    (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

/-- The point `1/2` of the unit circle is a null set. It is the image of the single point `1/2`
of the period window `(-1/2, 1/2]`, and the image map from that window is measure preserving. -/
theorem volume_singleton_half :
    volume ({((1 / 2 : ℝ) : UnitAddCircle)} : Set UnitAddCircle) = 0 := by
  have hmp := AddCircle.measurePreserving_mk 1 (-(1 / 2 : ℝ))
  rw [← hmp.measure_preimage (measurableSet_singleton _).nullMeasurableSet,
    Measure.restrict_apply' measurableSet_Ioc]
  refine measure_mono_null (t := {1 / 2}) ?_ (measure_singleton _)
  rintro y ⟨hy1, hy2⟩
  have h12 : (1 / 2 : ℝ) ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by norm_num
  have heq : (y : UnitAddCircle) = ((1 / 2 : ℝ) : UnitAddCircle) := hy1
  rw [AddCircle.coe_eq_coe_iff_of_mem_Ioc hy2 h12] at heq
  exact heq

/-- Almost everywhere equal functions on the unit circle have equal Fourier coefficients. -/
theorem fourierCoeff_congr_ae {f g : UnitAddCircle → ℂ} (h : f =ᵐ[volume] g) (k : ℤ) :
    fourierCoeff f k = fourierCoeff g k := by
  unfold fourierCoeff
  refine integral_congr_ae ?_
  rw [haarAddCircle_eq_volume]
  filter_upwards [h] with t ht
  rw [ht]

/-- The circle Sobolev seminorm depends only on the almost everywhere class of the function. -/
theorem circleSobolevSq_congr_ae {r : ℝ} {f g : UnitAddCircle → ℂ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (h : f =ᵐ[volume] g) :
    circleSobolevSq r ⟨f, hf⟩ = circleSobolevSq r ⟨g, hg⟩ := by
  unfold circleSobolevSq
  refine tsum_congr fun k => ?_
  rw [fourierCoeff_congr_ae h k]

/-- The unit-circle test at scale `ℓ` agrees almost everywhere with the pullback of the
periodization of its zero extension. -/
theorem testAtScale_ae_eq_pullback (p : Profile) (ell : Scale) :
    (fun x => (testAtScale p ell x : ℂ)) =ᵐ[volume]
      pullbackPeriodization (zeroExtension p) ell.val := by
  -- Only the point `1/2 = -1/2` of the circle is left out.
  have hnull : ∀ᵐ x : UnitAddCircle ∂volume, x ≠ ((1 / 2 : ℝ) : UnitAddCircle) := by
    refine ae_iff.2 ?_
    simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
    exact volume_singleton_half
  filter_upwards [hnull] with x hx
  have : Fact (0 < unitLength.val) := ⟨unitLength.property⟩
  have hxz : ((centralRep unitLength x : ℝ) : UnitAddCircle) = x := by
    unfold centralRep
    exact AddCircle.coe_equivIco
  have hmem : -(1 / 2 : ℝ) ≤ centralRep unitLength x ∧ centralRep unitLength x < 1 / 2 := by
    have h := (AddCircle.equivIco unitLength.val (-unitLength.val / 2) x).property
    change -(1 : ℝ) / 2 ≤ centralRep unitLength x ∧
      centralRep unitLength x < -(1 : ℝ) / 2 + 1 at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hne : centralRep unitLength x ≠ -(1 / 2 : ℝ) := by
    intro hc
    apply hx
    rw [← hxz, hc, ← AddCircle.coe_add_period (1 : ℝ) (-(1 / 2 : ℝ))]
    norm_num
  have hlt : |centralRep unitLength x| < 1 / 2 := by
    rw [abs_lt]
    exact ⟨lt_of_le_of_ne hmem.1 (Ne.symm hne), hmem.2⟩
  obtain ⟨z, hzlt, rfl⟩ : ∃ z : ℝ, |z| < 1 / 2 ∧ x = (z : UnitAddCircle) :=
    ⟨centralRep unitLength x, hlt, hxz.symm⟩
  rw [testAtScale_coe_of_abs_lt p hzlt,
    pullbackPeriodization_coe_of_abs_lt p ell.property.1 ell.property.2 hzlt]

/-- The Riesz constant is positive for `0 < s < 1`. -/
theorem rieszConstant_pos (s : RieszExponent) : 0 < rieszConstant s := by
  obtain ⟨h0, h1⟩ := s.property
  unfold rieszConstant
  have hA : 0 < (1 - s.val) / 2 := by linarith
  have hB : 0 < s.val / 2 := by linarith
  have hG1 := Real.Gamma_pos_of_pos hA
  have hG2 := Real.Gamma_pos_of_pos hB
  have hsqrt : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  positivity

/-- Elementary comparison of the two variance expressions, from the scaled Sobolev comparison.
Both variance expressions are `ofReal(weight) * seminorm`. The powers `a^{-s}` and `a^{s}` cancel
in the difference, and the comparison bound contributes `a² a^{-s} = a^{2-s}`. -/
theorem abs_variance_sub_le {K s a Cs M : ℝ} (hK : 0 ≤ K) (ha : 0 < a) {Sc Sl : ENNReal}
    (hcomp : |Sc.toReal - a ^ s * Sl.toReal| ≤ Cs * a ^ 2 * M) :
    |(ENNReal.ofReal (K * a ^ (-s)) * Sc).toReal - (ENNReal.ofReal K * Sl).toReal| ≤
      K * Cs * M * a ^ (2 - s) := by
  have hpos : 0 < a ^ s := Real.rpow_pos_of_pos ha s
  have hinv : a ^ (-s) * a ^ s = 1 := by
    rw [Real.rpow_neg ha.le, inv_mul_cancel₀ hpos.ne']
  have hneg : 0 ≤ a ^ (-s) := (Real.rpow_pos_of_pos ha (-s)).le
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hK hneg),
    ENNReal.toReal_ofReal hK]
  have key : K * a ^ (-s) * Sc.toReal - K * Sl.toReal =
      K * a ^ (-s) * (Sc.toReal - a ^ s * Sl.toReal) := by
    linear_combination (K * Sl.toReal) * hinv
  rw [key, abs_mul, abs_of_nonneg (mul_nonneg hK hneg)]
  have hpow2 : a ^ (2 - s) = a ^ 2 * a ^ (-s) := by
    rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_two]
  rw [hpow2]
  calc K * a ^ (-s) * |Sc.toReal - a ^ s * Sl.toReal|
      ≤ K * a ^ (-s) * (Cs * a ^ 2 * M) :=
        mul_le_mul_of_nonneg_left hcomp (mul_nonneg hK hneg)
    _ = K * Cs * M * (a ^ 2 * a ^ (-s)) := by ring

namespace Internal

/-- **Scale comparison of the variance parameters for a compact profile (internal).** Let `p` be a
compact profile, let `f0` represent its zero extension, and assume that the zero extension lies in
`H^{(1-s)/2}(ℝ)`. Then the line variance `σ_0²` is finite, and for some `C1 > 0` and every scale
`0 < a ≤ 1` the unit-circle test at scale `a` lies in `H^{(1-s)/2}(𝕋)` with finite circle variance
`σ_a²`, and `|σ_a² − σ_0²| ≤ C1 a^{2−s}`. The hypothesis on `f0` is the line membership assertion
of the admissibility regularity lemma, which this declaration does not prove. -/
theorem compact_variance_of_line_membership (P : Parameters) (p : Profile) (hp : CompactProfile p)
    (f0 : Lp ℂ 2 (volume : Measure ℝ)) (hf0 : RepresentsZeroExtension p f0)
    (hline : LineSobolev ((1 - P.val.2) / 2) f0) :
    lineVariance P f0 < ⊤ ∧ ∃ C1 : ℝ, 0 < C1 ∧ ∀ a : Scale,
      CircleSobolev ((1 - P.val.2) / 2) (fun x => (testAtScale p a x : ℂ)) ∧
        circleVariance P p a < ⊤ ∧
        |(circleVariance P p a).toReal - (lineVariance P f0).toReal| ≤
          C1 * a.val ^ (2 - P.val.2) := by
  obtain ⟨ρ, hρ0, hρ1, hsupp⟩ := hp
  have hs0 : 0 < P.val.2 := P.property.2.1
  have hs1 : P.val.2 < 1 := P.property.2.2
  have hd0 : (0 : ℝ) < 1 / 2 - ρ := by linarith
  have hd1 : (1 / 2 - ρ : ℝ) < 1 / 2 := by linarith
  obtain ⟨C, hC, hcomp⟩ := seminorm_scaling_full hs0 hs1 hd0 hd1
  have hsupp' : ∀ᵐ x : ℝ ∂volume, 1 / 2 - (1 / 2 - ρ) < |x| → zeroExtension p x = 0 := by
    filter_upwards [hsupp] with x hx h
    exact hx (by linarith)
  -- The representative of `f0` is the `L²` class of the zero extension.
  have hf0eq : f0 = (zeroExtensionL2 p).toLp _ :=
    Lp.ext (hf0.trans (zeroExtensionL2 p).coeFn_toLp.symm)
  subst hf0eq
  set K : ℝ := (2 * Real.pi) ^ (1 - P.val.2) /
    (2 * P.val.1 * rieszConstant (parametersExponent P)) with hKdef
  set M : ℝ := ∫ x, zeroExtension p x ^ 2 with hMdef
  have hK : 0 ≤ K := by
    have hc : 0 < rieszConstant (parametersExponent P) := rieszConstant_pos _
    have hb : 0 < P.val.1 := P.property.1
    rw [hKdef]
    positivity
  have hM : 0 ≤ M := integral_nonneg fun x => sq_nonneg _
  have hC1 : 0 ≤ K * C * M := mul_nonneg (mul_nonneg hK hC.le) hM
  refine ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hline, K * C * M + 1, by linarith, ?_⟩
  intro a
  obtain ⟨hF, hfin, hb⟩ := (hcomp a.val (zeroExtension p) (zeroExtensionL2 p) a.property.1
    a.property.2 hsupp').1 hline
  have hS := circleSobolevSq_congr_ae (r := (1 - P.val.2) / 2) (testAtScaleL2 p a) hF
    (testAtScale_ae_eq_pullback p a)
  have hfinT : circleSobolevSq ((1 - P.val.2) / 2)
      ⟨fun x => (testAtScale p a x : ℂ), testAtScaleL2 p a⟩ < ⊤ := by
    rw [hS]
    exact hfin
  have ha : 0 < a.val := a.property.1
  have hb' := abs_variance_sub_le (Cs := C) (M := M) hK ha
    (Sc := circleSobolevSq ((1 - P.val.2) / 2) ⟨fun x => (testAtScale p a x : ℂ),
      testAtScaleL2 p a⟩)
    (Sl := lineSobolevSq ((1 - P.val.2) / 2) ((zeroExtensionL2 p).toLp _)) (by
      rw [hS]
      exact hb)
  refine ⟨⟨testAtScaleL2 p a, hfinT⟩, ?_, ?_⟩
  · unfold circleVariance
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinT
  · unfold circleVariance lineVariance
    have hpow : (0 : ℝ) ≤ a.val ^ (2 - P.val.2) := Real.rpow_nonneg ha.le _
    calc _ ≤ K * C * M * a.val ^ (2 - P.val.2) := hb'
      _ ≤ (K * C * M + 1) * a.val ^ (2 - P.val.2) := by nlinarith

end Internal

end Riesz1
