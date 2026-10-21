/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.NondegeneracyCompact
public import Riesz1.Kernel.AdmissibilityRegularityProfileFourier
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Positivity and lower semicontinuity over observation scales

The compactness step of the nondegeneracy argument for Theorem 3.
Lower semicontinuity suffices for the positive minimum argument.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Riesz1
namespace Internal

lemma nondegeneracy_const_scaled_zero (p : Profile) (hp : CompactProfile p)
    (a : Scale) {c : ℝ} (hc : testAtScale p a =ᵐ[volume] fun _ => c) :
    zeroExtension p =ᵐ[volume] fun _ => 0 := by
  have hco := (AddCircle.measurePreserving_mk 1 (-(1 / 2 : ℝ))).quasiMeasurePreserving.ae_eq_comp hc
  have hcell : ∀ᵐ z : ℝ, z ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) →
      zeroExtension p (z / a.val) = c := by
    have hh := (ae_restrict_iff' measurableSet_Ioc).mp hco
    filter_upwards [hh] with z hz hzi
    have hab : |z| < 1 / 2 := abs_lt.mpr hzi
    exact (testAtScale_coe_of_abs_lt p hab).symm.trans (hz ⟨hzi.1, by linarith [hzi.2]⟩)
  obtain ⟨r, hr, hrhalf, hs⟩ := hp
  have hscaled := (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ)
    (inv_ne_zero a.property.1.ne')).ae hs
  have hs' : ∀ᵐ z : ℝ, r ≤ |z / a.val| → zeroExtension p (z / a.val) = 0 := by
    simpa only [smul_eq_mul, div_eq_inv_mul] using hscaled
  have hczero : c = 0 := by
    have hex : volume (Ioo r (1 / 2 : ℝ)) ≠ 0 := by
      rw [Real.volume_Ioo]
      exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hrhalf)).ne'
    obtain ⟨z, hz, hzc, hzs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hex
      (ae_restrict_of_ae (hcell.and hs'))
    have hzpos : 0 < z := hr.trans hz.1
    have hzdiv : z ≤ z / a.val := (le_div_iff₀ a.property.1).mpr
      (mul_le_of_le_one_right hzpos.le a.property.2)
    exact (hzc ⟨by linarith, hz.2⟩).symm.trans
      (hzs (by rw [abs_of_pos (div_pos hzpos a.property.1)]; exact hz.1.le.trans hzdiv))
  have hback := (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ)
    a.property.1.ne').ae hcell
  filter_upwards [hback] with x hx
  by_cases hxi : |x| < 1 / 2
  · have hax : |a.val * x| < 1 / 2 := by
      rw [abs_mul, abs_of_pos a.property.1]
      exact (mul_le_of_le_one_left (abs_nonneg x) a.property.2).trans_lt hxi
    have he := hx (abs_lt.mp hax)
    simpa only [smul_eq_mul, mul_div_cancel_left₀ _ a.property.1.ne', hczero] using he
  · exact zeroExtension_eq_zero_of_half_le (le_of_not_gt hxi)

/-- At every positive scale a nonzero compact profile has positive seminorm. -/
lemma nondegeneracy_scale_seminorm_pos (p : Profile) (hp : CompactProfile p)
    (hz : ¬ zeroExtension p =ᵐ[volume] fun _ => 0) (a : Scale) (r : ℝ) :
    0 < circleSobolevSq r ⟨(fun x => (testAtScale p a x : ℂ)), testAtScaleL2 p a⟩ := by
  apply pos_iff_ne_zero.mpr
  intro hzero
  obtain ⟨c, hc⟩ := (circleSobolevSq_eq_zero_iff r _).mp hzero
  exact hz (nondegeneracy_const_scaled_zero p hp a
    (hc.mono fun _ hx => congrArg Complex.re hx))

/-- Each Fourier coefficient varies continuously with the observation scale. -/
lemma nondegeneracy_scale_coeff_continuous (p : Profile) (k : ℤ) :
    Continuous (fun a : Scale => fourierCoeff (fun x => (testAtScale p a x : ℂ)) k) := by
  have heq (a : Scale) : fourierCoeff (fun x => (testAtScale p a x : ℂ)) k =
      (a.val : ℂ) * (∫ x : ℝ, (zeroExtension p x : ℂ) *
        Complex.exp (((-(2 * Real.pi * (k : ℝ) * a.val) * x : ℝ) : ℂ) * Complex.I)) := by
    have hh := length_mul_periodizedProfile_coeff p a k
    rw [← testAtScale_coeff_eq_periodized] at hh
    change ((a.val⁻¹ : ℝ) : ℂ) * _ = _ at hh
    change ((a.val⁻¹ : ℝ) : ℂ) * _ =
      ∫ x : ℝ, (zeroExtension p x : ℂ) *
        Complex.exp (((-(2 * Real.pi * (k : ℝ) / a.val⁻¹) * x : ℝ) : ℂ) * Complex.I) at hh
    rw [div_inv_eq_mul] at hh
    calc _ = (a.val : ℂ) * (((a.val⁻¹ : ℝ) : ℂ) *
          fourierCoeff (fun x => (testAtScale p a x : ℂ)) k) := by
            rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ a.property.1.ne',
              Complex.ofReal_one, one_mul]
      _ = _ := congrArg (fun z : ℂ => (a.val : ℂ) * z) hh
  simp_rw [heq]
  exact (Complex.continuous_ofReal.comp continuous_subtype_val).mul
    ((continuous_zeroExtension_fourierIntegral p).comp
      (continuous_const.mul continuous_subtype_val))

/-- The nonnegative Fourier sum is lower semicontinuous, without a finiteness assumption. -/
lemma nondegeneracy_scale_seminorm_lowerSemicontinuous (p : Profile) (r : ℝ) :
    LowerSemicontinuous (fun a : Scale => circleSobolevSq r
      ⟨(fun x => (testAtScale p a x : ℂ)), testAtScaleL2 p a⟩) := by
  unfold circleSobolevSq
  apply lowerSemicontinuous_tsum
  intro k
  by_cases hk : k = 0
  · simp only [hk, ite_true]
    exact continuous_const.lowerSemicontinuous
  · simp only [hk, ite_false]
    exact (ENNReal.continuous_ofReal.comp
      (continuous_const.mul ((nondegeneracy_scale_coeff_continuous p k).norm.pow 2))).lowerSemicontinuous

lemma nondegeneracy_compact_away_zero (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (hz : ¬ zeroExtension p =ᵐ[volume] fun _ => 0)
    (hfin : ∀ a : Scale, circleVariance P p a < ⊤)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Scale, t ≤ a.val →
      c ≤ Real.sqrt (circleVariance P p a).toReal := by
  let S := fun a : Scale => circleSobolevSq ((1 - P.val.2) / 2)
    ⟨(fun x => (testAtScale p a x : ℂ)), testAtScaleL2 p a⟩
  let K : Set Scale := {a | t ≤ a.val}
  have hK : IsCompact K := by
    apply Topology.IsInducing.subtypeVal.isCompact_iff.mpr
    have heq : Subtype.val '' K = Icc t 1 := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨ha, a.property.2⟩
      · intro hx
        exact ⟨⟨x, ht.trans_le hx.1, hx.2⟩, hx.1, rfl⟩
    exact heq.symm ▸ isCompact_Icc
  have hne : K.Nonempty := ⟨⟨1, by norm_num⟩, ht1⟩
  obtain ⟨b, hb, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne hK
    ((nondegeneracy_scale_seminorm_lowerSemicontinuous p
      ((1 - P.val.2) / 2)).lowerSemicontinuousOn K)
  let A := (2 * Real.pi) ^ (1 - P.val.2) /
    (2 * P.val.1 * rieszConstant (parametersExponent P))
  have hA : 0 < A := by
    simpa only [Real.one_rpow, mul_one] using
      nondegeneracy_variance_prefactor_pos P ⟨1, by norm_num⟩
  have hSb : S b ≠ ⊤ := by
    have hf := hfin b
    change ENNReal.ofReal (A * b.val ^ (-P.val.2)) * S b < ⊤ at hf
    intro htop
    rw [htop, ENNReal.mul_top
      (ENNReal.ofReal_pos.mpr (nondegeneracy_variance_prefactor_pos P b)).ne'] at hf
    exact lt_irrefl _ hf
  have hpositive : 0 < (S b).toReal := ENNReal.toReal_pos
    (nondegeneracy_scale_seminorm_pos p hp hz b _).ne' hSb
  refine ⟨Real.sqrt (A * (S b).toReal), Real.sqrt_pos.mpr (mul_pos hA hpositive),
    fun a ha => Real.sqrt_le_sqrt ?_⟩
  have hpower : 1 ≤ a.val ^ (-P.val.2) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos a.property.1 a.property.2
      (neg_nonpos.mpr P.property.2.1.le)
  have hlow : ENNReal.ofReal A * S b ≤ circleVariance P p a :=
    mul_le_mul (ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right hA.le hpower))
      (hmin ha) zero_le zero_le
  have hr := ENNReal.toReal_mono (hfin a).ne hlow
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA.le] using hr

lemma nondegeneracy_compact_uniform_of_admissible (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (ell : Scales) (α : ℝ) (d : TestData)
    (h : Admissible P p ell α d)
    (hz : ¬ zeroExtension p =ᵐ[volume] fun _ => 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Scale, circleVariance P p a < ⊤ ∧
      c ≤ Real.sqrt (circleVariance P p a).toReal := by
  obtain ⟨c₀, t₀, hc₀, ht₀, hsmall⟩ :=
    nondegeneracy_compact_small_scales_of_admissible P p hp ell α d h hz
  obtain ⟨_, _, _, _, hcomp⟩ := admissible_compact_variance P p hp ell α d h
    ((zeroExtensionL2 p).toLp _) (zeroExtensionL2 p).coeFn_toLp
  have hfin (a : Scale) := (hcomp a).2.1
  let t := min t₀ 1 / 2
  have ht : 0 < t := half_pos (lt_min ht₀ one_pos)
  have ht1 : t ≤ 1 := by dsimp [t]; linarith [min_le_right t₀ (1 : ℝ)]
  obtain ⟨c₁, hc₁, hlarge⟩ := nondegeneracy_compact_away_zero P p hp hz hfin ht ht1
  refine ⟨min c₀ c₁, lt_min hc₀ hc₁, fun a => ⟨hfin a, ?_⟩⟩
  by_cases ha : a.val < t₀
  · exact (min_le_left _ _).trans (hsmall a ha).2
  · exact (min_le_right _ _).trans (hlarge a (by
      dsimp [t]
      linarith [min_le_left t₀ (1 : ℝ)]))

end Internal

/-- The unsmoothed compact variance has a uniform positive lower bound over
all observation scales. Constants precede every admissible sequence. This is
the compact minimum step of the nondegeneracy argument for Theorem 3. -/
theorem clt_nondegeneracy_compact_unsmoothed (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (α : ℝ) (d : TestData)
    (hz : ¬ zeroExtension p =ᵐ[volume] fun _ => 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ ell : Scales, Admissible P p ell α d →
      ∀ a : Scale, circleVariance P p a < ⊤ ∧
        c ≤ Real.sqrt (circleVariance P p a).toReal := by
  classical
  by_cases hex : ∃ ell : Scales, Admissible P p ell α d
  · obtain ⟨ell, hell⟩ := hex
    obtain ⟨c, hc, hb⟩ :=
      Internal.nondegeneracy_compact_uniform_of_admissible P p hp ell α d hell hz
    exact ⟨c, hc, fun _ _ => hb⟩
  · exact ⟨1, one_pos, fun ell hell => (hex ⟨ell, hell⟩).elim⟩

end Riesz1
