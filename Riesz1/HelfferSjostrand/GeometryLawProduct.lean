/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GeometryLawCoordinates

/-!
# The product law of the Gibbs coordinates `(z, ω)`

This is the product law part of Lemma 3.6. Under the Gibbs
probability `μ` of a pair Hamiltonian `H`, the coordinates `(z, ω)` of `Configuration N` have law
`ν_B ⊗ Unif(AddCircle √N)`. Here `ν_B` is the probability on the radial domain `B_N ⊂ e^⊥` with
density proportional to `e^{-H(z)}`, and `Unif` is the normalized Haar measure of the circle of
length `√N`, which is the normalized volume.

The proof uses `lintegral_configuration_fiber`: the Gibbs weight is a function of `z` alone
(`hsPairExpression_orthProj`), so each rectangle `s × t` has measure `ν_B(s)` times the normalized
circle measure of `t`. Two identities in `ℝ≥0∞` close the computation. The bijection and the local
isometry are proved in `Riesz1.HelfferSjostrand.GeometryLawBijection`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

theorem measurableSet_hsRadialDomain (N : ℕ+) : MeasurableSet (hsRadialDomain N) := by
  have hopen : IsOpen (Subtype.val ⁻¹' hsChamber N : Set (hsOrthSubspace N)) :=
    (isOpen_hsChamber N).preimage continuous_subtype_val
  exact hopen.measurableSet

theorem measurable_hsConfigCoord (N : ℕ+) : Measurable (hsConfigCoord N) :=
  (measurable_hsCoord N).comp
    ((PiLp.volume_preserving_toLp (Fin (N : ℕ))).measurable.comp measurable_subtype_coe)

/-- The radial density `e^{-H(z)}` on `B_N`, extended by zero to `e^⊥`. -/
def hsRadialDensity {c : ℝ} (χ : HsPairPotentials N c) (z : hsOrthSubspace N) : ℝ≥0∞ :=
  (hsRadialDomain N).indicator
    (fun z => ENNReal.ofReal (Real.exp (-hsPairExpression χ (z : HsEuclidean N)))) z

theorem measurable_hsRadialDensity {c : ℝ} (χ : HsPairPotentials N c) :
    Measurable (hsRadialDensity χ) := by
  classical
  have hcont : ContinuousOn (fun z : hsOrthSubspace N =>
      ENNReal.ofReal (Real.exp (-hsPairExpression χ (z : HsEuclidean N)))) (hsRadialDomain N) := by
    have hH : ContinuousOn (fun z : hsOrthSubspace N => hsPairExpression χ (z : HsEuclidean N))
        (hsRadialDomain N) :=
      (hsPairExpression_contDiffOn χ).continuousOn.comp continuous_subtype_val.continuousOn
        (fun _ hz => hz)
    exact ENNReal.continuous_ofReal.comp_continuousOn
      ((Real.continuous_exp.comp continuous_neg).comp_continuousOn hH)
  unfold hsRadialDensity
  rw [← piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise hcont continuousOn_const (measurableSet_hsRadialDomain N)

theorem support_hsRadialDensity {c : ℝ} (χ : HsPairPotentials N c) :
    Function.support (hsRadialDensity χ) ⊆ hsRadialDomain N := by
  intro z hz
  by_contra h
  exact hz (indicator_of_notMem h _)

/-- The Gibbs weight at a configuration is the radial density at its radial coordinate. -/
theorem hsConfigCoord_fst_mem (N : ℕ+) (X : Configuration N) :
    (hsConfigCoord N X).1 ∈ hsRadialDomain N := by
  have hx : (WithLp.toLp 2 X.val : HsEuclidean N) ∈ hsChamber N :=
    ⟨X.property.1, X.property.2.2.2⟩
  change hsOrthProj N (WithLp.toLp 2 X.val) ∈ hsChamber N
  rw [hsOrthProj_eq_translate]
  exact (hsTranslate_mem_chamber_iff _ _).mpr hx

theorem hsPairExpression_hsConfigCoord {c : ℝ} (χ : HsPairPotentials N c) (X : Configuration N) :
    hsPairExpression χ ((hsConfigCoord N X).1 : HsEuclidean N) = hsFundamentalHamiltonian χ X :=
  hsPairExpression_orthProj χ (WithLp.toLp 2 X.val)

theorem ofReal_exp_neg_hsFundamentalHamiltonian {c : ℝ} (χ : HsPairPotentials N c)
    (X : Configuration N) :
    ENNReal.ofReal (Real.exp (-hsFundamentalHamiltonian χ X)) =
      hsRadialDensity χ (hsConfigCoord N X).1 := by
  rw [hsRadialDensity, indicator_of_mem (hsConfigCoord_fst_mem N X),
    hsPairExpression_hsConfigCoord]

/-- The unnormalized radial measure `e^{-H(z)} dz` on `e^⊥`, supported in `B_N`. -/
def hsRadialMeasure {c : ℝ} (χ : HsPairPotentials N c) : Measure (hsOrthSubspace N) :=
  (volume : Measure (hsOrthSubspace N)).withDensity (hsRadialDensity χ)

theorem hsRadialMeasure_univ {c : ℝ} (χ : HsPairPotentials N c) :
    hsRadialMeasure χ univ = ∫⁻ z in hsRadialDomain N, hsRadialDensity χ z := by
  rw [hsRadialMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    setLIntegral_eq_of_support_subset (support_hsRadialDensity χ)]

theorem hsRadialMeasure_apply {c : ℝ} (χ : HsPairPotentials N c) {s : Set (hsOrthSubspace N)}
    (hs : MeasurableSet s) :
    hsRadialMeasure χ s = ∫⁻ z in hsRadialDomain N, s.indicator (hsRadialDensity χ) z := by
  have hsupp : Function.support (s.indicator (hsRadialDensity χ)) ⊆ hsRadialDomain N := by
    intro z hz
    by_contra h
    apply hz
    by_cases hzs : z ∈ s
    · rw [indicator_of_mem hzs, hsRadialDensity, indicator_of_notMem h]
    · exact indicator_of_notMem hzs _
  rw [setLIntegral_eq_of_support_subset hsupp, hsRadialMeasure, withDensity_apply _ hs,
    ← lintegral_indicator hs]

/-- The total radial mass `∫_{B_N} e^{-H}` is the partition function divided by `√N`. -/
theorem hsPartitionFunction_eq_radial {c : ℝ} (χ : HsPairPotentials N c) :
    hsPartitionFunction χ = hsRadialMeasure χ univ * ENNReal.ofReal (Real.sqrt (N : ℕ)) := by
  have hmeas := lintegral_configuration_fiber (G₁ := fun _ => (1 : ℝ≥0∞)) N
    (measurable_hsRadialDensity χ) measurable_const
  calc hsPartitionFunction χ
      = ∫⁻ X, hsRadialDensity χ (hsConfigCoord N X).1 * 1 ∂configurationVolume N := by
        rw [hsPartitionFunction_eq_lintegral]
        exact lintegral_congr fun X => by
          rw [mul_one, ofReal_exp_neg_hsFundamentalHamiltonian]
    _ = (∫⁻ z in hsRadialDomain N, hsRadialDensity χ z) * ∫⁻ _w, (1 : ℝ≥0∞) := hmeas
    _ = hsRadialMeasure χ univ * ENNReal.ofReal (Real.sqrt (N : ℕ)) := by
        rw [hsRadialMeasure_univ, lintegral_one, AddCircle.measure_univ]

theorem hsRadialMeasure_univ_ne_zero {c : ℝ} (χ : HsPairPotentials N c) :
    hsRadialMeasure χ univ ≠ 0 := by
  intro h
  have hZ := hsPartitionFunction_eq_radial χ
  rw [h, zero_mul] at hZ
  exact (hsPartitionFunction_pos χ).ne' hZ

theorem hsRadialMeasure_univ_ne_top {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c) :
    hsRadialMeasure χ univ ≠ ⊤ := by
  intro h
  have hZ := hsPartitionFunction_eq_radial χ
  have hs : ENNReal.ofReal (Real.sqrt (N : ℕ)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr N.pos))).ne'
  rw [h, ENNReal.top_mul hs] at hZ
  exact (hsPartitionFunction_lt_top χ hc).ne hZ

/-- The radial law `ν_B`: the probability on `B_N` with density proportional to `e^{-H(z)}`. -/
def hsRadialProbability {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c) :
    ProbabilityMeasure (hsOrthSubspace N) :=
  ⟨(hsRadialMeasure χ univ)⁻¹ • hsRadialMeasure χ, by
    rw [isProbabilityMeasure_iff, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (hsRadialMeasure_univ_ne_zero χ)
      (hsRadialMeasure_univ_ne_top χ hc)⟩

theorem hsRadialProbability_apply {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)
    (s : Set (hsOrthSubspace N)) :
    (hsRadialProbability χ hc : Measure (hsOrthSubspace N)) s =
      (hsRadialMeasure χ univ)⁻¹ * hsRadialMeasure χ s := by
  change ((hsRadialMeasure χ univ)⁻¹ • hsRadialMeasure χ) s = _
  rw [Measure.smul_apply, smul_eq_mul]

/-- The uniform probability on the circle `ℝ/√N ℤ`: the volume normalized to total mass one. -/
def hsUniformCircle (N : ℕ+) : ProbabilityMeasure (AddCircle (Real.sqrt (N : ℕ))) :=
  ⟨AddCircle.haarAddCircle, inferInstance⟩

theorem volume_eq_hsUniformCircle (N : ℕ+) :
    (volume : Measure (AddCircle (Real.sqrt (N : ℕ)))) =
      ENNReal.ofReal (Real.sqrt (N : ℕ)) • (hsUniformCircle N : Measure _) :=
  AddCircle.volume_eq_smul_haarAddCircle

theorem hsGibbsProbability_apply {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)
    {S : Set (Configuration N)} (hS : MeasurableSet S) :
    (hsGibbsProbability χ hc : Measure (Configuration N)) S =
      (hsPartitionFunction χ)⁻¹ *
        ∫⁻ X in S, ENNReal.ofReal (Real.exp (-hsFundamentalHamiltonian χ X))
          ∂configurationVolume N := by
  change ((hsPartitionFunction χ)⁻¹ • hsFundamentalWeight χ) S = _
  rw [Measure.smul_apply, smul_eq_mul, hsFundamentalWeight, withDensity_apply _ hS]

/-- Arithmetic in `ℝ≥0∞`: the normalizations `(m c)⁻¹` and `c` cancel. -/
theorem ennreal_inv_mul_mul_cancel {m c R H : ℝ≥0∞} (hm0 : m ≠ 0) (hmt : m ≠ ⊤)
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    (m * c)⁻¹ * (R * (c * H)) = m⁻¹ * R * H := by
  rw [ENNReal.mul_inv (Or.inl hm0) (Or.inl hmt)]
  have hcc : c⁻¹ * c = 1 := ENNReal.inv_mul_cancel hc0 hct
  calc m⁻¹ * c⁻¹ * (R * (c * H)) = m⁻¹ * R * H * (c⁻¹ * c) := by ring
    _ = m⁻¹ * R * H := by rw [hcc, mul_one]

/-- The indicator of a rectangle pulled back by the coordinates is the product of indicators of
the radial and circle coordinates, times the Gibbs weight written in `z` alone. -/
theorem indicator_hsConfigCoord {c : ℝ} (χ : HsPairPotentials N c) {s : Set (hsOrthSubspace N)}
    {t : Set (AddCircle (Real.sqrt (N : ℕ)))} (X : Configuration N) :
    (hsConfigCoord N ⁻¹' (s ×ˢ t)).indicator
        (fun X => ENNReal.ofReal (Real.exp (-hsFundamentalHamiltonian χ X))) X =
      s.indicator (hsRadialDensity χ) (hsConfigCoord N X).1 *
        t.indicator (fun _ => (1 : ℝ≥0∞)) (hsConfigCoord N X).2 := by
  classical
  by_cases h1 : (hsConfigCoord N X).1 ∈ s <;> by_cases h2 : (hsConfigCoord N X).2 ∈ t <;>
    simp [mem_preimage, mem_prod, h1, h2, ofReal_exp_neg_hsFundamentalHamiltonian]

/-- The product law: the law of `(z, ω)` under the Gibbs probability is the product of the radial
law `ν_B` and the uniform probability on the circle of length `√N`. -/
theorem hsGibbs_map_hsConfigCoord {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c) :
    (hsGibbsProbability χ hc : Measure (Configuration N)).map (hsConfigCoord N) =
      (hsRadialProbability χ hc : Measure (hsOrthSubspace N)).prod
        (hsUniformCircle N : Measure (AddCircle (Real.sqrt (N : ℕ)))) := by
  symm
  apply Measure.prod_eq
  intro s t hs ht
  have hS : MeasurableSet (hsConfigCoord N ⁻¹' (s ×ˢ t)) :=
    measurable_hsConfigCoord N (hs.prod ht)
  rw [Measure.map_apply (measurable_hsConfigCoord N) (hs.prod ht),
    hsGibbsProbability_apply χ hc hS, ← lintegral_indicator hS]
  have hint : ∫⁻ X, (hsConfigCoord N ⁻¹' (s ×ˢ t)).indicator
      (fun X => ENNReal.ofReal (Real.exp (-hsFundamentalHamiltonian χ X))) X
        ∂configurationVolume N =
      ∫⁻ X, s.indicator (hsRadialDensity χ) (hsConfigCoord N X).1 *
        t.indicator (fun _ => (1 : ℝ≥0∞)) (hsConfigCoord N X).2 ∂configurationVolume N :=
    lintegral_congr fun X => indicator_hsConfigCoord χ X
  rw [hint, lintegral_configuration_fiber N
    ((measurable_hsRadialDensity χ).indicator hs)
    (measurable_const.indicator ht), lintegral_indicator_const ht, one_mul,
    ← hsRadialMeasure_apply χ hs, hsPartitionFunction_eq_radial, hsRadialProbability_apply χ hc s,
    volume_eq_hsUniformCircle, Measure.smul_apply, smul_eq_mul]
  exact ennreal_inv_mul_mul_cancel (hsRadialMeasure_univ_ne_zero χ)
    (hsRadialMeasure_univ_ne_top χ hc) (ENNReal.ofReal_pos.mpr
      (Real.sqrt_pos.mpr (Nat.cast_pos.mpr N.pos))).ne'
    ENNReal.ofReal_ne_top

end Riesz1

end
