/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.FractionalLaplacianCoeffs
public import Riesz1.Frozen.ArcIndicator
public import Riesz1.Frozen.Admissible
public import Riesz1.Frozen.ArcCount
public import Riesz1.Frozen.BlDistance
public import Riesz1.Frozen.CircleSobolev
public import Riesz1.Frozen.CircleVariance
public import Riesz1.Frozen.CompactProfile
public import Riesz1.Frozen.Configuration
public import Riesz1.Frozen.ConvergesInLaw
public import Riesz1.Frozen.CountVariance
public import Riesz1.Frozen.CyclicLift
public import Riesz1.Frozen.Fluctuation
public import Riesz1.Frozen.GibbsMeasure
public import Riesz1.Frozen.LineSobolev
public import Riesz1.Frozen.LineVariance
public import Riesz1.Frozen.Mesoscopic
public import Riesz1.Frozen.ModelWellDefined
public import Riesz1.Frozen.NormalLaw
public import Riesz1.Frozen.NormalizedCount
public import Riesz1.Frozen.NormalizedGap
public import Riesz1.Frozen.NormalizedStatistic
public import Riesz1.Frozen.Parameters
public import Riesz1.Frozen.ParametersExponent
public import Riesz1.Frozen.ParticleNumber
public import Riesz1.Frozen.PeriodicZeta
public import Riesz1.Frozen.PowerExponent
public import Riesz1.Frozen.PowerRieszExponent
public import Riesz1.Frozen.PowerVariance
public import Riesz1.Frozen.Profile
public import Riesz1.Frozen.RepresentsZeroExtension
public import Riesz1.Frozen.RieszRepresentative
public import Riesz1.Frozen.Scale
public import Riesz1.Frozen.Scales
public import Riesz1.Frozen.StatisticLaws
public import Riesz1.Frozen.TestAtScale
public import Riesz1.Frozen.TestAtScaleL1
public import Riesz1.Frozen.TestData
public import Riesz1.Frozen.Variance

/-!
# Proved sanity checks

This module proves elementary sanity checks of the definitions. The analytic sanity obligations
are not proved here. This module has no proof slots.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz1

/-- The normalization is positive. -/
lemma rieszConstant_pos (s : RieszExponent) : 0 < rieszConstant s := by
  have hs := s.property.1
  have hs1 := s.property.2
  unfold rieszConstant
  exact div_pos
    (mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.sqrt_pos.mpr Real.pi_pos))
      (Real.Gamma_pos_of_pos (by linarith)))
    (Real.Gamma_pos_of_pos (by linarith))

/-- The library's even Hurwitz formula is precisely ζ(s,x)+ζ(s,1-x)
off the collision. -/
lemma rieszRepresentative_eq_hurwitz (s : RieszExponent) (x : UnitAddCircle) :
    rieszRepresentative s x =
      (HurwitzZeta.hurwitzZeta x (s.val : ℂ) + HurwitzZeta.hurwitzZeta (-x) (s.val : ℂ)).re := by
  rw [rieszRepresentative, HurwitzZeta.hurwitzZetaEven_eq]
  simp only [Complex.div_ofNat_re]
  ring

/-- Evenness is exact, including the library representative. See Lemma 2.1. -/
lemma rieszRepresentative_neg (s : RieszExponent) (x : UnitAddCircle) :
    rieszRepresentative s (-x) = rieszRepresentative s x := by
  simp only [rieszRepresentative, HurwitzZeta.hurwitzZetaEven_neg]

/-- The zeta combination vanishes at zero. -/
lemma periodicZeta_zero (s : RieszExponent) : periodicZeta s 0 = 0 := by
  simp [periodicZeta]

/-- The zeta combination is even. -/
lemma periodicZeta_neg (s : RieszExponent) (t : UnitAddCircle) : periodicZeta s (-t) = periodicZeta s t := by
  simp only [periodicZeta, HurwitzZeta.hurwitzZetaEven_neg]

/-- Nonzero Fourier modes have exactly the paper's seminorm normalization,
without a 2π factor. -/
lemma circleSobolevSq_fourier (r : ℝ) (k : ℤ) (hk : k ≠ 0) :
    circleSobolevSq r ⟨fourier k, ContinuousMap.memLp volume ℂ (fourier k)⟩ = ENNReal.ofReal (|(k : ℝ)| ^ (2 * r)) := by
  classical
  unfold circleSobolevSq
  rw [tsum_eq_single k]
  · simp [hk, fourierCoeff_fourier]
  · intro j hj
    simp [fourierCoeff_fourier, hj]

/-- Every Fourier mode is in H^r. -/
lemma circleSobolev_fourier (r : ℝ) (k : ℤ) : CircleSobolev r (fourier k) := by
  refine ⟨ContinuousMap.memLp volume ℂ (fourier k), ?_⟩
  by_cases hk : k = 0
  · subst k
    have h : circleSobolevSq r ⟨fourier 0, ContinuousMap.memLp volume ℂ (fourier 0)⟩ = 0 := by
      classical
      unfold circleSobolevSq
      have hterm (i : ℤ) :
          (if i = 0 then (0 : ℝ≥0∞) else
            ENNReal.ofReal (|(i : ℝ)| ^ (2 * r) * ‖fourierCoeff (fourier (T := 1) 0) i‖ ^ 2)) = 0 := by
        by_cases hi : i = 0 <;> simp [hi, fourierCoeff_fourier]
      simp only [hterm, tsum_zero]
    rw [h]
    exact ENNReal.zero_lt_top
  · rw [circleSobolevSq_fourier r k hk]
    exact ENNReal.ofReal_lt_top

/-- Fractional powers do not use a zero-frequency negative power. -/
lemma fractionalLaplacianCoeffs_zero (L : Length) (gamma : ℝ) (a : ℤ → ℂ) :
    fractionalLaplacianCoeffs L gamma a 0 = 0 := by
  simp [fractionalLaplacianCoeffs]

/-- The additive constant of the transport is fixed. -/
lemma transportCoeffs_zero (P : Parameters) (L : Length) (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}) :
    transportCoeffs P L f 0 = 0 := by
  simp [transportCoeffs]

/-- Zero variance gives the Dirac normal law. -/
lemma normalLaw_zero : normalLaw 0 = Measure.dirac 0 := by
  simp [normalLaw]

/-- All finite variance parameters give probability laws. -/
lemma normalLaw_probability (v : ℝ≥0) : IsProbabilityMeasure (normalLaw v) := by
  unfold normalLaw
  infer_instance

/-- Squared centered integrals cannot conceal an infinite second moment by
returning zero. -/
lemma variance_nonnegative {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) (F : Ω → ℝ) (hF : Integrable F mu) :
    0 ≤ variance mu F hF := zero_le

/-- The lift domain is measurable, so comap is the actual pullback measure. -/
lemma orderedDomain_measurable (N : ℕ+) : MeasurableSet (orderedDomain N) := by
  unfold orderedDomain
  change MeasurableSet {x : Fin (N : ℕ) → ℝ |
    (∀ i j, i < j → x i < x j) ∧ 0 ≤ x ⟨0, N.pos⟩ ∧
      x ⟨0, N.pos⟩ < 1 ∧ ∀ i, x i < x ⟨0, N.pos⟩ + 1}
  measurability

/-- All energy evaluations avoid the collision class. -/
lemma configuration_sub_ne_zero {N : ℕ+} (X : Configuration N)
    (i j : Fin (N : ℕ)) (hij : i ≠ j) :
    ((X.val i - X.val j : ℝ) : UnitAddCircle) ≠ 0 := by
  have h0 (a : Fin (N : ℕ)) : X.val ⟨0, N.pos⟩ ≤ X.val a :=
    X.property.1.monotone (Fin.zero_le a)
  have hlow : -1 < X.val i - X.val j := by
    have := X.property.2.2.2 j
    linarith [h0 i]
  have hupp : X.val i - X.val j < 1 := by
    have := X.property.2.2.2 i
    linarith [h0 j]
  intro h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff 1).mp h
  have hn' : (n : ℝ) = X.val i - X.val j := by simpa using hn
  have hn0 : n = 0 := by
    have h1 : (-1 : ℤ) < n := by exact_mod_cast (show (-1 : ℝ) < n by linarith)
    have h2 : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
    omega
  have heq : X.val i = X.val j := by simp [hn0] at hn'; linarith
  exact hij (X.property.1.injective heq)

/-- A single particle has no interaction energy. -/
lemma energy_one (s : RieszExponent) (X : Configuration 1) : energy s X = 0 := by
  classical
  have : Subsingleton (Fin ((1 : ℕ+) : ℕ)) := by rw [PNat.one_coe]; infer_instance
  unfold energy
  suffices hsum : (∑ i : Fin ((1 : ℕ+) : ℕ), ∑ j ∈ Finset.univ.erase i,
      rieszRepresentative s ((X.val i - X.val j : ℝ) : UnitAddCircle)) = 0 by rw [hsum, mul_zero]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  have heq : j = i := Subsingleton.elim _ _
  exact ((Finset.mem_erase.mp hj).1 heq).elim

/-- Cyclic lift agrees with the chosen coordinates on one period. -/
lemma cyclicLift_of_fin {N : ℕ+} (X : Configuration N) (i : Fin (N : ℕ)) :
    cyclicLift X i.val = X.val i := by
  have hi : (i.val : ℤ) < (N : ℕ) := by exact_mod_cast i.isLt
  simp [cyclicLift, Int.emod_eq_of_lt (by positivity) hi,
    Int.ediv_eq_zero_of_lt (by positivity) hi]

/-- An entire turn increases a lift by one. -/
lemma cyclicLift_add_period {N : ℕ+} (X : Configuration N) (j : ℤ) :
    cyclicLift X (j + (N : ℕ)) = cyclicLift X j + 1 := by
  simp [cyclicLift, Int.add_ediv_of_dvd_right]
  ring

/-- The Gibbs normalization algebra, conditional only as an internal helper.
The general positivity/finiteness test is an open obligation, not a hypothesis of any
proposition stated in the paper. -/
lemma internal_gibbs_probability_of_partition (P : Parameters) (N : ℕ+)
    (h0 : partitionFunction P N ≠ 0) (htop : partitionFunction P N ≠ ⊤) :
    IsProbabilityMeasure (gibbsMeasure P N) := by
  constructor
  change (partitionFunction P N)⁻¹ * partitionFunction P N = 1
  exact ENNReal.inv_mul_cancel h0 htop

/-- Fundamental volume is one for a single particle. -/
lemma configurationVolume_one : configurationVolume 1 Set.univ = 1 := by
  rw [configurationVolume,
    (MeasurableEmbedding.subtype_coe (orderedDomain_measurable 1)).comap_apply]
  have : Subsingleton (Fin ((1 : ℕ+) : ℕ)) := by rw [PNat.one_coe]; infer_instance
  have hdom : orderedDomain 1 = Set.univ.pi (fun _ : Fin ((1 : ℕ+) : ℕ) => Set.Ico (0 : ℝ) 1) := by
    ext x
    simp only [orderedDomain, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hx i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact ⟨hx.2.1, hx.2.2.1⟩
    · intro hx
      refine ⟨?_, (hx 0).1, (hx 0).2, ?_⟩
      · intro i j hij
        have : i = j := Subsingleton.elim _ _
        exact (hij.ne this).elim
      · intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        have hfirst : (⟨0, (1 : ℕ+).pos⟩ : Fin ((1 : ℕ+) : ℕ)) = 0 := Subsingleton.elim _ _
        rw [hfirst]
        linarith
  simp only [Set.image_univ, Subtype.range_coe]
  rw [hdom, volume_pi_pi]
  simp only [Real.volume_Ico, sub_zero, ENNReal.ofReal_one, Finset.prod_const_one]

/-- The partition function is exactly one for N=1. -/
lemma partitionFunction_one (P : Parameters) : partitionFunction P 1 = 1 := by
  simp only [partitionFunction, gibbsWeight, energy_one, mul_zero,
    Real.exp_zero, ENNReal.ofReal_one]
  rw [show (fun _ : Configuration 1 => (1 : ℝ≥0∞)) = 1 from rfl,
    withDensity_one, configurationVolume_one]

/-- Single-particle Gibbs law is a probability, without a partition hypothesis. -/
lemma gibbsMeasure_one_probability (P : Parameters) : IsProbabilityMeasure (gibbsMeasure P 1) :=
  internal_gibbs_probability_of_partition P 1
    (by rw [partitionFunction_one]; exact one_ne_zero)
    (by rw [partitionFunction_one]; exact ENNReal.one_ne_top)

/-- The displayed count/gap variance is strictly positive. See Corollary 1. -/
lemma countVariance_pos (P : Parameters) : 0 < countVariance P := by
  have hs := P.property.2.1
  have hb := P.property.1
  have hangle : 0 < Real.pi * P.val.2 / 2 := by positivity
  have hhalf : Real.pi * P.val.2 / 2 < Real.pi / 2 := by nlinarith [P.property.2.2, Real.pi_pos]
  have hsin : 0 < Real.sin (Real.pi * P.val.2 / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hangle (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos (Real.pi * P.val.2 / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hhalf⟩
  exact div_pos (div_pos hcos hsin) (by positivity)

/-- The zero function has zero line seminorm. -/
lemma lineSobolevSq_zero (r : ℝ) : lineSobolevSq r 0 = 0 := by
  simp [lineSobolevSq]

/-- The BL distance from a law to itself is zero. -/
lemma blDistance_self (mu : ProbabilityMeasure ℝ) : blDistance mu mu = 0 := by
  simp [blDistance]

/-- BL symmetry follows without changing its C¹ test class. -/
lemma blDistance_symm (mu nu : ProbabilityMeasure ℝ) : blDistance mu nu = blDistance nu mu := by
  unfold blDistance
  congr 1
  funext f
  rw [abs_sub_comm]

/-- Open arc indicators are L². Finiteness of their fractional seminorm is
proved separately in `Analytic.lean`. -/
lemma arcIndicator_memLp (center : UnitAddCircle) (a : ℝ) :
    MemLp (fun x => (arcIndicator center a x : ℂ)) 2 volume := by
  have hfun : (fun x => (arcIndicator center a x : ℂ)) =
      (Metric.ball center a).indicator (fun _ => (1 : ℂ)) := by
    funext x
    simp only [arcIndicator, Set.indicator, Metric.mem_ball]
    split_ifs <;> rfl
  rw [hfun]
  exact memLp_indicator_const 2 Metric.isOpen_ball.measurableSet.nullMeasurableSet 1
    (Or.inr (measure_ne_top _ _))

/-- Gibbs laws are absolutely continuous before normalization is proved. -/
lemma gibbsMeasure_absolutelyContinuous (P : Parameters) (N : ℕ+) :
    gibbsMeasure P N ≪ configurationVolume N :=
  (withDensity_absolutelyContinuous _ _).smul_left _

/-- Every fixed lift coordinate has null level sets under the configuration
volume. -/
lemma configurationVolume_coordinate_null (N : ℕ+) (i : Fin (N : ℕ)) (t : ℝ) :
    configurationVolume N {X | X.val i = t} = 0 := by
  rw [configurationVolume,
    (MeasurableEmbedding.subtype_coe (orderedDomain_measurable N)).comap_apply]
  have hnull : (volume : Measure (Fin (N : ℕ) → ℝ)) {x | x i = t} = 0 :=
    by
      rw [volume_pi]
      exact Measure.pi_eval_preimage_null (fun _ : Fin (N : ℕ) => (volume : Measure ℝ))
        (i := i) (s := {t}) (measure_singleton t)
  apply measure_mono_null _ hnull
  rintro x ⟨X, hX, rfl⟩
  exact hX

/-- A particle never hits the origin with positive Gibbs probability. This
justifies using the canonical analytic representative for the power-observable
law. See Corollary 2. -/
lemma gibbsMeasure_origin_null (P : Parameters) (N : ℕ+) (i : Fin (N : ℕ)) :
    gibbsMeasure P N {X | (X.val i : UnitAddCircle) = 0} = 0 := by
  apply gibbsMeasure_absolutelyContinuous P N
  have hnull : configurationVolume N (⋃ n : ℤ, {X | X.val i = (n : ℝ)}) = 0 :=
    measure_iUnion_null (fun n => configurationVolume_coordinate_null N i n)
  apply measure_mono_null _ hnull
  intro X hX
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff 1).mp hX
  apply Set.mem_iUnion.mpr
  exact ⟨n, by simpa using hn.symm⟩

end Riesz1

end
