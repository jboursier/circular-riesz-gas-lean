/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SettingQuotient
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Admissible pair Hamiltonians and their normalization

Pair potentials are represented by functions on `ℝ` with regularity asserted
only on `(0, 1)`, as in Mathlib's `ContDiffOn` API. The Hamiltonian on the
chamber evaluates them only at separations in this interval. No exterior
value is supplied by a default branch.

This file addresses Assumption 3.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

namespace Riesz1

/-- Pair-potential data, with symmetry in the two labels. -/
structure HsPairPotentials (N : ℕ+) (c : ℝ) where
  potential : Fin (N : ℕ) → Fin (N : ℕ) → ℝ → ℝ
  symmetric : ∀ i j, potential i j = potential j i
  smooth : ∀ i j, i < j → ContDiffOn ℝ ∞ (potential i j) (Ioo 0 1)
  curvature : ∀ i j, i < j → ∀ r ∈ Ioo (0 : ℝ) 1,
    c ≤ deriv (deriv (potential i j)) r
  leftBoundary : ∀ i j, i < j → Tendsto (potential i j) (𝓝[>] 0) atTop
  rightBoundary : ∀ i j, i < j → Tendsto (potential i j) (𝓝[<] 1) atTop

/-- The pair sum as an ambient expression. Only its chamber restriction is used analytically. -/
def hsPairExpression {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    (x : HsEuclidean N) : ℝ :=
  2 * ∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.filter (i < ·), χ.potential i j (x j - x i)

/-- The pair Hamiltonian on the fundamental region. -/
def hsFundamentalHamiltonian {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    (X : Configuration N) : ℝ := hsPairExpression χ (WithLp.toLp 2 X.val)

/-- The pair Hamiltonian on the cyclic quotient. -/
def hsHamiltonian {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    (x : HsConfiguration N) : ℝ :=
  hsFundamentalHamiltonian χ ((hsConfigurationEquiv N).symm x)

/-- Admissibility with the paper's constants `c` and `C_N`, with no uniformity in `N`. -/
def HsAdmissible {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (C_N : ℝ) : Prop :=
  ∃ hN : 2 ≤ (N : ℕ), 0 < c ∧ 0 ≤ C_N ∧ ∀ x ∈ hsChamber N,
    ‖gradient (hsPairExpression χ) x‖ ^ 2 / (4 * (N : ℝ)) -
      Laplacian.laplacian (hsPairExpression χ) x / 2 ≥
        (hsBoundaryDistance N hN x)⁻¹ ^ 2 - C_N

theorem hsPairExpression_translate {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    (t : ℝ) (x : HsEuclidean N) :
    hsPairExpression χ (hsTranslate t x) = hsPairExpression χ x := by
  unfold hsPairExpression
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [hsTranslate_apply]
  ring

theorem hsChamber_separation_mem {N : ℕ+} {x : HsEuclidean N}
    (hx : x ∈ hsChamber N) {i j : Fin (N : ℕ)} (hij : i < j) :
    x j - x i ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨sub_pos.mpr (hx.1 hij), ?_⟩
  have hlo : x ⟨0, N.pos⟩ ≤ x i := hx.1.monotone (Fin.mk_le_mk.mpr (Nat.zero_le _))
  linarith [hx.2 j]

/-- All the derivatives used in the admissibility predicate are interior derivatives. -/
theorem hsPairExpression_contDiffOn {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) :
    ContDiffOn ℝ ∞ (hsPairExpression χ) (hsChamber N) := by
  unfold hsPairExpression
  apply ContDiffOn.mul contDiffOn_const
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j hj
  have hij := (Finset.mem_filter.mp hj).2
  apply (χ.smooth i j hij).comp
    (((EuclideanSpace.proj j).contDiff.sub (EuclideanSpace.proj i).contDiff).contDiffOn)
  exact fun x hx => hsChamber_separation_mem hx hij

theorem hsHamiltonian_configurationMap {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    (X : Configuration N) :
    hsHamiltonian χ (hsConfigurationMap N X) = hsFundamentalHamiltonian χ X := by
  change hsFundamentalHamiltonian χ ((hsConfigurationEquiv N).symm
    ((hsConfigurationEquiv N) X)) = _
  rw [Equiv.symm_apply_apply]

/-- Every separation evaluated in the pair Hamiltonian belongs to `(0, 1)`. -/
theorem hsPair_separation_mem {N : ℕ+} (X : Configuration N)
    {i j : Fin (N : ℕ)} (hij : i < j) : X.val j - X.val i ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨sub_pos.mpr (X.property.1 hij), ?_⟩
  have hlo : X.val ⟨0, N.pos⟩ ≤ X.val i :=
    X.property.1.monotone (Fin.mk_le_mk.mpr (Nat.zero_le _))
  linarith [X.property.2.2.2 j]

theorem continuous_hsFundamentalHamiltonian {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) : Continuous (hsFundamentalHamiltonian χ) := by
  unfold hsFundamentalHamiltonian hsPairExpression
  apply continuous_const.mul
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j hj
  have hij : i < j := (Finset.mem_filter.mp hj).2
  apply (χ.smooth i j hij).continuousOn.comp_continuous
  · exact ((continuous_apply j).comp continuous_subtype_val).sub
      ((continuous_apply i).comp continuous_subtype_val)
  · exact fun X => hsPair_separation_mem X hij

theorem measurable_hsHamiltonian {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) :
    Measurable (hsHamiltonian χ) :=
  (continuous_hsFundamentalHamiltonian χ).measurable.comp
    (measurable_hsConfigurationEquiv_symm N)

/-- Internal convex-analysis estimate used to obtain normalization, without adding a bound
to the admissibility assumptions. -/
theorem hs_internal_convex_lower_bound {φ : ℝ → ℝ}
    (hc : ConvexOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : DifferentiableAt ℝ φ (1 / 2)) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    φ (1 / 2) - |deriv φ (1 / 2)| ≤ φ r := by
  have hm : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hs : φ (1 / 2) + deriv φ (1 / 2) * (r - 1 / 2) ≤ φ r := by
    rcases lt_trichotomy r (1 / 2) with h | h | h
    · have hh := hc.slope_le_deriv hr hm h hd
      rw [slope_def_field] at hh
      have hh' := (div_le_iff₀ (sub_pos.mpr h)).mp hh
      nlinarith
    · subst r
      simp
    · have hh := hc.deriv_le_slope hm hr h hd
      rw [slope_def_field] at hh
      have hh' := (le_div_iff₀ (sub_pos.mpr h)).mp hh
      nlinarith
  have ha : |r - 1 / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  have hb : |deriv φ (1 / 2) * (r - 1 / 2)| ≤ |deriv φ (1 / 2)| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left ha (abs_nonneg _)).trans_eq (mul_one _)
  linarith [neg_abs_le (deriv φ (1 / 2) * (r - 1 / 2))]

theorem HsPairPotentials.convex {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    (hc : 0 < c) (i j : Fin (N : ℕ)) (hij : i < j) :
    ConvexOn ℝ (Ioo (0 : ℝ) 1) (χ.potential i j) := by
  have h := χ.smooth i j hij
  apply convexOn_of_deriv2_nonneg' (convex_Ioo _ _)
    (h.differentiableOn (by norm_num))
    ((h.deriv_of_isOpen (m := 1) isOpen_Ioo (by simp)).differentiableOn
      (by norm_num))
  intro r hr
  exact hc.le.trans (χ.curvature i j hij r hr)

theorem hsFundamentalHamiltonian_bounded_below {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c) :
    ∃ B : ℝ, ∀ X : Configuration N, B ≤ hsFundamentalHamiltonian χ X := by
  let b (i j : Fin (N : ℕ)) :=
    χ.potential i j (1 / 2) - |deriv (χ.potential i j) (1 / 2)|
  refine ⟨2 * ∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.filter (i < ·), b i j, fun X => ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j hj
  have hij := (Finset.mem_filter.mp hj).2
  apply hs_internal_convex_lower_bound (χ.convex hc i j hij)
    (((χ.smooth i j hij).differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds (by norm_num : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1)))
    (hsPair_separation_mem X hij)

/-- The unnormalized Gibbs weight on the fundamental region. -/
def hsFundamentalWeight {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) :
    Measure (Configuration N) :=
  (configurationVolume N).withDensity (fun X => ENNReal.ofReal
    (Real.exp (-hsFundamentalHamiltonian χ X)))

/-- Its extended-real partition function, before establishing finiteness. -/
def hsPartitionFunction {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) : ℝ≥0∞ :=
  hsFundamentalWeight χ univ

theorem hsPartitionFunction_eq_lintegral {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) :
    hsPartitionFunction χ = ∫⁻ X, ENNReal.ofReal
      (Real.exp (-hsFundamentalHamiltonian χ X)) ∂configurationVolume N := by
  unfold hsPartitionFunction hsFundamentalWeight
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- Positivity does not require the boundary-growth inequality. -/
theorem hsPartitionFunction_pos {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) :
    0 < hsPartitionFunction χ := by
  have hm : Measurable (fun X => ENNReal.ofReal (Real.exp (-hsFundamentalHamiltonian χ X))) :=
    (ENNReal.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_hsFundamentalHamiltonian χ).neg)).measurable
  rw [hsPartitionFunction_eq_lintegral, lintegral_pos_iff_support hm]
  have hsupp : Function.support (fun X : Configuration N => ENNReal.ofReal
      (Real.exp (-hsFundamentalHamiltonian χ X))) = univ :=
    Set.eq_univ_of_forall fun X => by simp [Function.mem_support, Real.exp_pos]
  rw [hsupp, configurationVolume_univ]
  exact ENNReal.ofReal_pos.mpr (one_div_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos _)))

/-- Finiteness follows from pair convexity, without a closure regularity assumption. -/
theorem hsPartitionFunction_lt_top {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    (hc : 0 < c) : hsPartitionFunction χ < ⊤ := by
  obtain ⟨B, hB⟩ := hsFundamentalHamiltonian_bounded_below χ hc
  rw [hsPartitionFunction_eq_lintegral]
  calc (∫⁻ X, ENNReal.ofReal (Real.exp (-hsFundamentalHamiltonian χ X))
        ∂configurationVolume N) ≤ ∫⁻ _X : Configuration N,
        ENNReal.ofReal (Real.exp (-B)) ∂configurationVolume N :=
      lintegral_mono fun X => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg (hB X)))
    _ < ⊤ := by
      rw [lintegral_const, configurationVolume_univ]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- The Gibbs probability as a bundled probability, defined for every positively convex
pair-potential family. In particular it is available for every admissible Hamiltonian. -/
def hsGibbsProbability {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c) :
    ProbabilityMeasure (Configuration N) :=
  ⟨(hsPartitionFunction χ)⁻¹ • hsFundamentalWeight χ, by
    rw [isProbabilityMeasure_iff, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (hsPartitionFunction_pos χ).ne'
      (hsPartitionFunction_lt_top χ hc).ne⟩

end Riesz1

end
