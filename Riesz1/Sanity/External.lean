/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.External.Pinsker
public import Riesz1.Frozen.External.PrekopaLeindler
public import Riesz1.Frozen.External.BakryEmery
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Tactic

/-!
# Sanity checks for the external statements

Pinsker at equal probability measures, a nonzero convex-ball indicator for
midpoint Prékopa–Leindler, and the Gaussian potential and constant tests for
Bakry–Émery. None of these checks assumes an external statement.
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Riesz1.ExternalSanity

/-- The full Pinsker conclusion is true at every equal pair of probabilities. -/
lemma pinsker_self {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    (etvDist μ μ / 2) ^ 2 ≤ 2 * InformationTheory.klDiv μ μ := by
  simp

/-- An explicit probability supplies both Pinsker hypotheses. -/
lemma pinsker_dirac_hypotheses :
    IsProbabilityMeasure (Measure.dirac (0 : ℝ)) ∧
      (etvDist (Measure.dirac (0 : ℝ)) (Measure.dirac 0) / 2) ^ 2 ≤
        2 * InformationTheory.klDiv (Measure.dirac (0 : ℝ)) (Measure.dirac 0) :=
  ⟨inferInstance, pinsker_self _⟩

/-- Disjoint point masses have distance one, rather than full variation two. -/
lemma pinsker_disjoint_dirac_distance :
    etvDist (Measure.dirac (0 : ℝ)) (Measure.dirac 1) / 2 = 1 := by
  have hs : Measure.dirac (0 : ℝ) ⟂ₘ Measure.dirac 1 :=
    ⟨{1}, measurableSet_singleton 1, by simp, by simp⟩
  rw [etvDist_of_mutuallySingular hs]
  norm_num
  exact ENNReal.div_self (by norm_num) (by norm_num)

/-- The unit-ball indicator is a nonzero test satisfying every PL function hypothesis. -/
lemma prekopa_ball_hypotheses (d : ℕ) :
    let f := (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).indicator
      (fun _ => (1 : ℝ))
    Measurable f ∧ (∀ x, 0 ≤ f x) ∧ Bornology.IsBounded (Set.range f) ∧
      Bornology.IsBounded (Function.support f) ∧ f 0 = 1 ∧
      ∀ x y, Real.sqrt (f x * f y) ≤ f ((1 / 2 : ℝ) • (x + y)) := by
  classical
  dsimp only
  refine ⟨measurable_const.indicator measurableSet_closedBall,
    fun _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _, ?_,
    Metric.isBounded_closedBall.subset Set.support_indicator_subset, ?_, ?_⟩
  · refine (Set.toFinite {0, (1 : ℝ)}).isBounded.subset ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 <;> simp [hx]
  · simp
  · intro x y
    by_cases hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
    · by_cases hy : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
      · have hm := (convex_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).midpoint_mem hx hy
        rw [midpoint_eq_smul_add] at hm
        simp only [invOf_eq_inv, smul_add] at hm
        simp [hx, hy, hm]
      · simp [hy, Set.indicator_nonneg (fun _ _ => zero_le_one)]
    · simp [hx, Set.indicator_nonneg (fun _ _ => zero_le_one)]

/-- The actual PL conclusion, including all three integrability certificates, for that test. -/
lemma prekopa_ball_conclusion (d : ℕ) :
    let f := (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).indicator
      (fun _ => (1 : ℝ))
    ∃ (_ : Integrable f volume) (_ : Integrable f volume) (_ : Integrable f volume),
      Real.sqrt ((∫ x, f x) * ∫ x, f x) ≤ ∫ x, f x := by
  classical
  dsimp only
  have hi : Integrable ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).indicator
      (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne)
  refine ⟨hi, hi, hi, ?_⟩
  rw [Real.sqrt_mul_self (integral_nonneg (fun _ =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) _))]

/-- First derivative of the Gaussian potential, a check on the Hessian convention. -/
lemma gaussian_potential_fderiv (d : ℕ) :
    fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2 / 2) = ⇑(innerSL ℝ) := by
  funext x
  have he : (2 : ℝ)⁻¹ • (2 • innerSL ℝ x) = innerSL ℝ x := by
    ext y
    simp
  simpa only [he, Pi.smul_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_smul (2 : ℝ)⁻¹).fderiv

/-- At w = 1 the Gaussian potential satisfies the exact smoothness and curvature premises. -/
lemma bakry_gaussian_hypotheses (d : ℕ) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2 / 2) ∧
      ∀ x h : EuclideanSpace ℝ (Fin d),
        (1 : ℝ)⁻¹ * ‖h‖ ^ 2 ≤
          (fderiv ℝ (fderiv ℝ (fun y => ‖y‖ ^ 2 / 2)) x h) h := by
  refine ⟨(contDiff_norm_sq ℝ).div_const 2, ?_⟩
  intro x h
  rw [gaussian_potential_fderiv, ContinuousLinearMap.fderiv]
  simp only [inv_one, one_mul]
  exact (real_inner_self_eq_norm_sq h).ge

/-- Gaussian normalization is an integrable, strictly positive real integral. -/
lemma bakry_gaussian_normalization (d : ℕ) :
    ∃ (_ : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
        Real.exp (-(‖x‖ ^ 2 / 2))) volume),
      0 < ∫ x : EuclideanSpace ℝ (Fin d), Real.exp (-(‖x‖ ^ 2 / 2)) := by
  have hi : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp (-(‖x‖ ^ 2 / 2))) volume := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
      (by norm_num : (0 : ℝ) < (1 / 2 : ℂ).re) (0 : ℂ)
      (0 : EuclideanSpace ℝ (Fin d))).re
    convert h using 1
    ext x
    change Real.exp (-(‖x‖ ^ 2 / 2)) =
      (Complex.exp (-(1 / 2 : ℂ) * (‖x‖ : ℂ) ^ 2 + 0 * ↑(inner ℝ 0 x))).re
    rw [show -(1 / 2 : ℂ) * (‖x‖ : ℂ) ^ 2 + 0 * ↑(inner ℝ 0 x) =
      ((-(‖x‖ ^ 2 / 2) : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.exp_ofReal_re _).symm
  exact ⟨hi, integral_exp_pos hi⟩

/-- Internal normalization bridge, requiring only integrability and positive mass. -/
lemma normalizedDensity_probability {d : ℕ} {V : EuclideanSpace ℝ (Fin d) → ℝ}
    (hi : Integrable (fun x => Real.exp (-V x)) volume)
    (hp : 0 < ∫ x, Real.exp (-V x)) :
    IsProbabilityMeasure (volume.withDensity (fun x =>
      ENNReal.ofReal (Real.exp (-V x) / ∫ y, Real.exp (-V y)))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _) (ae_of_all _ (fun _ =>
      div_nonneg (Real.exp_pos _).le hp.le)), integral_div, div_self hp.ne']
  simp

/-- The very same density used in the external is a probability for the Gaussian potential. -/
lemma bakry_gaussian_probability (d : ℕ) :
    IsProbabilityMeasure (volume.withDensity (fun x : EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2 / 2)) /
        ∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-(‖y‖ ^ 2 / 2))))) := by
  obtain ⟨hi, hp⟩ := bakry_gaussian_normalization d
  exact normalizedDensity_probability hi hp

/-- Every constant test, including zero, satisfies all the smooth bounded test premises. -/
lemma bakry_constant_hypotheses (d : ℕ) (c : ℝ) :
    ContDiff ℝ ∞ (fun _ : EuclideanSpace ℝ (Fin d) => c) ∧
      Bornology.IsBounded (Set.range (fun _ : EuclideanSpace ℝ (Fin d) => c)) ∧
      Bornology.IsBounded (Set.range (gradient (fun _ : EuclideanSpace ℝ (Fin d) => c))) := by
  refine ⟨contDiff_const, ?_, ?_⟩ <;>
    simp only [gradient_fun_const', Set.range_const] <;> exact Bornology.isBounded_singleton

/-- Constants have zero homogeneous entropy and energy under every probability. -/
lemma bakry_constant_conclusion (d : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure ν] (w c : ℝ) :
    ∃ (_ : Integrable (fun _ => c ^ 2) ν)
      (_ : Integrable (fun _ => Real.negMulLog (c ^ 2)) ν)
      (_ : Integrable (fun x => ‖gradient (fun _ => c) x‖ ^ 2) ν),
      -(∫ x, Real.negMulLog ((fun _ => c) x ^ 2) ∂ν) +
          Real.negMulLog (∫ x, (fun _ => c) x ^ 2 ∂ν) ≤
        2 * w * ∫ x, ‖gradient (fun _ => c) x‖ ^ 2 ∂ν := by
  refine ⟨integrable_const _, integrable_const _, ?_, ?_⟩
  · simp [gradient_fun_const]
  · simp [gradient_fun_const]

end Riesz1.ExternalSanity

end
end
