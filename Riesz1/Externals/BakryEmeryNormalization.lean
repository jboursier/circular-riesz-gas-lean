/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.External.BakryEmery
public import Riesz1.ToMathlib.StrongConvexTangent
public import Riesz1.ToMathlib.Gaussian.AffineDensity
public import Riesz1.HelfferSjostrand.LogSobolevTransfer

/-!
# Normalization and test integrability for Bakry–Émery

This proves the normalization and integrability assertions of the Bakry–Émery criterion `External.BakryEmery`
directly from the Hessian bound, without invoking that external statement. It does not prove
the entropy inequality. The quadratic tangent bound gives a Gaussian majorant. Bounded
smooth tests then have integrable squares, entropy integrands, and gradient energies.

No code from an external development is used.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace Riesz1.Externals

variable {d : ℕ} {w : ℝ} {V : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The global Gaussian lower bound, with the value and gradient at the origin retained. -/
theorem bakry_emery_quadratic_lower (hV : ContDiff ℝ ∞ V)
    (hH : ∀ x h, w⁻¹ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x h) h)
    (x : EuclideanSpace ℝ (Fin d)) :
    (2 * w)⁻¹ * ‖x‖ ^ 2 + ⟪gradient V 0, x⟫_ℝ + V 0 ≤ V x := by
  have hi := quadratic_tangent_le_of_hessian_lower convex_univ isOpen_univ
    (hV.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffOn
    (fun y _ h => hH y h) (mem_univ (0 : EuclideanSpace ℝ (Fin d))) (mem_univ x)
  simp only [sub_zero, ← inner_gradient_left] at hi
  convert hi using 1
  ring

/-- Uniform convexity gives integrability of the unnormalized whole-space density. -/
theorem bakry_emery_density_integrable (hw : 0 < w) (hV : ContDiff ℝ ∞ V)
    (hH : ∀ x h, w⁻¹ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x h) h) :
    Integrable (fun x => Real.exp (-V x)) volume := by
  refine (Gaussian.integrable_exp_quadratic_affine hw (gradient V 0) (V 0)).mono'
    (Real.continuous_exp.comp hV.continuous.neg).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (neg_le_neg (bakry_emery_quadratic_lower hV hH x))

/-- The whole-space normalizing integral is strictly positive. -/
theorem bakry_emery_normalization_pos (hw : 0 < w) (hV : ContDiff ℝ ∞ V)
    (hH : ∀ x h, w⁻¹ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x h) h) :
    0 < ∫ x, Real.exp (-V x) :=
  integral_exp_pos (bakry_emery_density_integrable hw hV hH)

/-- The measure used literally in the statement is a probability. -/
theorem bakry_emery_isProbabilityMeasure (hw : 0 < w) (hV : ContDiff ℝ ∞ V)
    (hH : ∀ x h, w⁻¹ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x h) h) :
    IsProbabilityMeasure (volume.withDensity (fun x =>
      ENNReal.ofReal (Real.exp (-V x) / ∫ y, Real.exp (-V y)))) :=
  Gaussian.isProbabilityMeasure_normalized_density
    (bakry_emery_density_integrable hw hV hH) (fun _ => (Real.exp_pos _).le)
    (bakry_emery_normalization_pos hw hV hH)

/-- All test integrability obligations in the statement, for any finite measure. -/
theorem bakry_emery_test_integrable {μ : Measure (EuclideanSpace ℝ (Fin d))}
    [IsFiniteMeasure μ] {q : EuclideanSpace ℝ (Fin d) → ℝ}
    (hq : ContDiff ℝ ∞ q) (hqb : Bornology.IsBounded (range q))
    (hgb : Bornology.IsBounded (range (gradient q))) :
    Integrable (fun x => q x ^ 2) μ ∧
      Integrable (fun x => Real.negMulLog (q x ^ 2)) μ ∧
      Integrable (fun x => ‖gradient q x‖ ^ 2) μ := by
  obtain ⟨C, hC⟩ := hqb.exists_norm_le
  obtain ⟨D, hD⟩ := hgb.exists_norm_le
  have hn (x : EuclideanSpace ℝ (Fin d)) : ‖gradient q x‖ = ‖fderiv ℝ q x‖ :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.norm_map _
  have hi := LogSobolevInternal.test_integrable (μ := μ)
    (hq.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
    (fun x => (Real.norm_eq_abs _ ▸ hC _ (mem_range_self x)))
    (fun x => (hn x ▸ hD _ (mem_range_self x)))
  simpa only [hn] using hi

/-- The normalization and test-integrability conclusions of the Bakry–Émery criterion `External.BakryEmery`.
The entropy–energy inequality remains a separate obligation. -/
theorem bakry_emery_normalization (hw : 0 < w) (hV : ContDiff ℝ ∞ V)
    (hH : ∀ x h, w⁻¹ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x h) h) :
    ∃ (_ : Integrable (fun x => Real.exp (-V x)) volume),
      0 < (∫ x, Real.exp (-V x)) ∧
      let ν : Measure (EuclideanSpace ℝ (Fin d)) :=
        volume.withDensity (fun x =>
          ENNReal.ofReal (Real.exp (-V x) / ∫ y, Real.exp (-V y)))
      IsProbabilityMeasure ν ∧
        ∀ q : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ q →
          Bornology.IsBounded (range q) → Bornology.IsBounded (range (gradient q)) →
          Integrable (fun x => q x ^ 2) ν ∧
            Integrable (fun x => Real.negMulLog (q x ^ 2)) ν ∧
            Integrable (fun x => ‖gradient q x‖ ^ 2) ν := by
  refine ⟨bakry_emery_density_integrable hw hV hH,
    bakry_emery_normalization_pos hw hV hH, bakry_emery_isProbabilityMeasure hw hV hH, ?_⟩
  let := bakry_emery_isProbabilityMeasure hw hV hH
  exact fun _ hq hqb hgb => bakry_emery_test_integrable hq hqb hgb

end Riesz1.Externals

end
