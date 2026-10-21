/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Externals.BakryEmeryEntropy
public import Riesz1.ToMathlib.SquareEntropyRegularization

/-!
# Proof of the smooth Bakry–Émery criterion

This proves `Riesz1.External.BakryEmery`, the Bakry–Émery criterion, with no external
hypotheses. The reference for the statement is Bakry–Émery, *Diffusions
hypercontractives* (1985), Proposition 3 (4b), Proposition 4, and Corollary 2 (23).
The proof here uses the Prékopa–Leindler argument of Bobkov–Ledoux, *From Brunn–Minkowski
to Brascamp–Lieb and to logarithmic Sobolev inequalities* (2000), Proposition 3.1:
https://www.math.univ-toulouse.fr/~ledoux/BrunnMinkowski.pdf .

The weighted comparison is differentiated at weight one, compact cutoffs remove the
auxiliary Hessian bound, and `log(q² + ε)` gives the square-test statement including
zeros. Normalization, probability, and all integrability conclusions are supplied by the
previously proved normalization module. No external code is copied in this module.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1.Externals

/-- The smooth Bakry–Émery criterion, proved without external hypotheses. -/
theorem bakry_emery_proof : Riesz1.External.BakryEmery := by
  unfold Riesz1.External.BakryEmery
  intro d hd w hw V hV hH
  refine ⟨bakry_emery_density_integrable hw hV hH,
    bakry_emery_normalization_pos hw hV hH, bakry_emery_isProbabilityMeasure hw hV hH, ?_⟩
  let ν : Measure (EuclideanSpace ℝ (Fin d)) := volume.withDensity (fun x =>
    ENNReal.ofReal (Real.exp (-V x) / ∫ y, Real.exp (-V y)))
  let : IsProbabilityMeasure ν := bakry_emery_isProbabilityMeasure hw hV hH
  intro q hq hqb hgb
  obtain ⟨hi₁, hi₂, hi₃⟩ := bakry_emery_test_integrable (μ := ν) hq hqb hgb
  refine ⟨hi₁, hi₂, hi₃, ?_⟩
  have hnorm (f : EuclideanSpace ℝ (Fin d) → ℝ) (x) :
      ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by simp only [gradient, LinearIsometryEquiv.norm_map]
  obtain ⟨K, hK⟩ := hqb.exists_norm_le
  obtain ⟨D, hD⟩ := hgb.exists_norm_le
  have hExp : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ g →
      (∃ K, ∀ x, |g x| ≤ K) → (∃ D, ∀ x, ‖fderiv ℝ g x‖ ≤ D) →
      (∫ x, g x * Real.exp (g x) ∂ν) -
        (∫ x, Real.exp (g x) ∂ν) * Real.log (∫ x, Real.exp (g x) ∂ν) ≤
          w / 2 * ∫ x, Real.exp (g x) * ‖fderiv ℝ g x‖ ^ 2 ∂ν := by
    intro g hg ⟨C, hC⟩ ⟨B, hB⟩
    have hbg : Bornology.IsBounded (range g) := isBounded_iff_forall_norm_le.mpr
      ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
    have hbG : Bornology.IsBounded (range (gradient g)) := isBounded_iff_forall_norm_le.mpr
      ⟨B, by rintro _ ⟨x, rfl⟩; rw [hnorm]; exact hB x⟩
    simpa only [hnorm] using bakry_emery_exponential_entropy hd hw hV hH hg hbg hbG
  have hi := square_entropy_of_exponential (μ := ν) (w / 2) (by positivity) hExp hq
    (fun x => hK _ (mem_range_self x))
    (fun x => by rw [← hnorm]; exact hD _ (mem_range_self x))
  have he : 4 * (w / 2) = 2 * w := by ring
  simpa only [he, hnorm] using hi

end Riesz1.Externals

end
