/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.AnchoredCalculus
public import Riesz1.ToMathlib.WeightedSobolev.BoundedDomainComposition

/-!
# The anchored scalar chain rule

The `C¹` chain rule on the
bounded Euclidean simplex with its anchored Gibbs probability.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ContDiff NNReal

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- Smooth scalar composition in the anchored Sobolev completion. -/
theorem IsAnchoredH1.comp_smooth (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {F : AnchoredEuclidean n → ℝ} {G : AnchoredEuclidean n → AnchoredEuclidean n}
    (hFG : IsAnchoredH1 χ F G) {T : ℝ → ℝ} (hT : ContDiff ℝ ∞ T)
    (h0 : T 0 = 0) {C : ℝ≥0} (hb : ∀ r, ‖deriv T r‖₊ ≤ C) :
    IsAnchoredH1 χ (fun x => T (F x)) (fun x => deriv T (F x) • G x) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact WeightedSobolev.IsWeightedH1.comp_smooth (isBounded_anchoredSimplex n)
    (ae_mem_anchoredSimplex χ) hFG hT h0 hb

/-- The bounded-derivative `C¹` chain rule for `H¹(μ*)`. -/
theorem IsAnchoredH1.comp_C1 (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {F : AnchoredEuclidean n → ℝ} {G : AnchoredEuclidean n → AnchoredEuclidean n}
    (hFG : IsAnchoredH1 χ F G) {T : ℝ → ℝ} (hT : ContDiff ℝ 1 T)
    (h0 : T 0 = 0) {C : ℝ≥0} (hb : ∀ r, ‖deriv T r‖₊ ≤ C) :
    IsAnchoredH1 χ (fun x => T (F x)) (fun x => deriv T (F x) • G x) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact WeightedSobolev.IsWeightedH1.comp_C1 (isBounded_anchoredSimplex n)
    (ae_mem_anchoredSimplex χ) hFG hT h0 hb

end Riesz1

end
