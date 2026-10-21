/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.AnchoredSobolevLevelSets
public import Riesz1.ToMathlib.WeightedSobolev.PiecewiseComposition

/-!
# Finitely piecewise C¹ composition for the anchored law

The piecewise `C¹` clause applies
to the anchored Sobolev completion with its Euclidean gradient.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff NNReal

namespace Riesz1

/-- The finitely piecewise `C¹` Lipschitz chain rule for the anchored law. -/
theorem IsAnchoredH1.comp_piecewise {n : ℕ} {c : ℝ}
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {F : AnchoredEuclidean n → ℝ} {G : AnchoredEuclidean n → AnchoredEuclidean n}
    (hFG : IsAnchoredH1 χ F G) {T : ℝ → ℝ} {C : ℝ≥0}
    (hT : LipschitzWith C T) (h0 : T 0 = 0) {B : Set ℝ} (hB : B.Finite)
    (hTC : ContDiffOn ℝ 1 T Bᶜ) :
    IsAnchoredH1 χ (fun x => T (F x)) (fun x => deriv T (F x) • G x) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact WeightedSobolev.Internal.graph_comp_piecewise
    (P := WeightedSobolev.SmoothNearClosure (anchoredSimplex n)) (value := id) (grad := gradient)
    (fun φ hφ => (WeightedSobolev.memLp_of_smoothNearClosure
      (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex χ) hφ).1)
    (fun φ hφ => (WeightedSobolev.memLp_of_smoothNearClosure
      (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex χ) hφ).2)
    hFG.1 hFG.2.1 (fun _ hS hS0 _ hSb => hFG.comp_smooth χ hc hS hS0 hSb) hT h0 hB hTC
    (fun a _ => hFG.gradient_eq_zero_on_level χ hc a)

end Riesz1

end
