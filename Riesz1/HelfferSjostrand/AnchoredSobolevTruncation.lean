/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.AnchoredSobolevLevelSets
public import Riesz1.ToMathlib.WeightedSobolev.TruncationGraph

/-!
# Truncations for the anchored law

Truncations on the anchored simplex:
truncation membership with the exact strict-sublevel gradient, and
convergence for the displayed sum-of-squares Sobolev norm.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- Anchored truncations belong to `H¹(μ*)` with gradient `1_{|F|<R} G`. -/
theorem IsAnchoredH1.clip (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {F : AnchoredEuclidean n → ℝ} {G : AnchoredEuclidean n → AnchoredEuclidean n}
    (hFG : IsAnchoredH1 χ F G) {R : ℝ} (hR : 0 ≤ R) :
    IsAnchoredH1 χ (fun x => WeightedSobolev.clipReal R (F x))
      ({x | |F x| < R}.indicator G) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact WeightedSobolev.Internal.graph_clip
    (P := WeightedSobolev.SmoothNearClosure (anchoredSimplex n)) (value := id) (grad := gradient)
    (fun φ hφ => (WeightedSobolev.memLp_of_smoothNearClosure
      (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex χ) hφ).1)
    (fun φ hφ => (WeightedSobolev.memLp_of_smoothNearClosure
      (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex χ) hφ).2)
    hFG.1 hFG.2.1 (fun _ hS hS0 _ hSb => hFG.comp_smooth χ hc hS hS0 hSb) hR
    (hFG.gradient_eq_zero_on_level χ hc (-R)) (hFG.gradient_eq_zero_on_level χ hc R)

/-- The anchored truncations converge in the specified squared Sobolev norm. -/
theorem IsAnchoredH1.tendsto_clip_error (χ : HsPairPotentials n.succPNat c)
    {F : AnchoredEuclidean n → ℝ} {G : AnchoredEuclidean n → AnchoredEuclidean n}
    (hFG : IsAnchoredH1 χ F G) :
    Tendsto (fun k : ℕ => ∫ x,
      (WeightedSobolev.clipReal k (F x) - F x) ^ 2 +
        ‖({y | |F y| < (k : ℝ)}.indicator G) x - G x‖ ^ 2 ∂anchoredMeasureE χ)
      atTop (𝓝 0) :=
  WeightedSobolev.tendsto_truncation_pair_error hFG.1 hFG.2.1

end Riesz1

end
