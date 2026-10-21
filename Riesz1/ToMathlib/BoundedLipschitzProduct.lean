/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Products of bounded Lipschitz real functions

An explicit Lipschitz constant for a product on any pseudometric domain.
-/

@[expose] public section

open scoped NNReal

namespace Riesz1

/-- Bounded Lipschitz real factors have a Lipschitz product. -/
theorem lipschitzWith_mul_of_bounds {E : Type*} [PseudoMetricSpace E]
    {b q : E → ℝ} {B Q M L : ℝ≥0} (hb : LipschitzWith B b) (hq : LipschitzWith Q q)
    (hm : ∀ x, ‖b x‖ ≤ M) (hl : ∀ x, ‖q x‖ ≤ L) :
    LipschitzWith (M * Q + B * L) (fun x => b x * q x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖b x * q x - b y * q y‖ ≤ ((M * Q + B * L : ℝ≥0) : ℝ) * dist x y
  have hbxy : ‖b x - b y‖ ≤ (B : ℝ) * dist x y := by
    simpa only [dist_eq_norm] using hb.dist_le_mul x y
  have hqxy : ‖q x - q y‖ ≤ (Q : ℝ) * dist x y := by
    simpa only [dist_eq_norm] using hq.dist_le_mul x y
  calc
    ‖b x * q x - b y * q y‖ =
        ‖b x * (q x - q y) + (b x - b y) * q y‖ := by congr 1; ring
    _ ≤ ‖b x * (q x - q y)‖ + ‖(b x - b y) * q y‖ := norm_add_le _ _
    _ = ‖b x‖ * ‖q x - q y‖ + ‖b x - b y‖ * ‖q y‖ := by rw [norm_mul, norm_mul]
    _ ≤ (M : ℝ) * ((Q : ℝ) * dist x y) + ((B : ℝ) * dist x y) * (L : ℝ) := by
      exact add_le_add
        (mul_le_mul (hm x) hqxy (norm_nonneg _) M.2)
        (mul_le_mul hbxy (hl y) (norm_nonneg _) (mul_nonneg B.2 dist_nonneg))
    _ = _ := by push_cast; ring

end Riesz1
