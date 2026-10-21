/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopIBPVariance
public import Riesz1.Variance.LoopIBPMoments

/-!
# Square integrability of the loop functional under the Gibbs law

Proposition 5.9, the square-integrability step of the variance clause. For a
Lipschitz one-periodic profile `f`, the loop functional is bounded by a constant times
`1 + ∑ₖ gapₖ^{-s}` on every configuration. The squared shifted power sum is in `L²` under the
Gibbs law (`memLp_sq_one_add_gapPowerSum`), so the loop functional is in `L²` too.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- **Square integrability.** For a Lipschitz one-periodic profile `f` and a Riesz exponent
`0 < s < 1`, the loop functional `X ↦ Loop_1[f](X)` lies in `L²` of the Gibbs law. -/
theorem memLp_loopFunctional_gibbs (P : Parameters) (hPL : External.PrekopaLeindler) (N : ℕ+)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) :
    MemLp (fun X : Configuration N => loopFunctional s (N : ℕ) f X.val) 2 (gibbsMeasure P N) := by
  have : IsFiniteMeasure (gibbsMeasure P N) := by
    have := (modelWellDefined P N).2.2
    infer_instance
  obtain ⟨C, hC0, hC⟩ := exists_loopFunctional_le ⟨s, hs0, hs1⟩ N hf hp
  -- The bound `C (1 + G) ≤ C (1 + G)²` holds because `1 + G ≥ 1` for the nonnegative power sum `G`.
  have hbound : MemLp (fun X : Configuration N => C * (1 + gapPowerSum s X) ^ 2) 2
      (gibbsMeasure P N) :=
    (memLp_sq_one_add_gapPowerSum P hPL N hs0).const_mul C
  refine MemLp.of_le hbound ?_ (Filter.Eventually.of_forall fun X => ?_)
  · exact ((measurable_loopFunctional ⟨s, hs0, hs1⟩ (N : ℕ) hf.continuous).comp
      measurable_subtype_coe).aestronglyMeasurable
  · have hG : 0 ≤ gapPowerSum s X := gapPowerSum_nonneg s X
    calc ‖loopFunctional s (N : ℕ) f X.val‖
        = |loopFunctional s (N : ℕ) f X.val| := Real.norm_eq_abs _
      _ ≤ C * (1 + gapPowerSum s X) := hC X
      _ ≤ C * (1 + gapPowerSum s X) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith) hC0
      _ = ‖C * (1 + gapPowerSum s X) ^ 2‖ :=
          (Real.norm_of_nonneg (mul_nonneg hC0 (sq_nonneg _))).symm

/-- The loop functional of a Lipschitz one-periodic profile is integrable under the Gibbs law. -/
theorem integrable_loopFunctional_gibbs (P : Parameters) (hPL : External.PrekopaLeindler)
    (N : ℕ+) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) :
    Integrable (fun X : Configuration N => loopFunctional s (N : ℕ) f X.val)
      (gibbsMeasure P N) := by
  have : IsFiniteMeasure (gibbsMeasure P N) := by
    have := (modelWellDefined P N).2.2
    infer_instance
  exact (memLp_loopFunctional_gibbs P hPL N hs0 hs1 hf hp).integrable one_le_two

end Riesz1

end
