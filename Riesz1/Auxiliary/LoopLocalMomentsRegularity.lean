/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalMomentsBackground

/-!
# Measurability and integral certificates for the local loop

All particle/background integrals converge on the entire
preceding-particle carrier. The loop is measurable there, without a good-event cutoff.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

theorem loopLocalLoop_background_integrable {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (N : ℕ+) (ℓ γ : ℝ) {b : ℝ → ℝ} (hb : ContDiff ℝ 1 b)
    (hp : Function.Periodic b (N : ℝ)) (X : LoopPrecedingConfiguration N) (i : ℤ) :
    IntervalIntegrable (fun u => loopArcKernel s N b (loopPrecedingLift X i) u)
      volume (loopLocalLo N ℓ γ) (loopLocalHi N ℓ γ) :=
  loopLocalKernel_intervalIntegrable hs hs1 N hb hp _ _ _

/-- Measurability in the particle position of a background integral on any ordered interval. -/
theorem measurable_loopLocalKernel_integral {b : ℝ → ℝ} (hb : Continuous b)
    (s : ℝ) (N : ℕ+) {a c : ℝ} (hac : a ≤ c) :
    Measurable (fun z => ∫ u in a..c, loopArcKernel s N b z u) := by
  simp_rw [intervalIntegral.integral_of_le hac]
  exact ((measurable_loopLocalKernel hb s N).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc a c))).measurable

theorem measurable_loopLocalLoop {b : ℝ → ℝ} (hb : Continuous b) (s : ℝ)
    (N : ℕ+) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (γ : ℝ) :
    Measurable (loopLocalLoop s N ℓ γ b) := by
  have hi := measurable_loopLocalKernel_integral hb s N (loopLocalLo_le_hi N hℓ (γ := γ))
  have hsum : Measurable (fun X : LoopPrecedingConfiguration N =>
      ∑ i ∈ gradLabels N ℓ γ, ∑ j ∈ (gradLabels N ℓ γ).erase i,
        loopArcKernel s N b (loopPrecedingLift X i) (loopPrecedingLift X j)) := by
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    exact (measurable_loopLocalKernel hb s N).comp
      ((measurable_loopPrecedingLift N i).prodMk (measurable_loopPrecedingLift N j))
  have hbg : Measurable (fun X : LoopPrecedingConfiguration N =>
      ∑ i ∈ gradLabels N ℓ γ, ∫ u in loopLocalLo N ℓ γ..loopLocalHi N ℓ γ,
        loopArcKernel s N b (loopPrecedingLift X i) u) := by
    apply Finset.measurable_sum
    intro i _
    exact hi.comp (measurable_loopPrecedingLift N i)
  exact hsum.sub (hbg.const_mul 2)

end Riesz1

end
