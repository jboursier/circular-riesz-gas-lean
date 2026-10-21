/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopEstimates

/-!
# Boundary checks for loop localization

The two-particle regime is always a full window when `K ≥ 1` and `γ ≥ 0`.
The zero envelope gives a constant transport, whose actual loop is zero.
These checks use the definitions on their whole carriers.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1.Internal

/-- Every admissible two-particle scale is a full window. -/
theorem loopEstimates_two_full {ℓ γ : ℝ} (hK : 1 ≤ (2 : ℝ) * ℓ) (hγ : 0 ≤ γ) :
    ¬GradPartial (1 : ℕ).succPNat ℓ γ := by
  have hp := Real.one_le_rpow hK hγ
  change ¬((2 : ℝ) * ℓ) ^ γ < (2 : ℝ) / 8
  linarith

/-- The zero derivative envelope forces the smooth transport to be constant. -/
theorem loopEstimates_zero_envelope_constant {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {s a K L : ℝ}
    (hd : ∀ t, |deriv ψ t| ≤ 0 * gradWeightOne s a K L t) :
    ∀ t, ψ t = ψ 0 := by
  have hz : ∀ t, deriv ψ t = 0 := by
    intro t
    have hh := hd t
    rw [zero_mul] at hh
    exact abs_nonpos_iff.mp hh
  exact fun t => is_const_of_deriv_eq_zero (hψ.differentiable (by simp)) hz t 0

/-- A constant microscopic transport has zero loop, also for two particles. -/
theorem loopEstimates_constant_loop (s c : ℝ) (N : ℕ+) (X : Configuration N) :
    loopArcL s N (fun _ => c) X = 0 := by
  simp [loopArcL, loopArcKernel]

end Riesz1.Internal

end
