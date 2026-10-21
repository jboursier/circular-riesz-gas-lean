/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.ConvexificationEnergyPairs
public import Riesz1.HelfferSjostrand.RieszAdmissiblePerturbation

/-!
# Admissibility of the actual nearest-neighbour tilt

The smooth forcing contributes globally smooth pair potentials. Their
first two derivatives are bounded on the closed unit interval, so the
Riesz perturbation theorem applies to precisely `nearestTiltedPairs`.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff

namespace Riesz1.APrioriComparison

/-- The actual pair representation used by the comparison energy is admissible. -/
theorem nearestTiltedPairs_admissible (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (K γ ε : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, HsAdmissible (nearestTiltedPairs P N hθ K γ ε hK) C := by
  apply hsRiesz_perturbed_admissible
  · exact hN
  · intro i j _
    have hs := nearestPairPenalty_smooth P.val.1 hθ N
      (nearestPairs N (window N K γ)) (K ^ ε) i j
    have hd : ContDiff ℝ ∞ (deriv (nearestPairPenalty P.val.1 θ N
        (nearestPairs N (window N K γ)) (K ^ ε) i j)) := (contDiff_infty_iff_deriv.mp hs).2
    obtain ⟨M₁, hM₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (hs.continuous_deriv (by simp)).continuousOn
    obtain ⟨M₂, hM₂⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (hd.continuous_deriv (by simp)).continuousOn
    refine ⟨max M₁ M₂, fun r hr => ?_⟩
    have hr' : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.le⟩
    have hb₁ : |deriv (nearestPairPenalty P.val.1 θ N
        (nearestPairs N (window N K γ)) (K ^ ε) i j) r| ≤ M₁ := by
      simpa only [Real.norm_eq_abs] using hM₁ r hr'
    have hb₂ : |deriv (deriv (nearestPairPenalty P.val.1 θ N
        (nearestPairs N (window N K γ)) (K ^ ε) i j)) r| ≤ M₂ := by
      simpa only [Real.norm_eq_abs] using hM₂ r hr'
    exact ⟨hb₁.trans (le_max_left _ _), hb₂.trans (le_max_right _ _)⟩

end Riesz1.APrioriComparison

end
