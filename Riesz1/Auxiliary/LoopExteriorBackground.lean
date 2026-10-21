/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopExteriorGeometry
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Absolute convergence of the exterior background force

The deterministic exterior background integral is over a set
uniformly separated from the central interval and hence contains no singularity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- Separation from the closed exterior arcs. The endpoints `±M` may be included. -/
theorem loopExteriorBackground_nonsingular {N : ℕ+} {ℓ γ z u : ℝ}
    (hM : 0 < gradM N ℓ γ) (hP : GradPartial N ℓ γ)
    (hz : z ∈ Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4))
    (hu : u ∈ Icc (-(N : ℝ) / 2) (-gradM N ℓ γ) ∪
      Icc (gradM N ℓ γ) ((N : ℝ) / 2)) :
    (((z - u) / (N : ℝ) : ℝ) : UnitAddCircle) ≠ 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hPr : gradM N ℓ γ < (N : ℝ) / 8 := hP
  apply gradSplit_coe_ne_zero
  · rw [abs_pos]
    apply div_ne_zero _ hN.ne'
    apply sub_ne_zero.mpr
    rcases hu with hu | hu
    · exact (show u < z by linarith [hu.2, hz.1]).ne'
    · exact (show z < u by linarith [hu.1, hz.2]).ne
  · rw [abs_div, abs_of_pos hN, div_lt_one hN, abs_lt]
    rcases hu with hu | hu <;> constructor <;> linarith [hu.1, hu.2, hz.1, hz.2]

/-- The background force integral converges absolutely at every point of its carrier. -/
theorem integrableOn_loopExteriorBackground {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {N : ℕ+} {ℓ γ z : ℝ} (hM : 0 < gradM N ℓ γ) (hP : GradPartial N ℓ γ)
    (hz : z ∈ Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)) :
    IntegrableOn (fun u => deriv (loopArcG s N) (z - u)) (loopExteriorBackground N ℓ γ) := by
  let B := Icc (-(N : ℝ) / 2) (-gradM N ℓ γ) ∪ Icc (gradM N ℓ γ) ((N : ℝ) / 2)
  have hcont : ContinuousOn (fun u => deriv (loopArcG s N) (z - u)) B := by
    intro u hu
    have hc := contDiffAt_deriv_loopArcG hs hs1 N
      (loopExteriorBackground_nonsingular hM hP hz hu)
    have hl : ContDiffAt ℝ ∞ (fun u : ℝ => z - u) u := contDiffAt_const.sub contDiffAt_id
    exact (hc.comp u hl).continuousAt.continuousWithinAt
  apply (hcont.integrableOn_compact (isCompact_Icc.union isCompact_Icc)).mono_set
  intro u hu
  rcases hu with ⟨huN, huM⟩
  change u ∈ B
  dsimp [B]
  by_cases h : u ≤ -gradM N ℓ γ
  · exact Or.inl ⟨huN.1, h⟩
  · exact Or.inr ⟨by
      by_contra hm
      exact huM ⟨le_of_lt (lt_of_not_ge h), le_of_lt (lt_of_not_ge hm)⟩, huN.2⟩

end Riesz1

end
