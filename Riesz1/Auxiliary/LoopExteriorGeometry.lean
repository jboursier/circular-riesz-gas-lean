/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopExteriorDefs
public import Riesz1.Auxiliary.GradientSplittingWindowKernel

/-!
# Separation of the exterior particles

On the event `𝒢`, every exterior summand is nonsingular
throughout the central interval. Both sides of the cyclic window are used, including
the upper bound supplied by the negative endpoint after translation by one period.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff

namespace Riesz1

/-- On the good event, an exterior lift lies between the two endpoint barriers,
possibly after adding one microscopic period. -/
theorem loopExteriorLift_barriers {N : ℕ+} {ℓ γ : ℝ}
    (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ) (hP : GradPartial N ℓ γ)
    {X : LoopPrecedingConfiguration N} (hX : X ∈ loopExteriorGood N ℓ γ)
    {j : ℤ} (hj : j ∈ loopExteriorLabels N ℓ γ) :
    (gradM N ℓ γ / 2 ≤ loopPrecedingLift X j ∧
      loopPrecedingLift X j ≤ (N : ℝ) - gradM N ℓ γ / 2) ∨
    (gradM N ℓ γ / 2 - (N : ℝ) ≤ loopPrecedingLift X j ∧
      loopPrecedingLift X j ≤ -gradM N ℓ γ / 2) := by
  have hM : 1 ≤ gradM N ℓ γ := Real.one_le_rpow hK hγ
  have hn0 : (0 : ℤ) ≤ ⌊gradM N ℓ γ⌋ := Int.floor_nonneg.mpr (by linarith)
  have hnN : 2 * ⌊gradM N ℓ γ⌋ < (N : ℤ) := by
    have hf := Int.floor_le (gradM N ℓ γ)
    have hPr : gradM N ℓ γ < (N : ℝ) / 8 := hP
    have : (2 : ℝ) * (⌊gradM N ℓ γ⌋ : ℤ) < N := by linarith
    exact_mod_cast this
  have hj' := Finset.mem_sdiff.mp hj
  have hrep := (Finset.mem_filter.mp hj'.1).2
  have hout : j < -⌊gradM N ℓ γ⌋ ∨ ⌊gradM N ℓ γ⌋ < j := by
    have hnot := hj'.2
    simp only [gradLabels, hP, ↓reduceIte, Finset.mem_Icc, not_and_or, not_le] at hnot
    exact hnot
  rcases hout with hjneg | hjpos
  · right
    constructor
    · have hb := (loopPrecedingLift_strictMono X).monotone
        (show ⌊gradM N ℓ γ⌋ ≤ j + N by omega)
      rw [loopPrecedingLift_add_N] at hb
      have hleft := hX.2.1
      linarith
    · exact ((loopPrecedingLift_strictMono X).monotone hjneg.le).trans hX.2.2
  · left
    constructor
    · exact hX.2.1.trans ((loopPrecedingLift_strictMono X).monotone hjpos.le)
    · have hb := (loopPrecedingLift_strictMono X).monotone
        (show j ≤ -⌊gradM N ℓ γ⌋ + N by omega)
      rw [loopPrecedingLift_add_N] at hb
      have hright := hX.2.2
      linarith

/-- No exterior particle meets the central interval, even across a periodic seam. -/
theorem loopExteriorLift_nonsingular {N : ℕ+} {ℓ γ : ℝ}
    (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ) (hP : GradPartial N ℓ γ)
    {X : LoopPrecedingConfiguration N} (hX : X ∈ loopExteriorGood N ℓ γ)
    {j : ℤ} (hj : j ∈ loopExteriorLabels N ℓ γ)
    {z : ℝ} (hz : z ∈ Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)) :
    (((z - loopPrecedingLift X j) / (N : ℝ) : ℝ) : UnitAddCircle) ≠ 0 := by
  have hM : 0 < gradM N ℓ γ := lt_of_lt_of_le zero_lt_one (Real.one_le_rpow hK hγ)
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  apply gradSplit_coe_ne_zero
  · apply (abs_pos.mpr _)
    apply div_ne_zero _ hN.ne'
    rcases loopExteriorLift_barriers hK hγ hP hX hj with hp | hn
    · have : z < loopPrecedingLift X j := by linarith [hz.2, hp.1]
      exact sub_ne_zero.mpr this.ne
    · have : loopPrecedingLift X j < z := by linarith [hz.1, hn.2]
      exact sub_ne_zero.mpr this.ne'
  · rw [abs_div, abs_of_pos hN, div_lt_one hN]
    rcases loopExteriorLift_barriers hK hγ hP hX hj with hp | hn
    · rw [abs_of_neg (by linarith [hz.2, hp.1])]
      linarith [hz.1, hp.2]
    · rw [abs_of_pos (by linarith [hz.1, hn.2])]
      linarith [hz.2, hn.1]

/-- Smoothness of the microscopic force off its periodic singularities. -/
theorem contDiffAt_deriv_loopArcG {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (N : ℕ+) {r : ℝ} (hr : ((r / (N : ℝ) : ℝ) : UnitAddCircle) ≠ 0) :
    ContDiffAt ℝ ∞ (deriv (loopArcG s N)) r := by
  have hg : ContDiffAt ℝ ∞ (hurwitzKernel s) (r / N) :=
    (gradSplit_contDiffOn_kernel s hs hs1).contDiffAt (gradSplit_isOpen_nonInt.mem_nhds hr)
  have hl : ContDiffAt ℝ ∞ (fun x : ℝ => x / (N : ℝ)) r := contDiffAt_id.div_const _
  have hc := ContDiffAt.comp (f := fun x : ℝ => x / (N : ℝ))
    (g := hurwitzKernel s) r hg hl
  have hf : ContDiffAt ℝ ∞ (loopArcG s N) r := by
    change ContDiffAt ℝ ∞ (fun x : ℝ => (N : ℝ) ^ (-s) * hurwitzKernel s (x / N)) r
    exact contDiffAt_const.mul hc
  exact hf.derivWithin (m := ∞) (by simp)

/-- Each exterior summand is continuous on the entire central interval. -/
theorem continuousOn_loopExteriorSummand {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {N : ℕ+} {ℓ γ : ℝ} (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ)
    (hP : GradPartial N ℓ γ) {X : LoopPrecedingConfiguration N}
    (hX : X ∈ loopExteriorGood N ℓ γ) {j : ℤ} (hj : j ∈ loopExteriorLabels N ℓ γ) :
    ContinuousOn (fun z => deriv (loopArcG s N) (z - loopPrecedingLift X j))
      (Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)) := by
  intro z hz
  have hl : ContDiffAt ℝ ∞ (fun z : ℝ => z - loopPrecedingLift X j) z :=
    contDiffAt_id.sub contDiffAt_const
  exact ((contDiffAt_deriv_loopArcG hs hs1 N
    (loopExteriorLift_nonsingular hK hγ hP hX hj hz)).comp z hl).continuousAt.continuousWithinAt

end Riesz1

end
