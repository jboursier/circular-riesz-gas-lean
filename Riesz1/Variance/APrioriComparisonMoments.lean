/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriComparisonComparator
public import Riesz1.Unconditional.LoopMoments
public import Riesz1.Auxiliary.BellRandomSumIntegrability

/-!
# Moments of anchored errors for a priori comparison

The short-block moment estimate supplied by rigidity also bounds the
anchored coordinate error at labels on either side of the origin. For
labels past the antipode, use the complementary block and reverse sign.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset

namespace Riesz1.APrioriComparison

/-- Rigidity moments of every nonzero anchored coordinate error. -/
theorem anchoredError_moments (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < min (P.val.2 / 2) δ₀ →
      ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ i : Fin (N : ℕ), i ≠ ⟨0, N.pos⟩ →
        eLpNorm (fun X : Configuration N =>
          ((N : ℕ) : ℝ) * (X.val i - X.val ⟨0, N.pos⟩) - (i : ℕ)) 2 (gibbsMeasure P N) ≤
            ENNReal.ofReal (C * (labelDistToOne N i : ℝ) ^ (P.val.2 / 2 + δ)) := by
  obtain ⟨δ₀, hδ₀, hb⟩ := (auxiliary_Loop_moments hBE hPL P.val.1 P.val.2
    P.2.1 P.2.2.1 P.2.2.2).2.2.2
  refine ⟨δ₀, hδ₀, fun δ hδ hδlt => ?_⟩
  obtain ⟨C, hC, hblock⟩ := (hb δ hδ hδlt 2 (by norm_num)).2
  refine ⟨C, hC, fun N hN i hi => ?_⟩
  have hi0 : 1 ≤ i.val := by
    have : i.val ≠ 0 := fun h => hi (Fin.ext h)
    omega
  have hiN := i.isLt
  have hblock0 (X : Configuration N) : blockLength X 0 i.val =
      ((N : ℕ) : ℝ) * (X.val i - X.val ⟨0, N.pos⟩) := by
    simp only [blockLength, zero_add, cyclicLift_natCast]
    rw [show cyclicLift X 0 = X.val ⟨0, N.pos⟩ by
      simpa using cyclicLift_natCast X ⟨0, N.pos⟩]
  by_cases hh : i.val ≤ (N : ℕ) / 2
  · have hd : labelDistToOne N i = i.val := by rw [labelDistToOne_eq]; omega
    rw [hd]
    have h := hblock N hN ⟨0, N.pos⟩ i.val hi0 hh
    norm_num only [ENNReal.ofReal_ofNat, Fin.val_zero, Nat.cast_zero] at h
    simpa only [hblock0] using h
  · have hk1 : 1 ≤ (N : ℕ) - i.val := by omega
    have hkN : (N : ℕ) - i.val ≤ (N : ℕ) / 2 := by omega
    have hd : labelDistToOne N i = (N : ℕ) - i.val := by rw [labelDistToOne_eq]; omega
    rw [hd]
    have h := hblock N hN i ((N : ℕ) - i.val) hk1 hkN
    norm_num only [ENNReal.ofReal_ofNat] at h
    have heq : (fun X : Configuration N =>
        ((N : ℕ) : ℝ) * (X.val i - X.val ⟨0, N.pos⟩) - (i : ℕ)) =
        -(fun X : Configuration N => blockLength X (i : ℕ) ((N : ℕ) - i.val) -
          ((N : ℕ) - i.val : ℕ)) := by
      funext X
      have hc := bell_block_complement X 0 (Nat.le_of_lt hiN)
      simp only [zero_add, hblock0] at hc
      simp only [Pi.neg_apply]
      rw [hc, Nat.cast_sub (Nat.le_of_lt hiN)]
      ring
    rw [heq, eLpNorm_neg]
    exact h

end Riesz1.APrioriComparison

end
