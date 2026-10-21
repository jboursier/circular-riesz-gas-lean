/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.SelectionBounds
public import Riesz1.Frozen.NormalizedGap

/-!
# Variables for the gap CLT

Block lengths and nearest labels are the existing definitions. Counts use the half-open interval,
including its right endpoint. Integer increments use real lifts directly, also for negative indices.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset

namespace Riesz1

variable {N : ℕ+}

/-- The gap normalization `b_{N,k}`. -/
def gapScale (s : RieszExponent) (N : ℕ+) (k : ℕ) : ℝ :=
  Real.sqrt ((N : ℝ) ^ s.val * periodicZeta s (((k : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle))

/-- The normalized centered block at any integer label. -/
def centeredGap (s : RieszExponent) (X : Configuration N) (i : ℤ) (k : ℕ)
    (_hk : 1 ≤ k ∧ k ≤ (N : ℕ) / 2) : ℝ :=
  (blockLength X i k - k) / gapScale s N k

/-- The averaging length of the normalized centered block. -/
def gapBiasWindow (k : ℕ) : ℕ := Nat.sqrt k

/-- Particles following label `i` in a real interval of length `t < 1`.
The last possible particle, at `i + N`, is excluded by the strict upper bound on `t`. -/
def gapWindowIndices (X : Configuration N) (i : ℤ) (t : ℝ) : Finset ℕ :=
  (range ((N : ℕ) - 1)).filter
    (fun a => cyclicLift X (i + 1 + a) ≤ cyclicLift X i + t)

/-- The integer count, on its full carrier `k < N`. -/
def selectedCount (X : Configuration N) (k : ℕ) (_hk : k < (N : ℕ)) : ℕ :=
  (gapWindowIndices X (nearestLabel X) ((k : ℝ) / (N : ℝ))).card

/-- The centered selected count `Δ_{N,k}`. -/
def selectedDiscrepancy (X : Configuration N) (k : ℕ) (hk : k < (N : ℕ)) : ℤ :=
  (selectedCount X k hk : ℤ) - k

/-- The short increment `T_{N,k,r}`, expressed in lifts for every integer `r`. -/
def selectedIncrement (X : Configuration N) (k : ℕ) (r : ℤ) : ℝ :=
  (N : ℝ) * (cyclicLift X (nearestLabel X + k + r) -
    cyclicLift X (nearestLabel X + k)) - r

lemma blockLength_zero (X : Configuration N) (i : ℤ) : blockLength X i 0 = 0 := by
  simp [blockLength]

lemma blockLength_add_N (X : Configuration N) (i : ℤ) (k : ℕ) :
    blockLength X (i + (N : ℕ)) k = blockLength X i k := by
  unfold blockLength
  rw [show i + (N : ℕ) + k = (i + k) + (N : ℕ) by ring,
    cyclicLift_add_N, cyclicLift_add_N]
  ring

lemma blockLength_add_period_mul (X : Configuration N) (i q : ℤ) (k : ℕ) :
    blockLength X (i + (N : ℕ) * q) k = blockLength X i k := by
  unfold blockLength
  rw [show i + (N : ℕ) * q + k = (i + k) + (N : ℕ) * q by ring,
    lift_add_mul_eq (cyclicLift X) (cyclicLift_periodic X),
    lift_add_mul_eq (cyclicLift X) (cyclicLift_periodic X)]
  ring

lemma centeredGap_add_N (s : RieszExponent) (X : Configuration N) (i : ℤ) (k : ℕ)
    (hk : 1 ≤ k ∧ k ≤ (N : ℕ) / 2) :
    centeredGap s X (i + (N : ℕ)) k hk = centeredGap s X i k hk := by
  simp only [centeredGap, blockLength_add_N]

lemma centeredGap_eq_normalizedGap (P : Parameters) (N : ℕ+) (k : ℕ)
    (hk : 1 ≤ k ∧ k ≤ (N : ℕ) / 2) (X : Configuration N) :
    centeredGap (parametersExponent P) X 0 k hk = normalizedGap P N k hk X := by
  simp [centeredGap, gapScale, normalizedGap, blockLength, parametersExponent]

lemma gapBiasWindow_pos {k : ℕ} (hk : 1 ≤ k) : 1 ≤ gapBiasWindow k := by
  exact Nat.le_sqrt.mpr (by simpa using hk)

lemma gapBiasWindow_le (k : ℕ) : gapBiasWindow k ≤ k := Nat.sqrt_le_self k

lemma selectedCount_le (X : Configuration N) (k : ℕ) (hk : k < (N : ℕ)) :
    selectedCount X k hk ≤ (N : ℕ) - 1 := by
  exact (card_filter_le _ _).trans_eq (card_range _)

lemma measurable_centeredGap (s : RieszExponent) (i : ℤ) (k : ℕ)
    (hk : 1 ≤ k ∧ k ≤ (N : ℕ) / 2) :
    Measurable (fun X : Configuration N => centeredGap s X i k hk) :=
  ((measurable_blockLength i k).sub_const _).div_const _

lemma measurable_selectedIncrement (k : ℕ) (r : ℤ) :
    Measurable (fun X : Configuration N => selectedIncrement X k r) := by
  have hm (a : ℤ) : Measurable (fun X : Configuration N =>
      cyclicLift X (nearestLabel X + a)) := by
    have h : Measurable (fun q : Configuration N × ℤ => cyclicLift q.1 (q.2 + a)) :=
      measurable_from_prod_countable_left
        (fun j : ℤ => measurable_cyclicLift (N := N) (j + a))
    exact h.comp (measurable_id.prodMk (measurable_nearestLabel N))
  have hkr : Measurable (fun X : Configuration N =>
      cyclicLift X (nearestLabel X + k + r)) := by
    simpa only [add_assoc] using hm ((k : ℤ) + r)
  exact (measurable_const.mul (hkr.sub (hm k))).sub_const _

end Riesz1

end
end
