/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BlockAverage
public import Riesz1.Rigidity.ExpectationBound

/-!
# Exact identities and means for the block difference

Supporting steps in the proof of Theorem 1.
The averaging identity includes the even full block: the same integer
representatives are translated in both averages, so no seam offset remains.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset

namespace Riesz1

/-- Translating a block center translates precisely its chosen representatives. -/
theorem cyclicRep_add (N : ℕ+) (k : ℕ) (i d : ℤ) :
    cyclicRep N k (i + d) = (cyclicRep N k i).map (addRightEmbedding d) := by
  unfold cyclicRep
  split <;> rw [map_add_right_Icc] <;> congr 1 <;> ring

/-- The block difference is the average of centered block lengths, including
when `2k = N`. This is the exact identity used to control its mean. -/
theorem centeredBlockDiff_eq_average {N : ℕ+} (X : Configuration N)
    (i : ℤ) {k : ℕ} (hk : 1 ≤ k) :
    centeredBlockDiff X i k = ((cyclicRep N k i).card : ℝ)⁻¹ *
      ∑ j ∈ cyclicRep N k i, (blockLength X j k - (k : ℝ)) := by
  have hc : ((cyclicRep N k i).card : ℝ) ≠ 0 := by
    exact_mod_cast (cyclicRep_card_pos hk i).ne'
  unfold centeredBlockDiff blockAverage
  rw [cyclicRep_add, card_map, sum_map]
  simp only [addRightEmbedding_apply]
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, blockLength, mul_sub,
    ← mul_sum]
  field_simp

/-- The two replacement errors and the block difference give exactly the
centered gap. This is equation (4.7). -/
theorem blockLength_sub_eq_block_errors {N : ℕ+} (X : Configuration N)
    (i : ℤ) (k : ℕ) :
    blockLength X i k - k =
      (N : ℝ) * (cyclicLift X (i + k) - blockAverage X (i + k) k) -
        (N : ℝ) * (cyclicLift X i - blockAverage X i k) + centeredBlockDiff X i k := by
  unfold blockLength centeredBlockDiff
  ring

/-- The block difference is periodic in its integer label. -/
theorem centeredBlockDiff_add_N {N : ℕ+} (X : Configuration N)
    (i : ℤ) {k : ℕ} (hk : 1 ≤ k) :
    centeredBlockDiff X (i + (N : ℕ)) k = centeredBlockDiff X i k := by
  unfold centeredBlockDiff
  rw [show i + (N : ℕ) + k = (i + k) + (N : ℕ) by omega,
    blockAverage_add_N X _ hk, blockAverage_add_N X _ hk]
  ring

namespace Internal

/-- Integrability of the block difference follows from that of its finitely
many block lengths under any finite measure. -/
theorem integrable_centeredBlockDiff_of_blockLength {N : ℕ+}
    {μ : Measure (Configuration N)} [IsFiniteMeasure μ] (i : ℤ) {k : ℕ}
    (hk : 1 ≤ k)
    (hi : ∀ j ∈ cyclicRep N k i, Integrable (fun X => blockLength X j k) μ) :
    Integrable (fun X => centeredBlockDiff X i k) μ := by
  simp_rw [centeredBlockDiff_eq_average _ _ hk]
  exact (integrable_finsetSum _ fun j hj => (hi j hj).sub (integrable_const _)).const_mul _

/-- Integrating the exact averaging identity introduces no unproved
integrability premise. -/
theorem integral_centeredBlockDiff_eq_average {N : ℕ+}
    {μ : Measure (Configuration N)} [IsProbabilityMeasure μ] (i : ℤ) {k : ℕ}
    (hk : 1 ≤ k)
    (hi : ∀ j ∈ cyclicRep N k i, Integrable (fun X => blockLength X j k) μ) :
    (∫ X, centeredBlockDiff X i k ∂μ) = ((cyclicRep N k i).card : ℝ)⁻¹ *
      ∑ j ∈ cyclicRep N k i, ((∫ X, blockLength X j k ∂μ) - (k : ℝ)) := by
  simp_rw [centeredBlockDiff_eq_average _ _ hk]
  have hs : ∀ j ∈ cyclicRep N k i,
      Integrable (fun X => blockLength X j k - (k : ℝ)) μ :=
    fun j hj => (hi j hj).sub (integrable_const _)
  rw [integral_const_mul, integral_finsetSum _ hs]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [integral_sub (hi j hj) (integrable_const _), integral_const,
    probReal_univ, one_smul]

end Internal

/-- The block difference is integrable under the Gibbs law. -/
theorem integrable_centeredBlockDiff (P : Parameters) (N : ℕ+)
    (i : ℤ) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (fun X => centeredBlockDiff X i k) (gibbsMeasure P N) := by
  let := isProbabilityMeasure_gibbsMeasure P N
  exact Internal.integrable_centeredBlockDiff_of_blockLength i hk
    (fun j _ => integrable_blockLength P N j k)

/-- Exact centering under the Gibbs law for every scale, in particular the
even full block. No separate centering convention is required. -/
theorem integral_centeredBlockDiff_gibbsMeasure (P : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (i : ℤ) {k : ℕ} (hk : 1 ≤ k) :
    (∫ X, centeredBlockDiff X i k ∂gibbsMeasure P N) = 0 := by
  let := isProbabilityMeasure_gibbsMeasure P N
  rw [Internal.integral_centeredBlockDiff_eq_average i hk
    (fun j _ => integrable_blockLength P N j k)]
  simp [integral_blockLength_gibbsMeasure P N hN]

/-- Integrability also holds under every actual constrained probability. -/
theorem integrable_centeredBlockDiff_constrained (P : Parameters) (N : ℕ+)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (i₀ i : ℤ) (L : ℕ)
    {R : ℝ} (hR : 0 < R) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (fun X => centeredBlockDiff X i k) (constrainedLaw P N θ i₀ L R) := by
  let := isProbabilityMeasure_constrainedLaw P N hθ hR i₀ L
  exact Internal.integrable_centeredBlockDiff_of_blockLength i hk
    (fun j _ => (blockLength_constrained_integral P N hθ i₀ L hR j k).1)

/-- The mean needed in the local case of the proof of
Theorem 1: a single constant controls the
mean for every cutoff, particle number, block center and scale `3k < N`. -/
theorem centeredBlockDiff_constrained_mean_bound (P : Parameters)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+)
      (_hN : 2 ≤ (N : ℕ)) (θ : ℝ → ℝ), IsForcingCutoff θ →
      ∀ (i : ℤ) (k : ℕ), 1 ≤ k → 3 * k < (N : ℕ) →
      |∫ X, centeredBlockDiff X i k
        ∂constrainedLaw P N θ (i - k) (3 * k) (((3 * k : ℕ) : ℝ) ^ (1 + γ))| ≤ C := by
  obtain ⟨C, hC, hb⟩ := expectation_under_convexification P hγ
  refine ⟨C, hC, ?_⟩
  intro hPL N hN θ hθ i k hk hkN
  have hkN' : 2 * k < (N : ℕ) := by omega
  have hL : 0 < 3 * k := by omega
  have hLr : (0 : ℝ) < (3 * k : ℕ) := by exact_mod_cast hL
  have hR : 0 < ((3 * k : ℕ) : ℝ) ^ (1 + γ) := Real.rpow_pos_of_pos hLr _
  let := isProbabilityMeasure_constrainedLaw P N hθ hR (i - k) (3 * k)
  have hi (j : ℤ) : Integrable (fun X : Configuration N => blockLength X j k)
      (constrainedLaw P N θ (i - k) (3 * k) (((3 * k : ℕ) : ℝ) ^ (1 + γ))) :=
    (blockLength_constrained_integral P N hθ (i - k) (3 * k) hR j k).1
  rw [Internal.integral_centeredBlockDiff_eq_average i hk (fun j _ => hi j), abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  have hm (j : ℤ) (hj : j ∈ cyclicRep N k i) :
      |(∫ X : Configuration N, blockLength X j k
          ∂constrainedLaw P N θ (i - k) (3 * k) (((3 * k : ℕ) : ℝ) ^ (1 + γ))) - k| ≤ C := by
    have hj' := (mem_cyclicRep_of_two_mul_lt hkN').mp hj
    exact (hb hPL N hN θ hθ (i - k) j (3 * k) k hL hkN hj'.1
      (by omega) (by omega)).2
  have hc : ((cyclicRep N k i).card : ℝ) ≠ 0 := by
    exact_mod_cast (cyclicRep_card_pos hk i).ne'
  calc ((cyclicRep N k i).card : ℝ)⁻¹ * |∑ j ∈ cyclicRep N k i, _| ≤
        ((cyclicRep N k i).card : ℝ)⁻¹ * ∑ j ∈ cyclicRep N k i, |(_ : ℝ)| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ ((cyclicRep N k i).card : ℝ)⁻¹ * ∑ _j ∈ cyclicRep N k i, C :=
      mul_le_mul_of_nonneg_left (sum_le_sum hm) (by positivity)
    _ = C := by simp [hc]

end Riesz1

end
