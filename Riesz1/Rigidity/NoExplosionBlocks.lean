/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BlockMoments
public import Riesz1.Rigidity.NoExplosionEndpoints
public import Riesz1.ToMathlib.LogConcave.NegativePower

/-!
# Deterministic inverse-moment comparison for blocks

The finite Jensen step in Lemma 4.5.
It requires no independence or probabilistic hypotheses.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- The inverse power of an average of gaps is bounded by the average of their
inverse powers, the deterministic step of Lemma 4.5. -/
theorem blockLength_inverse_rpow_le {N : ℕ+} (X : Configuration N) (j : ℤ)
    {L : ℕ} (hL : 0 < L) {p : ℝ} (hp : 0 < p) :
    blockLength X j L ^ (-p) ≤ (L : ℝ) ^ (-p) *
      ((L : ℝ)⁻¹ * ∑ r ∈ Finset.range L, gap X (j + r) ^ (-p)) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hj := (convexOn_rpow_neg_Ioi hp).map_sum_le (t := Finset.range L)
    (w := fun _ => (L : ℝ)⁻¹) (p := fun r : ℕ => gap X (j + r))
    (fun _ _ => inv_nonneg.mpr hLr.le) (by simp [hLr.ne'])
    (fun _ _ => gap_pos X _)
  simp only [smul_eq_mul, ← Finset.mul_sum, ← blockLength_eq_sum] at hj
  have he : (L : ℝ) ^ (-p) * ((L : ℝ)⁻¹ * blockLength X j L) ^ (-p) =
      blockLength X j L ^ (-p) := by
    rw [← Real.mul_rpow hLr.le (mul_nonneg (inv_nonneg.mpr hLr.le) (blockLength_pos X j hL).le)]
    congr 1
    rw [← mul_assoc, mul_inv_cancel₀ hLr.ne', one_mul]
  rw [← he]
  exact mul_le_mul_of_nonneg_left hj (Real.rpow_nonneg hLr.le _)

/-- Every inverse block moment is integrable at fixed particle number.
The uniform-in-`N` bound needs the uniform nearest-gap estimate. -/
theorem integrable_blockLength_inverse_rpow (P : Parameters) (n : ℕ) (j : ℤ)
    {L : ℕ} (hL : 0 < L) {p : ℝ} (hp : 0 < p) :
    Integrable (fun X : Configuration (n + 1).succPNat => blockLength X j L ^ (-p))
      (gibbsMeasure P (n + 1).succPNat) := by
  have hi : MeasureTheory.Integrable (fun X : Configuration (n + 1).succPNat =>
      (L : ℝ) ^ (-p) * ((L : ℝ)⁻¹ *
        ∑ r ∈ Finset.range L, gap X (j + r) ^ (-p))) (gibbsMeasure P (n + 1).succPNat) :=
    ((MeasureTheory.integrable_finsetSum (Finset.range L) (fun (r : ℕ) _ =>
      integrable_gap_inverse_rpow P n (j + r) hp.le)).const_mul (L : ℝ)⁻¹).const_mul _
  apply hi.mono' ((measurable_blockLength j L).pow_const (-p)).aestronglyMeasurable
  exact MeasureTheory.ae_of_all _ fun X => by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (blockLength_pos X j hL).le _)]
    exact blockLength_inverse_rpow_le X j hL hp

end Riesz1

end
