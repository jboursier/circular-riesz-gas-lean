/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.BellQuadrature
public import Riesz1.Rigidity.InverseBlocks

/-!
# Absolute integrability of the random averaged kernel

The integrability assertion of the random-sum part of Lemma B.1. A block and its
complement control the two singular endpoints of `bellKernel`. This part does not
use rigidity. Constants in the moment bound are chosen before the particle number,
the block, the scale, the profile and the external input `External.PrekopaLeindler`.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace Riesz1

/-- The remaining cyclic block has the complementary microscopic length. -/
lemma bell_block_complement {N : ℕ+} (X : Configuration N) (j : ℤ) {k : ℕ}
    (hk : k ≤ (N : ℕ)) :
    blockLength X (j + k) ((N : ℕ) - k) = (N : ℝ) - blockLength X j k := by
  have he : j + (k : ℤ) + (((N : ℕ) - k : ℕ) : ℤ) = j + (N : ℕ) := by
    omega
  unfold blockLength
  rw [he, cyclicLift_add_N]
  ring

/-- A proper nonempty block lies strictly between the kernel's two singularities. -/
lemma bell_block_mem {N : ℕ+} (X : Configuration N) (j : ℤ) {k : ℕ}
    (hk : 0 < k) (hkN : k < (N : ℕ)) :
    blockLength X j k ∈ Ioo (0 : ℝ) (N : ℝ) := by
  refine ⟨blockLength_pos X j hk, ?_⟩
  have h := blockLength_pos X (j + k) (show 0 < (N : ℕ) - k by omega)
  rw [bell_block_complement X j hkN.le] at h
  linarith

/-- Block lengths are continuous functions on the configuration carrier. -/
lemma continuous_bell_blockLength (N : ℕ+) (j : ℤ) (k : ℕ) :
    Continuous (fun X : Configuration N => blockLength X j k) := by
  unfold blockLength cyclicLift
  exact continuous_const.mul
    ((((continuous_apply _).comp continuous_subtype_val).add continuous_const).sub
      (((continuous_apply _).comp continuous_subtype_val).add continuous_const))

/-- The averaged kernel evaluated at a proper block is continuous. -/
lemma continuous_bellKernel_blockLength {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {N : ℕ+} (j : ℤ) {k : ℕ} (hk : 0 < k) (hkN : k < (N : ℕ))
    {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    Continuous (fun X : Configuration N => bellKernel s N ℓ ψ (blockLength X j k)) := by
  rw [continuous_iff_continuousAt]
  intro X
  exact (hasDerivAt_bellKernel hs hs1 N.pos hℓ hψ
    (bell_block_mem X j hk hkN)).continuousAt.comp (f := fun Y : Configuration N => blockLength Y j k)
    (continuous_bell_blockLength N j k).continuousAt

/-- Absolute integrability of every expectation in the random-sum part of Lemma B.1.
The estimate is uniform in every proper block, and needs no rigidity hypothesis. -/
theorem bell_random_kernel_integrable (P : Parameters) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (j : ℤ) (k : ℕ),
      0 < k → k < (N : ℕ) → ∀ (ℓ : ℝ) (ψ : ℝ → ℝ),
      0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      Integrable (fun X : Configuration N => bellKernel P.1.2 N ℓ ψ (blockLength X j k))
        (gibbsMeasure P N) ∧
      (∫ X : Configuration N, |bellKernel P.1.2 N ℓ ψ (blockLength X j k)|
        ∂gibbsMeasure P N) ≤
          C * bellConstant ℓ ψ * ((k : ℝ) ^ (-P.1.2) + ((N : ℕ) - k : ℝ) ^ (-P.1.2)) := by
  obtain ⟨Cq, hCq, hq⟩ := bell_kernel P.1.2 P.2.2.1 P.2.2.2
  obtain ⟨Cm, hCm, hm⟩ := inverse_blocks_uniform P P.2.2.1
  refine ⟨Cq * Cm, mul_pos hCq hCm, ?_⟩
  intro hPL N j k hk hkN ℓ ψ hℓ hℓ1 hNℓ hψ hper
  have hA : 0 ≤ bellConstant ℓ ψ := mul_nonneg hℓ.le (bellEnergy_nonneg hℓ)
  have hCA : 0 ≤ Cq * bellConstant ℓ ψ := mul_nonneg hCq.le hA
  obtain ⟨hi, hb⟩ := hm hPL N j k hk
  obtain ⟨hi', hb'⟩ := hm hPL N (j + k) ((N : ℕ) - k) (by omega)
  have hdom : ∀ X : Configuration N,
      |bellKernel P.1.2 N ℓ ψ (blockLength X j k)| ≤ Cq * bellConstant ℓ ψ *
        (blockLength X j k ^ (-P.1.2) + blockLength X (j + k) ((N : ℕ) - k) ^ (-P.1.2)) := by
    intro X
    have hx := bell_block_mem X j hk hkN
    refine ((hq N ℓ ψ N.pos hℓ hℓ1 hNℓ hψ hper).2.2.1 _ hx).trans ?_
    apply mul_le_mul_of_nonneg_left _ hCA
    rw [bell_block_complement X j hkN.le]
    exact rpow_min_le_add _ _ _ hx.1 (sub_pos.mpr hx.2)
  have hint : Integrable (fun X : Configuration N =>
      bellKernel P.1.2 N ℓ ψ (blockLength X j k)) (gibbsMeasure P N) := by
    apply ((hi.add hi').const_mul (Cq * bellConstant ℓ ψ)).mono'
      (continuous_bellKernel_blockLength P.2.2.1 P.2.2.2 j hk hkN hℓ hψ).aestronglyMeasurable
    exact ae_of_all _ fun X => by simpa only [Real.norm_eq_abs, Pi.add_apply] using hdom X
  refine ⟨hint, ?_⟩
  have hmi : (∫ X : Configuration N, blockLength X j k ^ (-P.1.2) ∂gibbsMeasure P N) ≤
      Cm * (k : ℝ) ^ (-P.1.2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun X => Real.rpow_nonneg (blockLength_pos X j hk).le _)] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
  have hmi' : (∫ X : Configuration N, blockLength X (j + k) ((N : ℕ) - k) ^ (-P.1.2)
      ∂gibbsMeasure P N) ≤ Cm * (((N : ℕ) - k : ℕ) : ℝ) ^ (-P.1.2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi'
      (ae_of_all _ fun X => Real.rpow_nonneg (blockLength_pos X (j + k) (by omega)).le _)] at hb'
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb'
  calc (∫ X : Configuration N, |bellKernel P.1.2 N ℓ ψ (blockLength X j k)|
        ∂gibbsMeasure P N)
      ≤ ∫ X : Configuration N, Cq * bellConstant ℓ ψ *
        (blockLength X j k ^ (-P.1.2) + blockLength X (j + k) ((N : ℕ) - k) ^ (-P.1.2))
        ∂gibbsMeasure P N :=
          integral_mono hint.abs ((hi.add hi').const_mul _) hdom
    _ = Cq * bellConstant ℓ ψ *
        ((∫ X : Configuration N, blockLength X j k ^ (-P.1.2) ∂gibbsMeasure P N) +
          ∫ X : Configuration N, blockLength X (j + k) ((N : ℕ) - k) ^ (-P.1.2)
            ∂gibbsMeasure P N) := by rw [integral_const_mul, integral_add hi hi']
    _ ≤ Cq * bellConstant ℓ ψ *
        (Cm * (k : ℝ) ^ (-P.1.2) + Cm * (((N : ℕ) - k : ℕ) : ℝ) ^ (-P.1.2)) :=
          mul_le_mul_of_nonneg_left (add_le_add hmi hmi') hCA
    _ = _ := by rw [Nat.cast_sub hkN.le]; ring

end Riesz1

end
