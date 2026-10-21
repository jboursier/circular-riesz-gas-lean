/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.BellRandomSumMoments
public import Riesz1.Auxiliary.BellRandomSumWeights

/-!
# Summable comparison error for a short block

The random-sum part of Lemma B.1, before summing over block lengths.
The global mean value estimate is integrated by Cauchy--Schwarz. The
second moments have orders `k^(3s/2)` and `k^(-2-2s)`, respectively,
giving the summable error `k^(-1-s/4)`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- Simplify the product of two scaled square roots. -/
lemma bell_sqrt_rpow_product {x D M : ℝ} (hx : 0 < x) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (u v : ℝ) :
    Real.sqrt (D * x ^ u) * Real.sqrt (M * x ^ v) =
      Real.sqrt D * Real.sqrt M * x ^ ((u + v) / 2) := by
  rw [Real.sqrt_mul hD, Real.sqrt_mul hM,
    Real.sqrt_eq_rpow (x ^ u), Real.sqrt_eq_rpow (x ^ v),
    ← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le]
  calc _ = Real.sqrt D * Real.sqrt M * (x ^ (u * (1 / 2)) * x ^ (v * (1 / 2))) := by ring
    _ = _ := by rw [← Real.rpow_add hx]; congr 2; ring

namespace Internal

/-- A uniform, summable error for each short block, conditional on rigidity. -/
theorem bell_random_short_of_rigidity (beta s : ℝ) (hbeta : 0 < beta)
    (hs : 0 < s) (hs1 : s < 1) (hRig : RigidityConclusion beta s hbeta hs hs1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+),
      2 ≤ (N : ℕ) → ∀ (i : Fin (N : ℕ)) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
      ∀ (ℓ : ℝ) (ψ : ℝ → ℝ), 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      |(∫ X : Configuration N, bellKernel s N ℓ ψ (blockLength X (i : ℕ) k)
          ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) -
        bellKernel s N ℓ ψ (k : ℝ)| ≤
          C * bellConstant ℓ ψ * (k : ℝ) ^ (-1 - s / 4) := by
  let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
  obtain ⟨Cq, hCq, hq⟩ := bell_kernel s hs hs1
  obtain ⟨D, hD, hmom⟩ := bell_block_second_moment_of_rigidity beta s hbeta hs hs1 hRig
  obtain ⟨M, hM, hweight⟩ := bell_comparison_weight_second_moment P
  obtain ⟨Ci, _, hiq⟩ := bell_random_kernel_integrable P
  refine ⟨Cq * (Real.sqrt D * Real.sqrt M), by positivity, ?_⟩
  intro hPL N hN i k hk hkN ℓ ψ hℓ hℓ1 hNℓ hψ hper
  have := (modelWellDefined P N).2.2
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hkN' : k < (N : ℕ) := by omega
  have hkR : (k : ℝ) < N := by exact_mod_cast hkN'
  have hA : 0 ≤ Cq * bellConstant ℓ ψ :=
    mul_nonneg hCq.le (mul_nonneg hℓ.le (bellEnergy_nonneg hℓ))
  obtain ⟨hiZ, hbZ⟩ := hmom hPL N hN i k hk hkN
  obtain ⟨hiW, hbW⟩ := hweight hPL N (i : ℕ) k hk hkN
  have hZ : AEStronglyMeasurable
      (fun X : Configuration N => blockLength X (i : ℕ) k - k) (gibbsMeasure P N) :=
    ((measurable_blockLength _ _).sub_const _).aestronglyMeasurable
  have hW := (measurable_bellComparisonWeight s N (i : ℕ) k).aestronglyMeasurable
    (μ := gibbsMeasure P N)
  obtain ⟨hiZW, hbZW⟩ := integral_abs_mul_le_sqrt_second_moments hZ hW hiZ hiW hbZ hbW
  have hcs : (∫ X : Configuration N, |blockLength X (i : ℕ) k - k| *
      |bellComparisonWeight s (i : ℕ) k X| ∂gibbsMeasure P N) ≤
        Real.sqrt D * Real.sqrt M * (k : ℝ) ^ (-1 - s / 4) := by
    convert hbZW using 1
    rw [bell_sqrt_rpow_product hk0 hD.le hM.le]
    congr 2
    ring
  have hqi : Integrable (fun X : Configuration N =>
      bellKernel s N ℓ ψ (blockLength X (i : ℕ) k)) (gibbsMeasure P N) :=
    (hiq hPL N (i : ℕ) k hk hkN' ℓ ψ hℓ hℓ1 hNℓ hψ hper).1
  have hiDiff : Integrable (fun X : Configuration N =>
      bellKernel s N ℓ ψ (blockLength X (i : ℕ) k) - bellKernel s N ℓ ψ (k : ℝ))
      (gibbsMeasure P N) := hqi.sub (integrable_const _)
  have hpoint (X : Configuration N) :
      |bellKernel s N ℓ ψ (blockLength X (i : ℕ) k) - bellKernel s N ℓ ψ (k : ℝ)| ≤
        (Cq * bellConstant ℓ ψ) *
          (|blockLength X (i : ℕ) k - k| * |bellComparisonWeight s (i : ℕ) k X|) := by
    have hd := (hq N ℓ ψ N.pos hℓ hℓ1 hNℓ hψ hper).2.2.2
    have hh := bell_kernel_difference_bound hs hs1 N.pos hℓ hψ hCq.le hd
      (bell_block_mem X (i : ℕ) hk hkN') ⟨hk0, hkR⟩
    rw [← bell_block_complement X (i : ℕ) hkN'.le, ← Nat.cast_sub hkN'.le] at hh
    rw [abs_of_nonneg (bellComparisonWeight_nonneg s (i : ℕ) hk hkN' X)]
    exact hh.trans_eq (by unfold bellComparisonWeight; ring)
  have heq : (∫ X : Configuration N,
      bellKernel s N ℓ ψ (blockLength X (i : ℕ) k) - bellKernel s N ℓ ψ (k : ℝ)
      ∂gibbsMeasure P N) =
        (∫ X : Configuration N, bellKernel s N ℓ ψ (blockLength X (i : ℕ) k)
          ∂gibbsMeasure P N) - bellKernel s N ℓ ψ (k : ℝ) := by
    rw [integral_sub hqi (integrable_const _)]
    simp
  rw [← heq]
  calc _ ≤ ∫ X : Configuration N,
        |bellKernel s N ℓ ψ (blockLength X (i : ℕ) k) - bellKernel s N ℓ ψ (k : ℝ)|
        ∂gibbsMeasure P N := abs_integral_le_integral_abs
    _ ≤ ∫ X : Configuration N, (Cq * bellConstant ℓ ψ) *
        (|blockLength X (i : ℕ) k - k| * |bellComparisonWeight s (i : ℕ) k X|)
        ∂gibbsMeasure P N := integral_mono hiDiff.abs (hiZW.const_mul _) hpoint
    _ = (Cq * bellConstant ℓ ψ) *
        (∫ X : Configuration N, |blockLength X (i : ℕ) k - k| *
          |bellComparisonWeight s (i : ℕ) k X| ∂gibbsMeasure P N) := integral_const_mul _ _
    _ ≤ (Cq * bellConstant ℓ ψ) *
        (Real.sqrt D * Real.sqrt M * (k : ℝ) ^ (-1 - s / 4)) :=
          mul_le_mul_of_nonneg_left hcs hA
    _ = _ := by ring

end Internal

end Riesz1

end
