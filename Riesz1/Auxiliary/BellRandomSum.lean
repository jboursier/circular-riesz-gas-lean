/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.BellRandomSumShort
public import Mathlib.Analysis.PSeries

/-!
# Random block lengths versus a lattice, conditional on rigidity

The random-sum part of Lemma B.1, including absolute integrability. The
short-block error is summable. A long block is replaced pointwise by its
complement and the averaged kernel is reflected. No invariance of the
gap law is needed for this last step.
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Riesz1

/-- Reversing the proper block lengths permutes their finite sum. -/
lemma bell_sum_complement (N : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 (N - 1), f (N - k)) = ∑ k ∈ Finset.Icc 1 (N - 1), f k := by
  apply Finset.sum_bij (fun k _ => N - k)
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_Icc] at ha hb
    omega
  · intro b hb
    refine ⟨N - b, ?_, ?_⟩
    · simp only [Finset.mem_Icc] at hb ⊢
      omega
    · simp only [Finset.mem_Icc] at hb
      omega
  · intro k hk
    rfl

namespace Internal

/-- **Random block lengths versus a lattice**, the random-sum part of Lemma B.1.
The constant is chosen before the external input, particle number, scale and
smooth profile. All expectations are absolutely integrable. -/
theorem bell_random_sum_of_rigidity (beta s : ℝ) (hbeta : 0 < beta)
    (hs : 0 < s) (hs1 : s < 1) (hRig : RigidityConclusion beta s hbeta hs hs1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+),
      2 ≤ (N : ℕ) → ∀ (ℓ : ℝ) (ψ : ℝ → ℝ),
      0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ k ∈ Finset.Icc 1 ((N : ℕ) - 1),
        Integrable (fun X : Configuration N => bellKernel s N ℓ ψ (blockLength X 0 k))
          (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N)) ∧
      (∑ k ∈ Finset.Icc 1 ((N : ℕ) - 1),
        |(∫ X : Configuration N, bellKernel s N ℓ ψ (blockLength X 0 k)
          ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) -
          bellKernel s N ℓ ψ (k : ℝ)|) ≤ C * bellConstant ℓ ψ := by
  let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
  obtain ⟨C0, hC0, hb⟩ := bell_random_short_of_rigidity beta s hbeta hs hs1 hRig
  obtain ⟨Ci, _, hi⟩ := bell_random_kernel_integrable P
  let f : ℕ → ℝ := fun k => (k : ℝ) ^ (-1 - s / 4)
  have hf : Summable f := Real.summable_nat_rpow.mpr (by linarith)
  have hf0 (k : ℕ) : 0 ≤ f k := Real.rpow_nonneg (Nat.cast_nonneg k) _
  have hts : 0 ≤ ∑' k, f k := tsum_nonneg hf0
  refine ⟨2 * C0 * (1 + ∑' k, f k), by positivity, ?_⟩
  intro hPL N hN ℓ ψ hℓ hℓ1 hNℓ hψ hper
  have hA : 0 ≤ C0 * bellConstant ℓ ψ :=
    mul_nonneg hC0.le (mul_nonneg hℓ.le (bellEnergy_nonneg hℓ))
  refine ⟨?_, ?_⟩
  · intro k hk
    have hkm := Finset.mem_Icc.mp hk
    exact (hi hPL N 0 k hkm.1 (by omega) ℓ ψ hℓ hℓ1 hNℓ hψ hper).1
  have hb' (k : ℕ) (hk : k ∈ Finset.Icc 1 ((N : ℕ) - 1)) :
      |(∫ X : Configuration N, bellKernel s N ℓ ψ (blockLength X 0 k)
        ∂gibbsMeasure P N) - bellKernel s N ℓ ψ (k : ℝ)| ≤
        C0 * bellConstant ℓ ψ * (f k + f ((N : ℕ) - k)) := by
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    have hkN' : k < (N : ℕ) := by omega
    by_cases hh : k ≤ (N : ℕ) / 2
    · have hshort := hb hPL N hN ⟨0, N.pos⟩ k hk1 hh ℓ ψ hℓ hℓ1 hNℓ hψ hper
      have hzero : (((⟨0, N.pos⟩ : Fin (N : ℕ)) : ℕ) : ℤ) = 0 := rfl
      rw [hzero] at hshort
      exact hshort.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hf0 _)) hA)
    · have hlen : 1 ≤ (N : ℕ) - k := by omega
      have hhalf : (N : ℕ) - k ≤ (N : ℕ) / 2 := by omega
      have hshort := hb hPL N hN ⟨k, hkN'⟩ ((N : ℕ) - k) hlen hhalf
        ℓ ψ hℓ hℓ1 hNℓ hψ hper
      have hp (X : Configuration N) :
          bellKernel s N ℓ ψ (blockLength X (k : ℤ) ((N : ℕ) - k)) =
            bellKernel s N ℓ ψ (blockLength X 0 k) := by
        have hc := bell_block_complement X 0 hkN'.le
        simp only [zero_add] at hc
        rw [hc, bellKernel_reflect s N N.pos ℓ ψ hper]
      have hd : bellKernel s N ℓ ψ (((N : ℕ) - k : ℕ) : ℝ) =
          bellKernel s N ℓ ψ (k : ℝ) := by
        rw [Nat.cast_sub hkN'.le, bellKernel_reflect s N N.pos ℓ ψ hper]
      simp only [hp, hd] at hshort
      exact hshort.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hf0 _)) hA)
  have hsum : (∑ k ∈ Finset.Icc 1 ((N : ℕ) - 1), f k) ≤ ∑' k, f k :=
    Summable.sum_le_tsum _ (fun k _ => hf0 k) hf
  calc _ ≤ ∑ k ∈ Finset.Icc 1 ((N : ℕ) - 1),
        C0 * bellConstant ℓ ψ * (f k + f ((N : ℕ) - k)) := Finset.sum_le_sum hb'
    _ = C0 * bellConstant ℓ ψ *
        ((∑ k ∈ Finset.Icc 1 ((N : ℕ) - 1), f k) +
          ∑ k ∈ Finset.Icc 1 ((N : ℕ) - 1), f ((N : ℕ) - k)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ = C0 * bellConstant ℓ ψ * (2 * ∑ k ∈ Finset.Icc 1 ((N : ℕ) - 1), f k) := by
        rw [bell_sum_complement]; ring
    _ ≤ C0 * bellConstant ℓ ψ * (2 * ∑' k, f k) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by norm_num)) hA
    _ ≤ (2 * C0 * (1 + ∑' k, f k)) * bellConstant ℓ ψ := by nlinarith

end Internal

end Riesz1

end
