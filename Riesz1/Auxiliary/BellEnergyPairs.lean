/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.BellEnergyGapLaw
public import Riesz1.ToMathlib.CyclicPairSum

/-!
# Counting the averaged particle pairs

The particle-particle term in Lemma B.1: cyclic invariance gives
one copy of every nonzero microscopic displacement for each starting particle.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

lemma bellKernel_zero (s : ℝ) (N : ℕ) (ℓ : ℝ) (ψ : ℝ → ℝ) :
    bellKernel s N ℓ ψ 0 = 0 := by
  simp [bellKernel, bellIncrement]

/-- Both orientations of a pair are encoded by subtraction in the cyclic label group. -/
theorem integral_bellPair_cyclic (P : Parameters) (hPL : External.PrekopaLeindler)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) (i j : Fin (N : ℕ)) :
    (∫ X : Configuration N, (N : ℝ) ^ (-P.1.2) *
      bellPairKernel P.1.2 (loopScaleField ℓ.val ψ.val) (X.val i) (X.val j) ∂gibbsMeasure P N) =
      ∫ X : Configuration N, bellKernel P.1.2 N ℓ.val ψ.val
        (blockLength X 0 ((j - i).val)) ∂gibbsMeasure P N := by
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [Fin.sub_val_of_le hij.le,
      integral_bellPair_eq_integral_bellKernel P hPL N ℓ ψ hψ i j hij,
      integral_bellKernel_block_label P N hN ℓ.2.1 hψ]
  · subst j
    simp [bellPairKernel_diag, blockLength, bellKernel_zero]
  · have hv : (j - i).val = (N : ℕ) - ((i : ℕ) - (j : ℕ)) := by
      rw [Fin.val_sub, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
      have := i.isLt
      omega
    rw [hv, integral_bellKernel_block_reflect P N hN ℓ.2.1 hψ ψ.2.1 (by omega),
      ← integral_bellKernel_block_label P N hN ℓ.2.1 hψ (j : ℕ)]
    have he : (fun X : Configuration N => (N : ℝ) ^ (-P.1.2) *
        bellPairKernel P.1.2 (loopScaleField ℓ.val ψ.val) (X.val i) (X.val j)) =
        (fun X : Configuration N => (N : ℝ) ^ (-P.1.2) *
        bellPairKernel P.1.2 (loopScaleField ℓ.val ψ.val) (X.val j) (X.val i)) := by
      funext X
      rw [bellPairKernel_symm]
    rw [he]
    exact integral_bellPair_eq_integral_bellKernel P hPL N ℓ ψ hψ j i hij

/-- The complete particle sum is `N` times the sum over nonzero block lengths. -/
theorem integral_bell_particle_sum (P : Parameters) (hPL : External.PrekopaLeindler)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) :
    (∫ X : Configuration N, (N : ℝ) ^ (-P.1.2) *
      (∑ p ∈ (Finset.univ : Finset (Fin (N : ℕ))).offDiag,
        bellPairKernel P.1.2 (loopScaleField ℓ.val ψ.val) (X.val p.1) (X.val p.2))
        ∂gibbsMeasure P N) =
      (N : ℝ) * ∑ k ∈ Finset.Icc 1 ((N : ℕ) - 1),
        ∫ X : Configuration N, bellKernel P.1.2 N ℓ.val ψ.val (blockLength X 0 k)
          ∂gibbsMeasure P N := by
  let Q (k : ℕ) := ∫ X : Configuration N,
    bellKernel P.1.2 N ℓ.val ψ.val (blockLength X 0 k) ∂gibbsMeasure P N
  have hQ : Q 0 = 0 := by simp [Q, blockLength, bellKernel_zero]
  have hs : (∑ k : Fin (N : ℕ), Q k.val) = ∑ k ∈ Finset.Icc 1 ((N : ℕ) - 1), Q k := by
    rw [Fin.sum_univ_eq_sum_range]
    symm
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
      omega
    · intro k hk hn
      have hk0 : k = 0 := by
        simp only [Finset.mem_Icc, Finset.mem_range] at hk hn
        omega
      simpa only [hk0] using hQ
  obtain ⟨M, hf⟩ := loopScaleField_lipschitz ψ
  have hp := loopScaleField_periodic ψ.2.1
  have hi (p : Fin (N : ℕ) × Fin (N : ℕ))
      (hp' : p ∈ (Finset.univ : Finset (Fin (N : ℕ))).offDiag) :
      Integrable (fun X : Configuration N => (N : ℝ) ^ (-P.1.2) *
        bellPairKernel P.1.2 (loopScaleField ℓ.val ψ.val) (X.val p.1) (X.val p.2))
        (gibbsMeasure P N) :=
    (bellPair_particle_integrable P hPL N hf hp p.1 p.2
      (Finset.mem_offDiag.mp hp').2.2).const_mul _
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ hi, ← Finset.mul_sum]
  rw [sum_offDiag_eq_card_mul_sum
    (fun i j : Fin (N : ℕ) => ∫ X : Configuration N, (N : ℝ) ^ (-P.1.2) *
      bellPairKernel P.1.2 (loopScaleField ℓ.val ψ.val) (X.val i) (X.val j) ∂gibbsMeasure P N)
    (fun k : Fin (N : ℕ) => Q k.val) hQ
    (integral_bellPair_cyclic P hPL N hN ℓ ψ hψ)]
  simp only [Fintype.card_fin, hs, Q]

/-- Particle-pair averaging also includes the empty sum at `N = 1`. -/
theorem integral_bell_particle_sum_all (P : Parameters) (hPL : External.PrekopaLeindler)
    (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) :
    (∫ X : Configuration N, (N : ℝ) ^ (-P.1.2) *
      (∑ p ∈ (Finset.univ : Finset (Fin (N : ℕ))).offDiag,
        bellPairKernel P.1.2 (loopScaleField ℓ.val ψ.val) (X.val p.1) (X.val p.2))
        ∂gibbsMeasure P N) =
      (N : ℝ) * ∑ k ∈ Finset.Icc 1 ((N : ℕ) - 1),
        ∫ X : Configuration N, bellKernel P.1.2 N ℓ.val ψ.val (blockLength X 0 k)
          ∂gibbsMeasure P N := by
  by_cases hN : 2 ≤ (N : ℕ)
  · exact integral_bell_particle_sum P hPL N hN ℓ ψ hψ
  · have hN1 : (N : ℕ) = 1 := by have := N.pos; omega
    have he : (Finset.univ : Finset (Fin (N : ℕ))).offDiag = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hne := (Finset.mem_offDiag.mp hp).2.2
      apply hne
      apply Fin.ext
      have := p.1.isLt
      have := p.2.isLt
      omega
    simp only [he, Finset.sum_empty, mul_zero, integral_zero, hN1, Nat.sub_self]
    simp

end Riesz1

end
