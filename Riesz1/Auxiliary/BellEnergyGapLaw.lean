/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.BellEnergyRotation
public import Riesz1.Auxiliary.BellRandomSumIntegrability

/-!
# Cyclic block laws in the averaged quadratic energy

The finite-coordinate consequences of the gap-law part of Lemma 4.2
used in the expectation identity of Lemma B.1.
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Riesz1

lemma bell_block_sum_fin {N : ℕ+} (X : Configuration N) (j : ℤ) (L : ℕ) :
    blockLength X j L = ∑ r : Fin L, gap X (j + (r : ℕ)) := by
  rw [blockLength_eq_sum]
  exact (Fin.sum_univ_eq_sum_range (fun r : ℕ => gap X (j + r)) L).symm

/-- Cyclic symmetry passes from the full gap vector to any consecutive block. -/
lemma bell_map_blockLength_add_one (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (j : ℤ) (L : ℕ) :
    (gibbsMeasure P N).map (fun X : Configuration N => blockLength X (j + 1) L) =
      (gibbsMeasure P N).map (fun X : Configuration N => blockLength X j L) := by
  let Sum : (Fin L → ℝ) → ℝ := fun v => ∑ r, v r
  have hSum : Measurable Sum := Finset.measurable_sum _ fun r _ => measurable_pi_apply r
  have h0 : Measurable (fun (X : Configuration N) (r : Fin L) => gap X (j + (r : ℕ))) :=
    Measurable.of_eval fun r => measurable_gap _
  have h1 : Measurable (fun (X : Configuration N) (r : Fin L) => gap X (j + (r : ℕ) + 1)) :=
    Measurable.of_eval fun r => measurable_gap _
  have hh := congrArg (Measure.map Sum)
    (map_gapFamily_add_one_gibbsMeasure P N hN (fun r : Fin L => j + (r : ℕ)))
  rw [Measure.map_map hSum h1, Measure.map_map hSum h0] at hh
  have he0 : Sum ∘ (fun (X : Configuration N) (r : Fin L) => gap X (j + (r : ℕ))) =
      (fun X : Configuration N => blockLength X j L) := by
    funext X
    exact (bell_block_sum_fin X j L).symm
  have he1 : Sum ∘ (fun (X : Configuration N) (r : Fin L) => gap X (j + (r : ℕ) + 1)) =
      (fun X : Configuration N => blockLength X (j + 1) L) := by
    funext X
    change (∑ r : Fin L, gap X (j + (r : ℕ) + 1)) = blockLength X (j + 1) L
    rw [bell_block_sum_fin]
    apply Finset.sum_congr rfl
    intro r hr
    congr 1
    ring
  rw [he0, he1] at hh
  exact hh

/-- Every natural starting label gives the same block law. -/
lemma bell_map_blockLength_nat (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i L : ℕ) :
    (gibbsMeasure P N).map (fun X : Configuration N => blockLength X (i : ℤ) L) =
      (gibbsMeasure P N).map (fun X : Configuration N => blockLength X 0 L) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simpa only [Nat.cast_add, Nat.cast_one] using
      (bell_map_blockLength_add_one P N hN (i : ℤ) L).trans ih

/-- Expectations of the scalar kernel do not depend on the starting label. -/
lemma integral_bellKernel_block_label (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (i L : ℕ) :
    (∫ X : Configuration N, bellKernel P.1.2 N ℓ ψ (blockLength X (i : ℤ) L)
      ∂gibbsMeasure P N) =
      ∫ X : Configuration N, bellKernel P.1.2 N ℓ ψ (blockLength X 0 L) ∂gibbsMeasure P N := by
  have hm := (measurable_bellKernel (s := P.1.2) (N := (N : ℕ)) hℓ hψ)
  rw [← integral_map (measurable_blockLength (i : ℤ) L).aemeasurable hm.aestronglyMeasurable,
    bell_map_blockLength_nat P N hN i L,
    integral_map (measurable_blockLength 0 L).aemeasurable hm.aestronglyMeasurable]

/-- Complementary block lengths have equal averaged-kernel expectations. -/
lemma integral_bellKernel_block_reflect (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hp : Function.Periodic ψ ℓ⁻¹) {k : ℕ} (hk : k ≤ (N : ℕ)) :
    (∫ X : Configuration N, bellKernel P.1.2 N ℓ ψ (blockLength X 0 ((N : ℕ) - k))
      ∂gibbsMeasure P N) =
      ∫ X : Configuration N, bellKernel P.1.2 N ℓ ψ (blockLength X 0 k) ∂gibbsMeasure P N := by
  rw [← integral_bellKernel_block_label P N hN hℓ hψ k ((N : ℕ) - k)]
  apply integral_congr_ae
  exact ae_of_all _ fun X => by
    change bellKernel P.1.2 N ℓ ψ (blockLength X (k : ℤ) ((N : ℕ) - k)) =
      bellKernel P.1.2 N ℓ ψ (blockLength X 0 k)
    have hh := bell_block_complement X 0 hk
    simp only [zero_add] at hh
    rw [hh, bellKernel_reflect P.1.2 N N.pos ℓ ψ hp]

end Riesz1

end
