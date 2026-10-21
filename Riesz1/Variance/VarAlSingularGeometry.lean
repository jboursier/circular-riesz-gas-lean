/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlSingularWeights
public import Riesz1.Variance.VarAlGapGeometry

/-!
# Label and spatial comparisons for the singular loop field

Proposition 5.9: the auxiliary integer labels represent
exactly the variance window and its cyclic label distances.
-/

@[expose] public section

noncomputable section

open Finset Set

namespace Riesz1

/-- The pinned label belongs to both kinds of window. -/
theorem varAlSingular_zero_mem (N : ℕ+) (ℓ γ : ℝ) (hK : 1 ≤ (N : ℝ) * ℓ) : (0 : ℤ) ∈ gradLabels N ℓ γ := by
  by_cases hp : GradPartial N ℓ γ
  · apply (mem_gradLabels_partial hp 0).2
    have h : 0 ≤ ⌊gradM N ℓ γ⌋ := Int.floor_nonneg.mpr (Real.rpow_nonneg (by linarith) _)
    omega
  · exact (mem_gradLabels_full hp 0).2 ⟨le_rfl, by exact_mod_cast N.pos⟩

/-- Cyclic distances agree after passing from an integer representative to its label. -/
theorem varAlSingular_distance_eq {N : ℕ+} {ℓ γ : ℝ} {j : ℤ}
    (hK : 1 ≤ (N : ℝ) * ℓ) (hj : j ∈ gradLabels N ℓ γ) :
    (gradLabelDist N 0 j : ℝ) = (labelDistToOne N (gradIndex N j) : ℝ) := by
  have hN : (0 : ℤ) < N := by exact_mod_cast N.pos
  have hjN := gradLabels_abs_sub_lt (varAlSingular_zero_mem N ℓ γ hK) hj
  simp only [sub_zero] at hjN
  have hjbounds := abs_lt.mp hjN
  have he : ((gradIndex N j).val : ℤ) = j % (N : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg j hN.ne')
  rw [gradLabelDist, sub_zero, labelDistToOne_eq, Nat.cast_min,
    Nat.cast_sub (Nat.le_of_lt (gradIndex N j).isLt)]
  have heR : ((gradIndex N j).val : ℝ) = ((j % (N : ℤ) : ℤ) : ℝ) := by exact_mod_cast he
  rw [heR]
  by_cases hj0 : 0 ≤ j
  · rw [Int.emod_eq_of_lt hj0 (by omega), abs_of_nonneg hj0]
    push_cast
    rfl
  · have hr : j % (N : ℤ) = j + N := by
      have hh : 0 ≤ j + (N : ℤ) ∧ j + (N : ℤ) < N := by omega
      have := Int.emod_eq_of_lt hh.1 hh.2
      rwa [Int.add_emod, Int.emod_self, add_zero, Int.emod_emod] at this
    rw [hr, abs_of_neg (by omega : j < 0)]
    push_cast
    have : (N : ℝ) - ((j : ℝ) + N) = -(j : ℝ) := by ring
    rw [this, min_comm]
    congr 1
    ring

/-- The spatial envelope on a good event is dominated by augmented comparison
weights, with exponent `3` chosen independently of epsilon. -/
theorem varAlSingular_spatial_bound {s b γ ε ℓ : ℝ} {N : ℕ+}
    (hs0 : 0 < s) (hs1 : s < 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hγ : 1 < γ) (hε : 0 < ε) (hεs : ε < (1 - s / 2) / 8)
    (hℓ : 0 < ℓ) (hK : 1 ≤ (N : ℝ) * ℓ) {X : Fin (N : ℕ) → ℝ}
    (hX : gradEvent s γ ε N ℓ X) (hX0 : X ⟨0, N.pos⟩ = 0)
    {j : ℤ} (hj : j ∈ gradLabels N ℓ γ) :
    ℓ⁻¹ * gradWeightTwo s b ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X j / ℓ) +
        (N : ℝ) * ((N : ℝ) * ℓ) ^ b /
          (1 + (N : ℝ) * circDist 1 (gradLift N X j)) ^ (1 + s / 2) ≤
      8 * ((N : ℝ) * ℓ) ^ (3 * ε) *
        ((N : ℝ) * augmentedComparisonWeight N ((N : ℝ) * ℓ) s b ε (gradIndex N j)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hzero : gradLift N X 0 = 0 := by
    simpa [gradLift, gradIndex] using hX0
  obtain ⟨hlo, hhi⟩ := gradient_splitting_comparison hs0 hγ hε hεs hK hX
    (varAlSingular_zero_mem N ℓ γ hK) hj
  rw [hzero, sub_zero, varAlSingular_distance_eq hK hj] at hlo hhi
  have hh := varAlSingular_weights (gradIndex N j) hK hs0 hs1 hb0 hb1 hε.le
    (mul_nonneg hN.le (circDist_nonneg _ _)) hlo hhi
  have hd : circDist ℓ⁻¹ (gradLift N X j / ℓ) =
      ((N : ℝ) * circDist 1 (gradLift N X j)) / ((N : ℝ) * ℓ) := by
    rw [show ℓ⁻¹ = 1 / ℓ by simp only [one_div], circDist_scale hℓ]
    field_simp
  have hmult := mul_le_mul_of_nonneg_left hh hN.le
  unfold gradWeightTwo
  rw [hd]
  convert hmult using 1 <;> field_simp

end Riesz1

end
