/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingQuadratureGeometry
public import Riesz1.Auxiliary.GradientSplittingQuadratureFull

/-!
# Partial-window reference sums and their cells

The quadrature part of Lemma 5.7. Reindexing a partial window gives exactly
the increments `[-n-i,n-i]`, with zero omitted. The cells tile `[-n-i-1/2,n-i+1/2]`.
The remainder quadrature on that interval is bounded by the one-cell estimates.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- Partial-window sums reindexed by their signed increments. -/
theorem sum_labels_erase_partial {N : ℕ+} {ℓ γ : ℝ} (hP : GradPartial N ℓ γ)
    (i : ℤ) (f : ℤ → ℝ) :
    ∑ j ∈ (gradLabels N ℓ γ).erase i, f (gradPathIncr N ℓ γ i j) =
      ∑ k ∈ (Finset.Icc (-⌊gradM N ℓ γ⌋ - i) (⌊gradM N ℓ γ⌋ - i)).erase 0, f k := by
  classical
  simp only [gradLabels, gradPathIncr, hP, ↓reduceIte]
  apply Finset.sum_bij (fun j _ => j - i)
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_Icc] at hj ⊢
    constructor
    · omega
    · constructor <;> omega
  · intro j hj k hk he
    omega
  · intro k hk
    simp only [Finset.mem_erase, Finset.mem_Icc] at hk
    refine ⟨k + i, ?_, by ring⟩
    simp only [Finset.mem_erase, Finset.mem_Icc]
    constructor
    · omega
    · constructor <;> omega
  · intro j hj
    rfl

/-- The partial-window cells lie strictly inside `[-N/2,N/2]`. -/
lemma gradPartial_cells_range {N : ℕ+} {ℓ γ : ℝ} (hP : GradPartial N ℓ γ)
    (hM : 1 ≤ gradM N ℓ γ) {i : ℤ} (hi : i ∈ gradLabels N ℓ γ) :
    -(N : ℝ) / 2 ≤ -(⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) - 1 / 2 ∧
      (⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) + 1 / 2 ≤ (N : ℝ) / 2 := by
  have hi' := (mem_gradLabels_partial hP i).mp hi
  have hiR : -(⌊gradM N ℓ γ⌋ : ℝ) ≤ (i : ℝ) ∧
      (i : ℝ) ≤ (⌊gradM N ℓ γ⌋ : ℝ) := by exact_mod_cast hi'
  have hf := Int.floor_le (gradM N ℓ γ)
  constructor <;> linarith [hP]

/-- Unit cells on the shifted partial window tile its reference interval. -/
lemma integral_gradCellR_partial_cells {s α ℓ γ C0 x : ℝ} {N : ℕ+} {ψ : ℝ → ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hα0 : s - 1 ≤ α) (hα1 : α < s / 2)
    (hN : 2 ≤ (N : ℕ)) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hK : 1 ≤ (N : ℝ) * ℓ)
    (hγ : 0 ≤ γ) (hP : GradPartial N ℓ γ) (hC0 : 0 ≤ C0) (hψ : ContDiff ℝ ∞ ψ)
    (hper : Function.Periodic ψ ℓ⁻¹)
    (h1 : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t)
    (h2 : ∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t)
    {i : ℤ} (hi : i ∈ gradLabels N ℓ γ) :
    ∑ k ∈ Finset.Icc (-⌊gradM N ℓ γ⌋ - i) (⌊gradM N ℓ γ⌋ - i),
        ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), gradCellR s (N : ℕ) ℓ ψ x v
      = ∫ v in (-(⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) - 1 / 2)..
          ((⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) + 1 / 2), gradCellR s (N : ℕ) ℓ ψ x v := by
  have hM : 1 ≤ gradM N ℓ γ := Real.one_le_rpow hK hγ
  have hn : (0 : ℤ) ≤ ⌊gradM N ℓ γ⌋ := Int.floor_nonneg.mpr (by linarith)
  have hhalf := intervalIntegrable_gradCellR_half hs0 hs1 hα0 hα1 hN hℓ hℓ1 hK hC0 hψ hper h1 h2
    (x := x)
  rw [← neg_div] at hhalf
  have hrange := gradPartial_cells_range hP hM hi
  have hiR : -(⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) - 1 / 2 ≤
      (⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) + 1 / 2 := by
    have : (0 : ℝ) ≤ (⌊gradM N ℓ γ⌋ : ℝ) := by exact_mod_cast hn
    linarith
  have hNR : (0 : ℝ) ≤ N := by positivity
  have hI := intervalIntegrable_of_le_of_le (by linarith : -(N : ℝ) / 2 ≤ (N : ℝ) / 2)
    hhalf hrange.1 hiR hrange.2
  have ht := sum_Ico_unitCell_integral (f := gradCellR s (N : ℕ) ℓ ψ x)
    (a := -⌊gradM N ℓ γ⌋ - i)
    (b := ⌊gradM N ℓ γ⌋ - i + 1) (by omega) (by convert hI using 1 <;> push_cast <;> ring)
  have heq : Finset.Ico (-⌊gradM N ℓ γ⌋ - i) (⌊gradM N ℓ γ⌋ - i + 1) =
      Finset.Icc (-⌊gradM N ℓ γ⌋ - i) (⌊gradM N ℓ γ⌋ - i) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [heq] at ht
  convert ht using 1
  congr 1 <;> push_cast <;> ring

/-- Remainder quadrature on the reference cells. Boundary strips are deliberately absent
from this internal estimate. Its interval is exactly the union of the cells. -/
theorem gradPartial_remainder_cell_error {s α : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα0 : s - 1 ≤ α) (hα1 : α < s / 2) :
    ∃ Cc Cd : ℝ, 0 < Cc ∧ 0 < Cd ∧
    ∀ (N : ℕ+) (ℓ γ C0 x : ℝ) (ψ : ℝ → ℝ) (i : ℤ),
      2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → 0 ≤ γ → GradPartial N ℓ γ →
      0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      i ∈ gradLabels N ℓ γ →
      |(∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradCellR s (N : ℕ) ℓ ψ x (gradPathIncr N ℓ γ i j))
        - ∫ v in (-(⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) - 1 / 2)..
            ((⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) + 1 / 2), gradCellR s (N : ℕ) ℓ ψ x v|
        ≤ (∑ j ∈ (gradLabels N ℓ γ).erase i,
            gradQuadCell s (1 - s + α) (N : ℕ) ℓ Cd C0 x (gradPathIncr N ℓ γ i j))
          + Cc * C0 * ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) := by
  classical
  obtain ⟨Cc, hCc, hcells⟩ := gradient_splitting_cells hs0 hs1 hα0 hα1
  obtain ⟨Cd, hCd, hder⟩ := cell_abs_deriv_integral_le hs0 hs1 hα0 hα1
  refine ⟨Cc, Cd, hCc, hCd, ?_⟩
  intro N ℓ γ C0 x ψ i hN hℓ hℓ1 hK hγ hP hC0 hψ hper h1 h2 hi
  have hcell0 := (hcells (N : ℕ) ℓ C0 x ψ hN hℓ hℓ1 hK hC0 hψ hper h1 h2).2.2.2.2.1
  have ht := integral_gradCellR_partial_cells hs0 hs1 hα0 hα1 hN hℓ hℓ1 hK hγ hP
    hC0 hψ hper h1 h2 hi (x := x)
  let T := Finset.Icc (-⌊gradM N ℓ γ⌋ - i) (⌊gradM N ℓ γ⌋ - i)
  have hi' := (mem_gradLabels_partial hP i).mp hi
  have hz : (0 : ℤ) ∈ T := by
    simp only [T, Finset.mem_Icc]
    omega
  have hsplit : (∑ k ∈ T, ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2),
      gradCellR s (N : ℕ) ℓ ψ x v) =
      (∑ k ∈ T.erase 0, ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2),
        gradCellR s (N : ℕ) ℓ ψ x v) + ∫ v in (-1 / 2 : ℝ)..(1 / 2),
          gradCellR s (N : ℕ) ℓ ψ x v := by
    simpa only [Int.cast_zero, zero_sub, zero_add, neg_div] using
      (Finset.sum_erase_add T (fun k : ℤ => ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2),
      gradCellR s (N : ℕ) ℓ ψ x v) hz).symm
  have hsum := sum_labels_erase_partial hP i
    (fun k : ℤ => ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), gradCellR s (N : ℕ) ℓ ψ x v)
  have hI : (∫ v in (-(⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) - 1 / 2)..
      ((⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) + 1 / 2), gradCellR s (N : ℕ) ℓ ψ x v) =
      (∑ j ∈ (gradLabels N ℓ γ).erase i,
        ∫ v in ((gradPathIncr N ℓ γ i j : ℝ) - 1 / 2)..
          ((gradPathIncr N ℓ γ i j : ℝ) + 1 / 2), gradCellR s (N : ℕ) ℓ ψ x v)
        + ∫ v in (-1 / 2 : ℝ)..(1 / 2), gradCellR s (N : ℕ) ℓ ψ x v := by
    rw [← ht, hsum]
    exact hsplit
  rw [hI, show ∀ A B C : ℝ, A - (B + C) = (A - B) - C by intros; ring,
    ← Finset.sum_sub_distrib]
  have hcen : |∫ v in (-1 / 2 : ℝ)..(1 / 2), gradCellR s (N : ℕ) ℓ ψ x v| ≤
      Cc * C0 * ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) := by
    have hb := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
      (f := gradCellR s (N : ℕ) ℓ ψ x) (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)
    exact hb.trans (by simpa only [neg_div] using hcell0)
  refine (abs_sub _ _).trans (add_le_add ?_ hcen)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro j hj
  obtain ⟨hne, hjl⟩ := Finset.mem_erase.mp hj
  have hk0 := gradPathIncr_ne_zero hi hjl hne
  have hkN := two_abs_gradPathIncr_le hi hjl
  have hk1 : 1 ≤ |(gradPathIncr N ℓ γ i j : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hk0
  have hkNr : |(gradPathIncr N ℓ γ i j : ℝ)| ≤ (N : ℝ) / 2 := by
    have : (2 : ℝ) * |(gradPathIncr N ℓ γ i j : ℝ)| ≤ (N : ℝ) := by exact_mod_cast hkN
    linarith
  refine (gradCell_cell_difference hs0 hs1 hψ hℓ (N : ℕ) hN x _ (by linarith) hkNr).trans ?_
  exact hder (N : ℕ) ℓ C0 x ψ _ hN hℓ hℓ1 hK hC0 hψ hper h1 h2 hk1 hkNr

end

end Riesz1
