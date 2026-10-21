/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingQuadratureCells
public import Riesz1.Auxiliary.GradientSplittingQuadratureLabels
public import Riesz1.Auxiliary.GradientSplittingConvolutionLattice
public import Riesz1.Auxiliary.GradientSplittingDisplacement

/-!
# Weight sums over a full window

The quadrature part of Lemma 5.7, full window. The cell bounds
of `GradientSplittingQuadratureCells` give, for each label `j ≠ i`, a bound of the cell integral
`∫_{cell k_{ij}} |R_x'|` by a weight `gradQuadCell`. This module sums that weight over the labels
`j ≠ i` of a full window:

* the sum of `|k_{ij}|^{-1-s}` is bounded by the decay sum `sum_labels_decay_le`.
* the sum of `w_2((x + k_{ij}/N)/ℓ) |k_{ij}|^{-1-s}` is bounded by the lattice sum
  `gradient_splitting_lattice_sum_three`, after reindexing by the residues `(j - i) mod N`.
-/

@[expose] public section

open Set MeasureTheory Finset
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The weight of the cell bound at the label increment `k` (quadrature part of Lemma 5.7):
`C₁ C_0 ℓ^{-1} (w_2(x/ℓ) + w_2((x + k/N)/ℓ)) |k|^{-1-s}`,
with `w_2` the weight of the data part of Lemma 5.7 on `ℓ^{-1} 𝕋` and the parameter `Nℓ`. -/
def gradQuadCell (s a : ℝ) (N : ℕ) (ℓ C₁ C0 x : ℝ) (k : ℤ) : ℝ :=
  C₁ * C0 * ℓ⁻¹ * (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
    + gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + (k : ℝ) / N) / ℓ)) * |(k : ℝ)| ^ (-1 - s)

/-- For `|k| ≥ 1`, `|k|^{-1-s} ≤ 2^{1+s} (1 + |k|)^{-(1+s/2)}`. -/
lemma rpow_abs_le_two_pow_mul_one_add {s : ℝ} (hs0 : 0 < s) {y : ℝ} (hy : 1 ≤ |y|) :
    |y| ^ (-1 - s) ≤ 2 ^ (1 + s) * (1 + |y|) ^ (-(1 + s / 2)) := by
  have hpos : (0 : ℝ) < (1 + |y|) / 2 := by
    have := abs_nonneg y
    linarith
  have hle : (1 + |y|) / 2 ≤ |y| := by linarith
  have h1 : |y| ^ (-1 - s) ≤ ((1 + |y|) / 2) ^ (-1 - s) :=
    Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
  have h2' : (2 : ℝ) ^ (-1 - s) = ((2 : ℝ) ^ (1 + s))⁻¹ := by
    rw [show (-1 - s) = -(1 + s) by ring, Real.rpow_neg (by norm_num)]
  have h2 : ((1 + |y|) / 2) ^ (-1 - s) = 2 ^ (1 + s) * (1 + |y|) ^ (-1 - s) := by
    rw [Real.div_rpow (by linarith [abs_nonneg y]) (by norm_num), h2', div_inv_eq_mul]
    ring
  have h3 : (1 + |y|) ^ (-1 - s) ≤ (1 + |y|) ^ (-(1 + s / 2)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y]) (by linarith)
  have h4 : 0 ≤ (2 : ℝ) ^ (1 + s) := by positivity
  nlinarith

/-- The decay of the weights `|k_{ij}|^{-1-s}` over the labels `j ≠ i` of a full window. -/
lemma sum_erase_abs_pow_le {s : ℝ} (hs0 : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ : ℝ) (i : ℤ), 2 ≤ (N : ℕ) →
      ¬GradPartial N ℓ γ → i ∈ gradLabels N ℓ γ →
      ∑ j ∈ (gradLabels N ℓ γ).erase i, |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ^ (-1 - s) ≤ C := by
  obtain ⟨C, hC, hdec⟩ := sum_labels_decay_le hs0
  refine ⟨2 ^ (1 + s) * C, by positivity, ?_⟩
  intro N ℓ γ i hN hP hi
  have hsum := hdec N ℓ γ i hN hi
  calc ∑ j ∈ (gradLabels N ℓ γ).erase i, |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ^ (-1 - s)
      ≤ ∑ j ∈ (gradLabels N ℓ γ).erase i,
          2 ^ (1 + s) * (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2)) := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hne, hjl⟩ := Finset.mem_erase.mp hj
        have hk1 : 1 ≤ |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| := by
          have hne0 := gradPathIncr_ne_zero hi hjl hne
          have h1 : (1 : ℤ) ≤ |(gradPathIncr N ℓ γ i j : ℤ)| := by
            have := abs_pos.mpr hne0
            omega
          have h2 : ((1 : ℤ) : ℝ) ≤ ((|(gradPathIncr N ℓ γ i j : ℤ)| : ℤ) : ℝ) := by
            exact_mod_cast h1
          rw [Int.cast_abs] at h2
          simpa using h2
        have hval := rpow_abs_le_two_pow_mul_one_add hs0 (y := ((gradPathIncr N ℓ γ i j : ℤ) : ℝ)) hk1
        have habs : |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| = (gradLabelDist N i j : ℝ) := by
          rw [← Int.cast_abs, abs_gradPathIncr_eq hi hjl]
        rw [habs] at hval ⊢
        exact hval
    _ = 2 ^ (1 + s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
          (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2)) := by
        rw [Finset.mul_sum]
    _ ≤ 2 ^ (1 + s) * C := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun j hj _ => ?_)).trans hsum
        have h0 := gradLabelDist_nonneg (N := N) (i := i) (j := j) (gradLabels_abs_sub_lt hi hj)
        have h0' : (0 : ℝ) ≤ (gradLabelDist N i j : ℝ) := by exact_mod_cast h0
        exact Real.rpow_nonneg (by linarith) _

/-- One label of the full window: the weight `w_2` at the path increment, times `|k|^{-1-s}`, is at
most `2^{1+s}` times the lattice term at the residue `r = (j - i) mod N`. The weight `w_2` is
periodic with period `N` in the microscopic variable, and `|k| = circDist N r`. -/
lemma gradPathIncr_weight_le {s a : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {ℓ γ : ℝ} {N : ℕ+} (hP : ¬GradPartial N ℓ γ) (hℓ : 0 < ℓ) {i j : ℤ}
    (hi : i ∈ gradLabels N ℓ γ) (hjl : j ∈ gradLabels N ℓ γ) (hne : j ≠ i) (z : ℝ) :
    gradWeightTwo s a ((N : ℝ) * ℓ) ((N : ℝ) / ((N : ℝ) * ℓ)) ((z + ((gradPathIncr N ℓ γ i j : ℤ) : ℝ))
        / ((N : ℝ) * ℓ))
      * |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ^ (-1 - s)
    ≤ 2 ^ (1 + s) * (gradWeightTwo s a ((N : ℝ) * ℓ) ((N : ℝ) / ((N : ℝ) * ℓ))
        ((z + ((((j - i) % ((N : ℕ) : ℤ)).toNat : ℕ) : ℝ)) / ((N : ℝ) * ℓ))
      / (1 + circDist (N : ℝ) (((((j - i) % ((N : ℕ) : ℤ)).toNat : ℕ)) : ℝ)) ^ (1 + s / 2)) := by
  have hn : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hK : 0 < (N : ℝ) * ℓ := mul_pos hNR hℓ
  have hL : 0 < (N : ℝ) / ((N : ℝ) * ℓ) := div_pos hNR hK
  obtain ⟨hi0, hiN⟩ := (mem_gradLabels_full_iff hP i).mp hi
  obtain ⟨hj0, hjN⟩ := (mem_gradLabels_full_iff hP j).mp hjl
  obtain ⟨hr0, _⟩ := emod_sub_pos_of_ne hn hi0 hiN hj0 hjN hne
  obtain ⟨m, hm⟩ := gradPathIncr_emod N ℓ γ i j
  have hk2 := two_abs_gradPathIncr_le hi hjl
  have hk0 := gradPathIncr_ne_zero hi hjl hne
  -- the residue as a natural number, and its real value
  set rZ : ℤ := (j - i) % ((N : ℕ) : ℤ) with hrZdef
  set r : ℕ := rZ.toNat with hrdef
  have hrZ : ((r : ℕ) : ℤ) = rZ := Int.toNat_of_nonneg hr0.le
  have hrR : (r : ℝ) = (rZ : ℝ) := by
    have := congrArg (Int.cast (R := ℝ)) hrZ
    push_cast at this
    exact this
  set k : ℤ := gradPathIncr N ℓ γ i j with hkdef
  have hkR : (k : ℝ) = (r : ℝ) + (m : ℝ) * (N : ℝ) := by
    rw [hrR]
    have := congrArg (Int.cast (R := ℝ)) hm
    push_cast at this
    rw [this]
    ring
  -- the circle distance of the residue is the length of the increment
  have hcirc : circDist (N : ℝ) (r : ℝ) = |(k : ℝ)| := by
    have hk2R : 2 * |(k : ℝ)| ≤ (N : ℝ) := by
      have h : ((2 * |k| : ℤ) : ℝ) ≤ (((N : ℕ) : ℤ) : ℝ) := by exact_mod_cast hk2
      push_cast at h
      linarith
    have hcd : circDist (N : ℝ) (k : ℝ) = |(k : ℝ)| := by
      rcases lt_or_gt_of_ne (show (k : ℝ) ≠ 0 from by exact_mod_cast hk0) with hneg | hpos
      · have hkn : (-(k : ℝ)) ≥ 0 := by linarith
        have := circDist_neg_of_mem_Icc hNR hkn (by linarith [abs_nonneg (k : ℝ), abs_of_neg hneg])
        rw [neg_neg] at this
        rw [this, abs_of_neg hneg]
      · rw [circDist_of_mem_Icc hNR hpos.le (by linarith [abs_of_pos hpos]), abs_of_pos hpos]
    rw [← hcd, hkR, circDist_add_int_mul hNR (r : ℝ) m]
  -- the weight at the increment equals the weight at the residue
  have hw : gradWeightTwo s a ((N : ℝ) * ℓ) ((N : ℝ) / ((N : ℝ) * ℓ))
        ((z + (k : ℝ)) / ((N : ℝ) * ℓ))
      = gradWeightTwo s a ((N : ℝ) * ℓ) ((N : ℝ) / ((N : ℝ) * ℓ))
        ((z + (r : ℝ)) / ((N : ℝ) * ℓ)) := by
    apply gradWeightTwo_congr
    have hshift : (z + (k : ℝ)) / ((N : ℝ) * ℓ)
        = (z + (r : ℝ)) / ((N : ℝ) * ℓ) + (m : ℝ) * ((N : ℝ) / ((N : ℝ) * ℓ)) := by
      rw [hkR]
      field_simp
      ring
    rw [hshift, circDist_add_int_mul hL]
  -- the power comparison at `|k| ≥ 1`
  have hk1 : 1 ≤ |(k : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |k| := by
      have := abs_pos.mpr hk0
      omega
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast h1
    rw [Int.cast_abs] at h2
    simpa using h2
  have hpow := rpow_abs_le_two_pow_mul_one_add hs0 (y := (k : ℝ)) hk1
  have hwnn : 0 ≤ gradWeightTwo s a ((N : ℝ) * ℓ) ((N : ℝ) / ((N : ℝ) * ℓ))
        ((z + (k : ℝ)) / ((N : ℝ) * ℓ)) :=
    gradWeightTwo_nonneg_unconditional _ _ _ _ _
  rw [hw] at hwnn ⊢
  calc gradWeightTwo s a ((N : ℝ) * ℓ) ((N : ℝ) / ((N : ℝ) * ℓ))
          ((z + (r : ℝ)) / ((N : ℝ) * ℓ)) * |(k : ℝ)| ^ (-1 - s)
      ≤ gradWeightTwo s a ((N : ℝ) * ℓ) ((N : ℝ) / ((N : ℝ) * ℓ))
          ((z + (r : ℝ)) / ((N : ℝ) * ℓ)) * (2 ^ (1 + s) * (1 + |(k : ℝ)|) ^ (-(1 + s / 2))) :=
        mul_le_mul_of_nonneg_left hpow hwnn
    _ = 2 ^ (1 + s) * (gradWeightTwo s a ((N : ℝ) * ℓ) ((N : ℝ) / ((N : ℝ) * ℓ))
          ((z + (r : ℝ)) / ((N : ℝ) * ℓ)) / (1 + circDist (N : ℝ) (r : ℝ)) ^ (1 + s / 2)) := by
        rw [hcirc, Real.rpow_neg (by linarith [abs_nonneg (k : ℝ)])]
        ring

/-- The weights over the labels `j ≠ i` of a full window, summed: the lattice bound of
the convolution part of Lemma 5.7 (third claim) after the reindexing by residues. -/
theorem full_sum_erase_weight_le {s a : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a)
    (ha1 : a < 1 - s / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ x : ℝ) (i : ℤ), 2 ≤ (N : ℕ) → ¬GradPartial N ℓ γ →
      0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → i ∈ gradLabels N ℓ γ →
      ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradWeightTwo s a ((N : ℝ) * ℓ) ((N : ℝ) / ((N : ℝ) * ℓ))
              (((N : ℝ) * x + ((gradPathIncr N ℓ γ i j : ℤ) : ℝ)) / ((N : ℝ) * ℓ))
            * |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ^ (-1 - s)
        ≤ C * (1 + Real.log ((N : ℝ) * ℓ)) *
          (gradWeightTwo s a ((N : ℝ) * ℓ) ((N : ℝ) / ((N : ℝ) * ℓ))
              (((N : ℝ) * x) / ((N : ℝ) * ℓ))
            + ((N : ℝ) * ℓ) ^ (1 + a) / (1 + circDist (N : ℝ) ((N : ℝ) * x)) ^ (1 + s / 2)) := by
  obtain ⟨C₀, hC₀, hlat⟩ := gradient_splitting_lattice_sum_three hs0 hs1 ha0 ha1
  refine ⟨2 ^ (1 + s) * C₀, by positivity, ?_⟩
  intro N ℓ γ x i hN hP hℓ hℓ1 hK1 hi
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hK : (0 : ℝ) < (N : ℝ) * ℓ := mul_pos hNR hℓ
  set z : ℝ := (N : ℝ) * x with hzdef
  set G : ℕ → ℝ := fun r => gradWeightTwo s a ((N : ℝ) * ℓ) ((N : ℝ) / ((N : ℝ) * ℓ))
      ((z + (r : ℝ)) / ((N : ℝ) * ℓ)) / (1 + circDist (N : ℝ) (r : ℝ)) ^ (1 + s / 2) with hGdef
  have hG : ∀ r, 0 ≤ G r := by
    intro r
    have hc := gradCell_circDist_nonneg (N : ℝ) (r : ℝ)
    exact div_nonneg (gradWeightTwo_nonneg_unconditional _ _ _ _ _)
      (Real.rpow_nonneg (by linarith) _)
  have hKN : (N : ℝ) * ℓ ≤ (N : ℝ) := by nlinarith
  have hlatN := hlat (N : ℕ) ((N : ℝ) * ℓ) z hN hK1 hKN
  calc ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradWeightTwo s a ((N : ℝ) * ℓ) ((N : ℝ) / ((N : ℝ) * ℓ))
              (((N : ℝ) * x + ((gradPathIncr N ℓ γ i j : ℤ) : ℝ)) / ((N : ℝ) * ℓ))
            * |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ^ (-1 - s)
      ≤ ∑ j ∈ (gradLabels N ℓ γ).erase i,
          2 ^ (1 + s) * G (((j - i) % ((N : ℕ) : ℤ)).toNat) := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hne, hjl⟩ := Finset.mem_erase.mp hj
        exact gradPathIncr_weight_le hs0 hs1 hP hℓ hi hjl hne z
    _ = 2 ^ (1 + s) * ∑ j ∈ (gradLabels N ℓ γ).erase i, G (((j - i) % ((N : ℕ) : ℤ)).toNat) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ 2 ^ (1 + s) * ∑ r ∈ Finset.range (N : ℕ), G r :=
        mul_le_mul_of_nonneg_left (sum_erase_residue_le hP hi G hG) (by positivity)
    _ ≤ 2 ^ (1 + s) * (C₀ * (1 + Real.log ((N : ℝ) * ℓ)) *
          (gradWeightTwo s a ((N : ℝ) * ℓ) ((N : ℝ) / ((N : ℝ) * ℓ)) (z / ((N : ℝ) * ℓ))
            + ((N : ℝ) * ℓ) ^ (1 + a) / (1 + circDist (N : ℝ) z) ^ (1 + s / 2))) :=
        mul_le_mul_of_nonneg_left hlatN (by positivity)
    _ = 2 ^ (1 + s) * C₀ * (1 + Real.log ((N : ℝ) * ℓ)) *
          (gradWeightTwo s a ((N : ℝ) * ℓ) ((N : ℝ) / ((N : ℝ) * ℓ))
              (((N : ℝ) * x) / ((N : ℝ) * ℓ))
            + ((N : ℝ) * ℓ) ^ (1 + a) / (1 + circDist (N : ℝ) ((N : ℝ) * x)) ^ (1 + s / 2)) := by
        rw [hzdef]
        ring

/-- The weight of the cell bound in the variable `ℓ^{-1}` and the lattice form: the two
parametrisations `((x + k/N)/ℓ)` with `L = ℓ^{-1}`, and `((Nx + k)/(Nℓ))` with `L = N/(Nℓ)`, agree. -/
lemma gradWeightTwo_cell_eq (s a : ℝ) {N ℓ x : ℝ} (hN : N ≠ 0) (hℓ : ℓ ≠ 0) (k : ℝ) :
    gradWeightTwo s a (N * ℓ) ℓ⁻¹ ((x + k / N) / ℓ)
      = gradWeightTwo s a (N * ℓ) (N / (N * ℓ)) ((N * x + k) / (N * ℓ)) := by
  have h1 : ℓ⁻¹ = N / (N * ℓ) := by
    field_simp
  have h2 : (x + k / N) / ℓ = (N * x + k) / (N * ℓ) := by
    field_simp
  rw [h1, h2]

/-- Summing the cell weights `gradQuadCell` over the labels `j ≠ i` of a full window: the
decay bound for `∑ |k_{ij}|^{-1-s}` and the lattice bound for the weighted sum, with the factor
`ℓ^{-1} (Nℓ)^{1+a} = N (Nℓ)^a`. -/
theorem sum_erase_gradQuadCell_le {s a : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a)
    (ha1 : a < 1 - s / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ x C₁ C0 : ℝ) (i : ℤ), 2 ≤ (N : ℕ) → ¬GradPartial N ℓ γ →
      0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → 0 ≤ C₁ → 0 ≤ C0 → i ∈ gradLabels N ℓ γ →
      ∑ j ∈ (gradLabels N ℓ γ).erase i, gradQuadCell s a (N : ℕ) ℓ C₁ C0 x
          (gradPathIncr N ℓ γ i j)
        ≤ C * C₁ * C0 * (1 + Real.log ((N : ℝ) * ℓ)) *
          (ℓ⁻¹ * gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
            + (N : ℝ) * ((N : ℝ) * ℓ) ^ a / (1 + circDist (N : ℝ) ((N : ℝ) * x)) ^ (1 + s / 2)) := by
  obtain ⟨CD, hCD, hdec⟩ := sum_erase_abs_pow_le hs0
  obtain ⟨CW, hCW, hw⟩ := full_sum_erase_weight_le hs0 hs1 ha0 ha1
  refine ⟨CD + CW, by positivity, ?_⟩
  intro N ℓ γ x C₁ C0 i hN hP hℓ hℓ1 hK hC₁ hC0 hi
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hNne : (N : ℝ) ≠ 0 := hNR.ne'
  have hℓne : ℓ ≠ 0 := hℓ.ne'
  have hK0 : (0 : ℝ) ≤ Real.log ((N : ℝ) * ℓ) := Real.log_nonneg hK
  set A := gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) with hAdef
  have hA0 : 0 ≤ A := gradWeightTwo_nonneg_unconditional _ _ _ _ _
  set Q := (1 + Real.log ((N : ℝ) * ℓ)) with hQdef
  have hQ1 : 1 ≤ Q := by linarith
  set T := ℓ⁻¹ * A + (N : ℝ) * ((N : ℝ) * ℓ) ^ a / (1 + circDist (N : ℝ) ((N : ℝ) * x)) ^ (1 + s / 2)
    with hTdef
  -- the weight at each label, split into the two summands
  have hsplit : ∀ j ∈ (gradLabels N ℓ γ).erase i,
      gradQuadCell s a (N : ℕ) ℓ C₁ C0 x (gradPathIncr N ℓ γ i j)
        = (C₁ * C0 * ℓ⁻¹) * (A * |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ^ (-1 - s))
          + (C₁ * C0 * ℓ⁻¹) * (gradWeightTwo s a ((N : ℝ) * ℓ) (N / ((N : ℝ) * ℓ))
              (((N : ℝ) * x + ((gradPathIncr N ℓ γ i j : ℤ) : ℝ)) / ((N : ℝ) * ℓ))
            * |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ^ (-1 - s)) := by
    intro j _
    unfold gradQuadCell
    rw [gradWeightTwo_cell_eq s a hNne hℓne]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  have hD := hdec (N : ℕ+) ℓ γ i (by exact_mod_cast hN) hP hi
  have hWt := hw (N : ℕ+) ℓ γ x i hN hP hℓ hℓ1 hK hi
  have hN1 : (N : ℝ) / ((N : ℝ) * ℓ) = ℓ⁻¹ := by
    field_simp
  have hN2 : ((N : ℝ) * x) / ((N : ℝ) * ℓ) = x / ℓ := by
    field_simp
  have hK0' : (0 : ℝ) < (N : ℝ) * ℓ := mul_pos hNR hℓ
  have hA' : gradWeightTwo s a ((N : ℝ) * ℓ) ((N : ℝ) / ((N : ℝ) * ℓ))
      (((N : ℝ) * x) / ((N : ℝ) * ℓ)) = A := by
    rw [hAdef, hN1, hN2]
  have hK' : ((N : ℝ) * ℓ) ^ (1 + a) / (1 + circDist (N : ℝ) ((N : ℝ) * x)) ^ (1 + s / 2)
      = ℓ * ((N : ℝ) * ((N : ℝ) * ℓ) ^ a / (1 + circDist (N : ℝ) ((N : ℝ) * x)) ^ (1 + s / 2)) := by
    rw [Real.rpow_add hK0', Real.rpow_one]
    field_simp
  rw [hA', hK'] at hWt
  have hSB : ∑ j ∈ (gradLabels N ℓ γ).erase i,
      gradWeightTwo s a ((N : ℝ) * ℓ) ((N : ℝ) / ((N : ℝ) * ℓ))
          (((N : ℝ) * x + ((gradPathIncr N ℓ γ i j : ℤ) : ℝ)) / ((N : ℝ) * ℓ))
        * |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ^ (-1 - s)
      ≤ CW * Q * (A + ℓ * ((N : ℝ) * ((N : ℝ) * ℓ) ^ a
          / (1 + circDist (N : ℝ) ((N : ℝ) * x)) ^ (1 + s / 2))) := hWt
  set T := ℓ⁻¹ * A + (N : ℝ) * ((N : ℝ) * ℓ) ^ a / (1 + circDist (N : ℝ) ((N : ℝ) * x)) ^ (1 + s / 2)
    with hTdef
  have hR0 : 0 ≤ (N : ℝ) * ((N : ℝ) * ℓ) ^ a / (1 + circDist (N : ℝ) ((N : ℝ) * x)) ^ (1 + s / 2) := by
    have := gradCell_circDist_nonneg (N : ℝ) ((N : ℝ) * x)
    apply div_nonneg (by positivity)
    exact Real.rpow_nonneg (by linarith) _
  have hT0 : 0 ≤ T := by
    rw [hTdef]
    have : 0 ≤ ℓ⁻¹ * A := mul_nonneg (inv_nonneg.mpr hℓ.le) hA0
    linarith
  have hleT : ℓ⁻¹ * A ≤ T := by
    rw [hTdef]
    linarith
  have hQT : T ≤ Q * T := by nlinarith
  have hcoef : 0 ≤ C₁ * C0 * ℓ⁻¹ := by
    have : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr hℓ.le
    positivity
  have hSA : ∑ j ∈ (gradLabels N ℓ γ).erase i,
      |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ^ (-1 - s) ≤ CD := hD
  calc (C₁ * C0 * ℓ⁻¹) * (A * ∑ j ∈ (gradLabels N ℓ γ).erase i,
            |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ^ (-1 - s))
        + (C₁ * C0 * ℓ⁻¹) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
            gradWeightTwo s a ((N : ℝ) * ℓ) ((N : ℝ) / ((N : ℝ) * ℓ))
                (((N : ℝ) * x + ((gradPathIncr N ℓ γ i j : ℤ) : ℝ)) / ((N : ℝ) * ℓ))
              * |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ^ (-1 - s)
      ≤ (C₁ * C0 * ℓ⁻¹) * (A * CD) + (C₁ * C0 * ℓ⁻¹) * (CW * Q * (A + ℓ * ((N : ℝ) * ((N : ℝ) * ℓ) ^ a
          / (1 + circDist (N : ℝ) ((N : ℝ) * x)) ^ (1 + s / 2)))) := by
        gcongr
    _ = C₁ * C0 * (CD * (ℓ⁻¹ * A) + CW * Q * T) := by
        rw [hTdef]
        field_simp
    _ ≤ C₁ * C0 * (CD * (Q * T) + CW * Q * T) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC₁ hC0)
        have hCD : 0 ≤ CD := hCD.le
        have hCW : 0 ≤ CW := hCW.le
        nlinarith [mul_le_mul_of_nonneg_left hleT hCD, mul_le_mul_of_nonneg_left hQT hCD,
          mul_nonneg (mul_nonneg hCW (by linarith : (0:ℝ) ≤ Q)) hT0]
    _ = (CD + CW) * C₁ * C0 * Q * T := by ring

end

end Riesz1
