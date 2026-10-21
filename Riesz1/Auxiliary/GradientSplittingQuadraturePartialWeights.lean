/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingQuadraturePartialCells
public import Riesz1.Auxiliary.GradientSplittingQuadratureLabels
public import Riesz1.Auxiliary.GradientSplittingConvolutionLattice
public import Riesz1.Auxiliary.GradientSplittingDisplacement

/-!
# Reference-cell weights in either window

The quadrature part of Lemma 5.7. Reuse the reference-point lattice
sum and the decay sum to control the cell weights without an event or packing loss.
The partial-window cell error then has exactly the two target weights.
-/

@[expose] public section

open Set MeasureTheory Finset
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The decay of the weights `|k_{ij}|^{-1-s}` over the labels `j ≠ i` of either window. -/
lemma gradQuad_sum_erase_abs_pow_le {s : ℝ} (hs0 : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ : ℝ) (i : ℤ), 2 ≤ (N : ℕ) →
      i ∈ gradLabels N ℓ γ →
      ∑ j ∈ (gradLabels N ℓ γ).erase i, |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ^ (-1 - s) ≤ C := by
  obtain ⟨C, hC, hdec⟩ := sum_labels_decay_le hs0
  refine ⟨2 ^ (1 + s) * C, by positivity, ?_⟩
  intro N ℓ γ i hN hi
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


/-- The reference weight lattice bound works in either window and needs no event. -/
theorem gradQuad_reference_weight_le {s a : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1 - s / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) (i : ℤ),
      2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → i ∈ gradLabels N ℓ γ →
      ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradW2 s a N ℓ ((N : ℝ) * gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ))
            * |(gradPathIncr N ℓ γ i j : ℝ)| ^ (-1 - s)
        ≤ C * (1 + Real.log ((N : ℝ) * ℓ)) *
          (gradW2 s a N ℓ ((N : ℝ) * gradLift N X i)
            + ((N : ℝ) * ℓ) ^ (1 + a) /
              (1 + circDist (N : ℝ) ((N : ℝ) * gradLift N X i)) ^ (1 + s / 2)) := by
  obtain ⟨C, hC, hlat⟩ := lattice_w2_sum hs0 hs1 ha0 ha1
  refine ⟨2 ^ (1 + s) * C, by positivity, ?_⟩
  intro N ℓ γ X i hN hℓ hℓ1 hK hi
  have hlat' := hlat N ℓ ((N : ℝ) * gradLift N X i) hN hK hℓ1
  have hsum := sum_second_term_le (s := s) (a := a) (X := X) hℓ hi
  have hpow : ∀ j ∈ (gradLabels N ℓ γ).erase i,
      |(gradPathIncr N ℓ γ i j : ℝ)| ^ (-1 - s) ≤
        2 ^ (1 + s) * (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2)) := by
    intro j hj
    obtain ⟨hne, hjl⟩ := Finset.mem_erase.mp hj
    have hk : 1 ≤ |(gradPathIncr N ℓ γ i j : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (gradPathIncr_ne_zero hi hjl hne)
    have hb := rpow_abs_le_two_pow_mul_one_add hs0 hk
    rw [← Int.cast_abs, abs_gradPathIncr_eq hi hjl] at hb
    rw [← Int.cast_abs, abs_gradPathIncr_eq hi hjl]
    exact hb
  have hnonneg : ∀ j ∈ gradLabels N ℓ γ,
      0 ≤ gradW2 s a N ℓ ((N : ℝ) * gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ))
        / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2) := by
    intro j hj
    apply div_nonneg (gradW2_nonneg _ _ _ _ _)
    apply Real.rpow_nonneg
    have hd : (0 : ℝ) ≤ (gradLabelDist N i j : ℝ) := by
      exact_mod_cast gradLabelDist_nonneg (gradLabels_abs_sub_lt hi hj)
    linarith
  have hcalc : (∑ j ∈ (gradLabels N ℓ γ).erase i,
      gradW2 s a N ℓ ((N : ℝ) * gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ))
        * |(gradPathIncr N ℓ γ i j : ℝ)| ^ (-1 - s))
      ≤ 2 ^ (1 + s) * ∑ j ∈ gradLabels N ℓ γ,
          gradW2 s a N ℓ ((N : ℝ) * gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ))
            / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2) := by
    calc
      _ ≤ ∑ j ∈ (gradLabels N ℓ γ).erase i,
          2 ^ (1 + s) * (gradW2 s a N ℓ
            ((N : ℝ) * gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ)) /
                (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2)) := by
          apply Finset.sum_le_sum
          intro j hj
          have hd : (0 : ℝ) ≤ (gradLabelDist N i j : ℝ) := by
            exact_mod_cast gradLabelDist_nonneg
              (gradLabels_abs_sub_lt hi (Finset.mem_of_mem_erase hj))
          rw [div_rpow_eq_mul_rpow_neg (by linarith)]
          calc _ ≤ _ := mul_le_mul_of_nonneg_left (hpow j hj) (gradW2_nonneg _ _ _ _ _)
               _ = _ := by ring
      _ = 2 ^ (1 + s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
            gradW2 s a N ℓ ((N : ℝ) * gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ))
              / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun j hj _ => hnonneg j hj)) (by positivity)
  refine hcalc.trans ?_
  have e (y : ℝ) : (1 + circDist (N : ℝ) y) ^ (-(1 + s / 2)) =
      ((1 + circDist (N : ℝ) y) ^ (1 + s / 2))⁻¹ :=
    Real.rpow_neg (by linarith [circDist_nonneg (N : ℝ) y]) _
  simp_rw [e, ← div_eq_mul_inv] at hlat'
  have hsum' := hsum.trans hlat'
  calc
    _ ≤ 2 ^ (1 + s) * (C * (1 + Real.log ((N : ℝ) * ℓ)) *
        (gradW2 s a N ℓ ((N : ℝ) * gradLift N X i) + ((N : ℝ) * ℓ) ^ (1 + a) /
          (1 + circDist (N : ℝ) ((N : ℝ) * gradLift N X i)) ^ (1 + s / 2))) :=
      mul_le_mul_of_nonneg_left hsum' (by positivity)
    _ = _ := by ring

/-- Summing the cell weights `gradQuadCell` over the labels `j ≠ i` of either window: the
decay bound for `∑ |k_{ij}|^{-1-s}` and the lattice bound for the weighted sum, with the factor
`ℓ^{-1} (Nℓ)^{1+a} = N (Nℓ)^a`. -/
theorem gradQuad_sum_erase_cell_le {s a : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a)
    (ha1 : a < 1 - s / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ C₁ C0 : ℝ) (X : Fin (N : ℕ) → ℝ) (i : ℤ), 2 ≤ (N : ℕ) →
      0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → 0 ≤ C₁ → 0 ≤ C0 → i ∈ gradLabels N ℓ γ →
      ∑ j ∈ (gradLabels N ℓ γ).erase i, gradQuadCell s a (N : ℕ) ℓ C₁ C0 (gradLift N X i)
          (gradPathIncr N ℓ γ i j)
        ≤ C * C₁ * C0 * (1 + Real.log ((N : ℝ) * ℓ)) *
          (ℓ⁻¹ * gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((gradLift N X i) / ℓ)
            + (N : ℝ) * ((N : ℝ) * ℓ) ^ a / (1 + circDist (N : ℝ) ((N : ℝ) * (gradLift N X i))) ^ (1 + s / 2)) := by
  obtain ⟨CD, hCD, hdec⟩ := gradQuad_sum_erase_abs_pow_le hs0
  obtain ⟨CW, hCW, hw⟩ := gradQuad_reference_weight_le hs0 hs1 ha0 ha1
  refine ⟨CD + CW, by positivity, ?_⟩
  intro N ℓ γ C₁ C0 X i hN hℓ hℓ1 hK hC₁ hC0 hi
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hNne : (N : ℝ) ≠ 0 := hNR.ne'
  have hℓne : ℓ ≠ 0 := hℓ.ne'
  have hK0 : (0 : ℝ) ≤ Real.log ((N : ℝ) * ℓ) := Real.log_nonneg hK
  set A := gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((gradLift N X i) / ℓ) with hAdef
  have hA0 : 0 ≤ A := gradWeightTwo_nonneg_unconditional _ _ _ _ _
  set Q := (1 + Real.log ((N : ℝ) * ℓ)) with hQdef
  have hQ1 : 1 ≤ Q := by linarith
  set T := ℓ⁻¹ * A + (N : ℝ) * ((N : ℝ) * ℓ) ^ a / (1 + circDist (N : ℝ) ((N : ℝ) * (gradLift N X i))) ^ (1 + s / 2)
    with hTdef
  -- the weight at each label, split into the two summands
  have hsplit : ∀ j ∈ (gradLabels N ℓ γ).erase i,
      gradQuadCell s a (N : ℕ) ℓ C₁ C0 (gradLift N X i) (gradPathIncr N ℓ γ i j)
        = (C₁ * C0 * ℓ⁻¹) * (A * |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ^ (-1 - s))
          + (C₁ * C0 * ℓ⁻¹) * (gradWeightTwo s a ((N : ℝ) * ℓ) (N / ((N : ℝ) * ℓ))
              (((N : ℝ) * (gradLift N X i) + ((gradPathIncr N ℓ γ i j : ℤ) : ℝ)) / ((N : ℝ) * ℓ))
            * |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ^ (-1 - s)) := by
    intro j _
    unfold gradQuadCell
    rw [gradWeightTwo_cell_eq s a hNne hℓne]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  have hD := hdec (N : ℕ+) ℓ γ i (by exact_mod_cast hN) hi
  have hWt := hw N ℓ γ X i hN hℓ hℓ1 hK hi
  unfold gradW2 at hWt
  have hnorm (k : ℝ) : ((N : ℝ) * gradLift N X i + k) / ((N : ℝ) * ℓ) =
      (gradLift N X i + k / N) / ℓ := by field_simp
  simp_rw [hnorm] at hWt
  have hperiod : (N : ℝ) / ((N : ℝ) * ℓ) = ℓ⁻¹ := by field_simp
  rw [hperiod] at hWt
  have hN2 : ((N : ℝ) * gradLift N X i) / ((N : ℝ) * ℓ) = gradLift N X i / ℓ := by
    field_simp
  have hK0' : (0 : ℝ) < (N : ℝ) * ℓ := mul_pos hNR hℓ
  have hK' : ((N : ℝ) * ℓ) ^ (1 + a) / (1 + circDist (N : ℝ) ((N : ℝ) * (gradLift N X i))) ^ (1 + s / 2)
      = ℓ * ((N : ℝ) * ((N : ℝ) * ℓ) ^ a / (1 + circDist (N : ℝ) ((N : ℝ) * (gradLift N X i))) ^ (1 + s / 2)) := by
    rw [Real.rpow_add hK0', Real.rpow_one]
    field_simp
  rw [hN2] at hWt
  change _ ≤ CW * (1 + Real.log ((N : ℝ) * ℓ)) *
    (A + ((N : ℝ) * ℓ) ^ (1 + a) /
      (1 + circDist (N : ℝ) ((N : ℝ) * gradLift N X i)) ^ (1 + s / 2)) at hWt
  rw [hK'] at hWt
  have hSB : ∑ j ∈ (gradLabels N ℓ γ).erase i,
      gradWeightTwo s a ((N : ℝ) * ℓ) ((N : ℝ) / ((N : ℝ) * ℓ))
          (((N : ℝ) * (gradLift N X i) + ((gradPathIncr N ℓ γ i j : ℤ) : ℝ)) / ((N : ℝ) * ℓ))
        * |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ^ (-1 - s)
      ≤ CW * Q * (A + ℓ * ((N : ℝ) * ((N : ℝ) * ℓ) ^ a
          / (1 + circDist (N : ℝ) ((N : ℝ) * (gradLift N X i))) ^ (1 + s / 2))) := by
    simpa only [hperiod, hnorm] using hWt
  set T := ℓ⁻¹ * A + (N : ℝ) * ((N : ℝ) * ℓ) ^ a / (1 + circDist (N : ℝ) ((N : ℝ) * (gradLift N X i))) ^ (1 + s / 2)
    with hTdef
  have hR0 : 0 ≤ (N : ℝ) * ((N : ℝ) * ℓ) ^ a / (1 + circDist (N : ℝ) ((N : ℝ) * (gradLift N X i))) ^ (1 + s / 2) := by
    have := gradCell_circDist_nonneg (N : ℝ) ((N : ℝ) * (gradLift N X i))
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
                (((N : ℝ) * (gradLift N X i) + ((gradPathIncr N ℓ γ i j : ℤ) : ℝ)) / ((N : ℝ) * ℓ))
              * |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ^ (-1 - s)
      ≤ (C₁ * C0 * ℓ⁻¹) * (A * CD) + (C₁ * C0 * ℓ⁻¹) * (CW * Q * (A + ℓ * ((N : ℝ) * ((N : ℝ) * ℓ) ^ a
          / (1 + circDist (N : ℝ) ((N : ℝ) * (gradLift N X i))) ^ (1 + s / 2)))) := by
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

/-- The complete remainder-cell error in a partial window has the target weights of the paper.
Only the mismatch strips remain before passing to the background interval. -/
theorem gradPartial_remainder_cells_bound {s α : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα0 : s - 1 ≤ α) (hα1 : α < s / 2) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ+) (ℓ γ C0 : ℝ) (X : Fin (N : ℕ) → ℝ) (ψ : ℝ → ℝ) (i : ℤ),
      2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → 0 ≤ γ → GradPartial N ℓ γ →
      0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      i ∈ gradLabels N ℓ γ →
      |(∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradCellR s (N : ℕ) ℓ ψ (gradLift N X i) (gradPathIncr N ℓ γ i j))
        - ∫ v in (-(⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) - 1 / 2)..
            ((⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) + 1 / 2),
              gradCellR s (N : ℕ) ℓ ψ (gradLift N X i) v|
        ≤ C * C0 * (1 + Real.log ((N : ℝ) * ℓ)) *
          (ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
            + (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) /
              (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)) := by
  obtain ⟨Cc, Cd, hCc, hCd, hcell⟩ := gradPartial_remainder_cell_error hs0 hs1 hα0 hα1
  obtain ⟨Cq, hCq, hsum⟩ := gradQuad_sum_erase_cell_le hs0 hs1
    (by linarith : 0 ≤ 1 - s + α) (by linarith : 1 - s + α < 1 - s / 2)
  refine ⟨Cq * Cd + Cc, by positivity, ?_⟩
  intro N ℓ γ C0 X ψ i hN hℓ hℓ1 hK hγ hP hC0 hψ hper h1 h2 hi
  have hc := hcell N ℓ γ C0 (gradLift N X i) ψ i hN hℓ hℓ1 hK hγ hP hC0 hψ hper h1 h2 hi
  have hq := hsum N ℓ γ Cd C0 X i hN hℓ hℓ1 hK hCd.le hC0 hi
  have hNR : (0 : ℝ) < N := by exact_mod_cast N.pos
  rw [circDist_mul_self_scale hNR] at hq
  let A := ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
  let B := (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) /
    (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)
  let L := 1 + Real.log ((N : ℝ) * ℓ)
  have hA : 0 ≤ A := mul_nonneg (inv_nonneg.mpr hℓ.le)
    (gradWeightTwo_nonneg_unconditional _ _ _ _ _)
  have hB : 0 ≤ B := div_nonneg (mul_nonneg hNR.le (Real.rpow_nonneg (by linarith) _))
    (Real.rpow_nonneg (by have := mul_nonneg hNR.le (circDist_nonneg 1 (gradLift N X i)); linarith) _)
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hK]
  have hAL : A ≤ L * (A + B) := by nlinarith
  have he := mul_le_mul_of_nonneg_left hAL (mul_nonneg hCc.le hC0)
  change _ ≤ (Cq * Cd + Cc) * C0 * L * (A + B)
  calc _ ≤ Cq * Cd * C0 * L * (A + B) + Cc * C0 * A :=
      hc.trans (by
        calc _ ≤ _ := add_le_add hq le_rfl
             _ = _ := by dsimp [A, B, L]; ring)
    _ ≤ _ := by nlinarith [he]

end

end Riesz1
