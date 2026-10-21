/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingQuadratureStrips

/-!
# Remainder quadrature over the partial background

The quadrature part of Lemma 5.7. Combine the reference cells and the
two mismatch strips, using the integrability on the half-period.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

theorem gradPartial_remainder_large_bound {s α γ ε : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα0 : s - 1 ≤ α) (hα1 : α < s / 2)
    (hγ : 0 ≤ γ) (hε0 : 0 ≤ ε) (hε : ε < γ * (1 - s / 2)) :
    ∃ C K₀ : ℝ, 0 < C ∧ 1 ≤ K₀ ∧
    ∀ (N : ℕ+) (ℓ C0 : ℝ) (X : Fin (N : ℕ) → ℝ) (ψ : ℝ → ℝ) (i : ℤ),
      2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → K₀ ≤ (N : ℝ) * ℓ → GradPartial N ℓ γ →
      0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) →
      gradEvent s γ ε N ℓ X →
      |(N : ℝ) * gradLift N X 0| ≤ ((N : ℝ) * ℓ) ^ ε → i ∈ gradLabels N ℓ γ →
      |(∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradCellR s (N : ℕ) ℓ ψ (gradLift N X i) (gradPathIncr N ℓ γ i j))
        - ∫ v in (-gradM N ℓ γ - (N : ℝ) * gradLift N X i)..
            (gradM N ℓ γ - (N : ℝ) * gradLift N X i),
              gradCellR s (N : ℕ) ℓ ψ (gradLift N X i) v|
        ≤ C * C0 * ((N : ℝ) * ℓ) ^ ε * (1 + Real.log ((N : ℝ) * ℓ)) *
          (ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
            + (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) /
              (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)) := by
  obtain ⟨Cc, hCc, hcell⟩ := gradPartial_remainder_cells_bound hs0 hs1 hα0 hα1
  obtain ⟨Cs, K₀, hCs, hK₀, hstrip⟩ := gradPartial_strips_bound hs0 hs1 hα0 hα1 hγ hε0 hε
  refine ⟨Cc + Cs, K₀, by positivity, hK₀, ?_⟩
  intro N ℓ C0 X ψ i hN hℓ hℓ1 hK0 hP hC0 hψ hper h1 h2 hsupp hX hanchor hi
  have hK := hK₀.trans hK0
  have hM : 1 ≤ gradM N ℓ γ := Real.one_le_rpow hK hγ
  have hx := gradPartial_anchor_lift_bound hs0 hγ hε.le hK hP hX hanchor hi
  let R := gradCellR s (N : ℕ) ℓ ψ (gradLift N X i)
  let a := -gradM N ℓ γ - (N : ℝ) * gradLift N X i
  let b := gradM N ℓ γ - (N : ℝ) * gradLift N X i
  let c := -(⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) - 1 / 2
  let d := (⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) + 1 / 2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hhalf := intervalIntegrable_gradCellR_half hs0 hs1 hα0 hα1 hN hℓ hℓ1 hK hC0
    hψ hper h1 h2 (x := gradLift N X i)
  rw [← neg_div] at hhalf
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have ha0 := gradPartial_background_range hP hx (left_mem_Icc.mpr hab)
  have hb0 := gradPartial_background_range hP hx (right_mem_Icc.mpr hab)
  have hrange := gradPartial_cells_range hP hM hi
  have hcd : c ≤ d := by
    have hn : (0 : ℝ) ≤ (⌊gradM N ℓ γ⌋ : ℝ) := by
      exact_mod_cast Int.floor_nonneg.mpr (by linarith : 0 ≤ gradM N ℓ γ)
    dsimp [c, d]; linarith
  have hmembg : a ∈ uIcc (-(N : ℝ) / 2) ((N : ℝ) / 2) ∧
      b ∈ uIcc (-(N : ℝ) / 2) ((N : ℝ) / 2) := by
    rw [uIcc_of_le (by linarith : -(N : ℝ) / 2 ≤ (N : ℝ) / 2)]
    exact ⟨⟨by linarith [(abs_le.mp ha0.2.le).1], by linarith [(abs_le.mp ha0.2.le).2]⟩,
      ⟨by linarith [(abs_le.mp hb0.2.le).1], by linarith [(abs_le.mp hb0.2.le).2]⟩⟩
  have hmemcell : c ∈ uIcc (-(N : ℝ) / 2) ((N : ℝ) / 2) ∧
      d ∈ uIcc (-(N : ℝ) / 2) ((N : ℝ) / 2) := by
    rw [uIcc_of_le (by linarith : -(N : ℝ) / 2 ≤ (N : ℝ) / 2)]
    exact ⟨⟨hrange.1, hcd.trans hrange.2⟩, ⟨hrange.1.trans hcd, hrange.2⟩⟩
  have hdiff := integral_interval_sub_interval_comm
    (hhalf.mono_set (uIcc_subset_uIcc hmembg.1 hmembg.2))
    (hhalf.mono_set (uIcc_subset_uIcc hmemcell.1 hmemcell.2))
    (hhalf.mono_set (uIcc_subset_uIcc hmembg.1 hmemcell.1))
  change (∫ v in a..b, R v) - (∫ v in c..d, R v) =
    (∫ v in a..c, R v) - (∫ v in b..d, R v) at hdiff
  have hs := hstrip N ℓ C0 X ψ i hN hℓ hℓ1 hK0 hP hC0 hψ hper h1 h2 hsupp hX hanchor hi
  have hc := hcell N ℓ γ C0 X ψ i hN hℓ hℓ1 hK hγ hP hC0 hψ hper h1 h2 hi
  let A := ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
  let B := (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) /
    (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)
  let L := 1 + Real.log ((N : ℝ) * ℓ)
  let E := ((N : ℝ) * ℓ) ^ ε
  have hA : 0 ≤ A := mul_nonneg (inv_nonneg.mpr hℓ.le) (gradWeightTwo_nonneg_unconditional _ _ _ _ _)
  have hB : 0 ≤ B := by dsimp [B]; have := circDist_nonneg 1 (gradLift N X i); positivity
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hK]
  have hE : 1 ≤ E := Real.one_le_rpow hK hε0
  have h0 : 0 ≤ Cc * C0 * L * (A + B) := by positivity
  have h1' : Cc * C0 * L * (A + B) ≤ Cc * C0 * E * L * (A + B) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hE) h0]
  have h2' : Cs * C0 * E * A ≤ Cs * C0 * E * L * (A + B) := by
    have hle : A ≤ L * (A + B) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ Cs * C0 * E)]
  have hid (S : ℝ) : S - (∫ v in a..b, R v) =
      (S - ∫ v in c..d, R v) - ((∫ v in a..b, R v) - ∫ v in c..d, R v) := by ring
  change |(∑ j ∈ (gradLabels N ℓ γ).erase i, R (gradPathIncr N ℓ γ i j)) -
    ∫ v in a..b, R v| ≤ (Cc + Cs) * C0 * E * L * (A + B)
  rw [hid, hdiff]
  refine (abs_sub _ _).trans ?_
  refine (add_le_add le_rfl (abs_sub _ _)).trans ?_
  calc _ ≤ Cc * C0 * L * (A + B) + Cs * C0 * E * A :=
      add_le_add hc (by simpa only [A, E, mul_assoc, mul_left_comm, mul_comm] using hs)
    _ ≤ Cc * C0 * E * L * (A + B) + Cs * C0 * E * L * (A + B) := add_le_add h1' h2'
    _ = _ := by ring

end

end Riesz1
