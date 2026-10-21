/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingQuadraturePartialRemainder
public import Riesz1.Auxiliary.GradientSplittingQuadratureTailWeights
public import Riesz1.Auxiliary.GradientSplittingQuadraturePartialReduce

/-!
# Partial-window quadrature at large scales

The quadrature part of Lemma 5.7. The odd term and the remainder over
the background are combined, and the logarithm is absorbed into `K^(2ε)`.
-/

@[expose] public section

open Set MeasureTheory
open scoped ContDiff

namespace Riesz1

noncomputable section

theorem gradV2_partial_large_bound {s α γ ε : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα0 : s - 1 ≤ α) (hα1 : α < s / 2)
    (hγ4 : 4 ≤ γ) (hγs : 2 / s ≤ γ) (hε0 : 0 < ε) (hε : ε < γ * (1 - s / 2)) :
    ∃ C K₀ : ℝ, 0 < C ∧ 1 ≤ K₀ ∧
    ∀ (N : ℕ+) (ℓ C0 : ℝ) (X : Fin (N : ℕ) → ℝ) (ψ : ℝ → ℝ) (i : ℤ),
      2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → K₀ ≤ (N : ℝ) * ℓ → GradPartial N ℓ γ →
      0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) →
      gradEvent s γ ε N ℓ X →
      |(N : ℝ) * gradLift N X 0| ≤ ((N : ℝ) * ℓ) ^ ε → i ∈ gradLabels N ℓ γ →
      |gradVdisc2 s ψ N ℓ γ X i + gradVbg s ψ N ℓ γ X i|
        ≤ C * C0 * ((N : ℝ) * ℓ) ^ (2 * ε) *
          (ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
            + (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) /
              (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)) := by
  obtain ⟨Cr, Kr, hCr, hKr, hr⟩ := gradPartial_remainder_large_bound hs0 hs1 hα0 hα1
    (by linarith) hε0.le hε
  obtain ⟨Co, Ko, hCo, hKo, ho⟩ := gradPartial_odd_large_bound hs0 hs1 hα0 hα1
    hγ4 hγs hε0.le hε
  refine ⟨2 * Co + 2 * Cr * (1 + 1 / ε), max Kr Ko, by positivity,
    hKr.trans (le_max_left _ _), ?_⟩
  intro N ℓ C0 X ψ i hN hℓ hℓ1 hK0 hP hC0 hψ hper h1 h2 hsupp hX hanchor hi
  have hK : 1 ≤ (N : ℝ) * ℓ := (hKr.trans (le_max_left _ _)).trans hK0
  have hrem := hr N ℓ C0 X ψ i hN hℓ hℓ1 ((le_max_left _ _).trans hK0) hP hC0
    hψ hper h1 h2 hsupp hX hanchor hi
  have hodd := ho N ℓ C0 X ψ i hN hℓ hℓ1 ((le_max_right _ _).trans hK0) hP hC0
    hψ h1 hsupp hX hanchor hi
  have hsplit := gradV2_partial_split hs0 hs1 hα0 hα1 (by linarith) hε.le hN hℓ hℓ1 hK
    hP hC0 hψ hper h1 h2 hsupp X hX hanchor hi
  let T := ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) +
    (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) /
      (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)
  have hW := gradWeightTwo_nonneg_unconditional s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹
    (gradLift N X i / ℓ)
  have hT : 0 ≤ T := by dsimp [T]; have := circDist_nonneg 1 (gradLift N X i); positivity
  have hL := one_add_log_le_rpow hK hε0
  have hE : 1 ≤ ((N : ℝ) * ℓ) ^ (2 * ε) := Real.one_le_rpow hK (by linarith)
  have hKpos : 0 < (N : ℝ) * ℓ := by linarith
  have heq : ((N : ℝ) * ℓ) ^ ε * ((N : ℝ) * ℓ) ^ ε = ((N : ℝ) * ℓ) ^ (2 * ε) := by
    rw [← Real.rpow_add hKpos]; congr 1; ring
  have htotal : |gradVdisc2 s ψ N ℓ γ X i + gradVbg s ψ N ℓ γ X i| ≤
      2 * Co * C0 * T + 2 * Cr * C0 * ((N : ℝ) * ℓ) ^ ε *
        (1 + Real.log ((N : ℝ) * ℓ)) * T := by
    simp only [gradPathIncr, hP, ↓reduceIte] at hrem hodd
    rw [hsplit]
    have ht := abs_add_le
      (2 * deriv ψ (gradLift N X i / ℓ) *
        ((N : ℝ) ^ (1 - s) *
          (gradKernelH s (gradT N ℓ γ - gradLift N X i) -
            gradKernelH s (-gradT N ℓ γ - gradLift N X i)) -
          (N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
            deriv (gradKernelH s) ((j - i : ℤ) / (N : ℝ))))
      (2 * ((∑ j ∈ (gradLabels N ℓ γ).erase i,
            gradCellR s (N : ℕ) ℓ ψ (gradLift N X i) ((j - i : ℤ) : ℝ)) -
          ∫ v in (-gradM N ℓ γ - (N : ℝ) * gradLift N X i)..
            (gradM N ℓ γ - (N : ℝ) * gradLift N X i),
              gradCellR s (N : ℕ) ℓ ψ (gradLift N X i) v))
    simp only [mul_assoc (2 : ℝ), abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ht hodd
    simp only [mul_assoc (2 : ℝ)]
    apply ht.trans
    calc
      _ ≤ 2 * (Co * C0 * T) +
             2 * (Cr * C0 * ((N : ℝ) * ℓ) ^ ε * (1 + Real.log ((N : ℝ) * ℓ)) * T) :=
              add_le_add (mul_le_mul_of_nonneg_left hodd (by norm_num))
                (mul_le_mul_of_nonneg_left hrem (by norm_num))
      _ = 2 * Co * C0 * T + 2 * Cr * C0 * ((N : ℝ) * ℓ) ^ ε *
          (1 + Real.log ((N : ℝ) * ℓ)) * T := by ring
    all_goals (ring_nf; exact le_rfl)
  have hodd' : 2 * Co * C0 * T ≤ 2 * Co * C0 * ((N : ℝ) * ℓ) ^ (2 * ε) * T := by
    nlinarith [mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 2 * Co * C0 * T)]
  have hrem' : 2 * Cr * C0 * ((N : ℝ) * ℓ) ^ ε *
      (1 + Real.log ((N : ℝ) * ℓ)) * T ≤
      2 * Cr * (1 + 1 / ε) * C0 * ((N : ℝ) * ℓ) ^ (2 * ε) * T := by
    calc _ ≤ 2 * Cr * C0 * ((N : ℝ) * ℓ) ^ ε *
        ((1 + 1 / ε) * ((N : ℝ) * ℓ) ^ ε) * T := by gcongr
      _ = _ := by rw [← heq]; ring
  calc _ ≤ _ := htotal
       _ ≤ 2 * Co * C0 * ((N : ℝ) * ℓ) ^ (2 * ε) * T +
          2 * Cr * (1 + 1 / ε) * C0 * ((N : ℝ) * ℓ) ^ (2 * ε) * T := add_le_add hodd' hrem'
       _ = _ := by ring

end

end Riesz1
