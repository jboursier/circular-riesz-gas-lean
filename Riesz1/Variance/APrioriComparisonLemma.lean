/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriComparisonEstimate

/-!
# Summation and comparison: complete statement

This is part of the proof of Lemma 5.2. The exponent for summation is
chosen before `ε`. The energy exponent is chosen after `a` and before
`ε` and `M`. Each constant is chosen before the particle number, scale,
selected labels, forcing cutoff and field. Both original and augmented
weights are included. All `K ≥ 1` are allowed, which includes `K = Nℓ`
for the range `0 < ℓ ≤ 1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Classical

namespace Riesz1

/-- **Summation and comparison, all assertions.** The only external hypotheses are the
Bakry–Émery criterion `hBE` and the Prékopa–Leindler inequality `hPL`. The energy is the actual
anchored inverse energy under the nearest-neighbour tilted law. Merely
measurable fields suffice. Their cutoff products are proved to be in `L²`.
The explicit choices are `κ = 2` and `κ₁ = 2a + 4 + 2γ`.
The two conjuncts keep the summation constant independent of `M` and `a`. -/
theorem a_priori_comparison (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 1 < γ) :
    ∃ κ : ℝ, 0 < κ ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C : ℝ, 0 < C ∧
        ∀ (N : ℕ+) (K : ℝ), 1 ≤ K →
        ∀ J : Finset (Fin (N : ℕ)), J ⊆ (window N K γ).erase ⟨0, N.pos⟩ →
          (∑ i ∈ J, comparisonWeight N K P.val.2 lam ε i *
            (labelDistToOne N i : ℝ) ^ (P.val.2 / 2) ≤
              C * K ^ (κ * ε) * (K ^ lam + K ^ (P.val.2 / 2))) ∧
          (∑ i ∈ J, augmentedComparisonWeight N K P.val.2 lam ε i *
            (labelDistToOne N i : ℝ) ^ (P.val.2 / 2) ≤
              C * K ^ (κ * ε) * (K ^ lam + K ^ (P.val.2 / 2)))) ∧
      (∀ a : ℝ, 0 < a → ∃ κ₁ : ℝ, 0 < κ₁ ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ M : ℝ, 0 < M →
          ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ),
          ∀ (K : ℝ) (hK : 1 ≤ K), ∀ J : Finset (Fin (n + 1)),
          J ⊆ (window n.succPNat K γ).erase ⟨0, n.succPNat.pos⟩ →
          ∀ w : Fin (n + 1) → ℝ,
            (w = comparisonWeight n.succPNat K P.val.2 lam ε ∨
              w = augmentedComparisonWeight n.succPNat K P.val.2 lam ε) →
          let χ := nearestTiltedPairs P n.succPNat hθ K γ ε (by linarith)
          ∀ (v : AnchoredEuclidean n → AnchoredEuclidean n), Measurable v →
            (∀ i, ∀ᵐ y ∂anchoredMeasureE χ, i.succ ∉ J → v y i = 0) →
            (∀ i, ∀ᵐ y ∂anchoredMeasureE χ,
              anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y) * |v y i| ≤
                (M * K ^ (a * ε)) * anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y) *
                  (((n : ℝ) + 1) * w i.succ)) →
            ∃ hv : MemLp (fun y => anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y) • v y)
                2 (anchoredMeasureE χ),
              anchoredInverseEnergy χ
                (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P))
                (hv.toLp (fun y => anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y) • v y)) ≤
                  C * K ^ (κ₁ * ε) * (K ^ (2 * lam) + K ^ P.val.2)) := by
  refine ⟨2, by norm_num, ?_, ?_⟩
  · exact fun ε hε hε1 => comparison_sums_le P.val.2 lam γ
      P.2.2.1 P.2.2.2 hlam hγ ε hε hε1
  · intro a ha
    refine ⟨2 * a + 4 + 2 * γ, by linarith, ?_⟩
    intro ε hε hε1 M hM
    exact a_priori_comparison_energy hBE hPL P lam γ M a hlam hγ hM ha ε hε hε1

end Riesz1

end
