/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriComparisonSummation
public import Riesz1.Variance.APrioriCutoffComplete

/-!
# The comparison conclusion used by the a priori bound

`Internal.APrioriComparisonInput` is the comparison assertion in the proof of Lemma 5.2,
on the weights, cutoff and tilted anchored inverse. It is a proposition, with no new inverse.

The scale is parametrized by `1 ≤ K ≤ N`, equivalently `K = Nℓ` with
`0 < ℓ ≤ 1`. The two alternatives for `w` are the original and augmented
weights. Only the cutoff field, rather than the uncut field, must be in
`L²`. Membership is a conclusion. All field conditions hold almost
everywhere for the actual tilted law.

The smallness threshold and the summation exponent are chosen before
`ε`. The energy exponent is chosen after `a` and before `ε` and `M`.
Constants are uniform in the smooth forcing cutoff, which generalizes
a fixed forcing cutoff.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1.Internal

/-- The full conclusion of the comparison assertion in the proof of Lemma 5.2.
The parameter `n` is `N - 1`, the dimension of the anchored simplex. -/
def APrioriComparisonInput : Prop :=
  ∀ (P : Parameters) (lam γ : ℝ), 0 ≤ lam → 1 < γ →
    ∃ κ ε₀ : ℝ, 0 < κ ∧ 0 < ε₀ ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ K : ℝ, 1 ≤ K → K ≤ (n : ℝ) + 1 →
        ∀ J : Finset (Fin (n.succPNat : ℕ)),
          J ⊆ (window n.succPNat K γ).erase ⟨0, n.succPNat.pos⟩ →
          (∑ i ∈ J, comparisonWeight n.succPNat K P.val.2 lam ε i *
              (labelDistToOne n.succPNat i : ℝ) ^ (P.val.2 / 2) ≤
            C * K ^ (κ * ε) * (K ^ lam + K ^ (P.val.2 / 2))) ∧
          (∑ i ∈ J, augmentedComparisonWeight n.succPNat K P.val.2 lam ε i *
              (labelDistToOne n.succPNat i : ℝ) ^ (P.val.2 / 2) ≤
            C * K ^ (κ * ε) * (K ^ lam + K ^ (P.val.2 / 2)))) ∧
      (∀ a : ℝ, 0 < a → ∃ κ₁ : ℝ, 0 < κ₁ ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ M : ℝ, 0 < M →
        ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n →
        ∀ (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ) (K : ℝ)
          (hK : 1 ≤ K), K ≤ (n : ℝ) + 1 →
        ∀ J : Finset (Fin (n.succPNat : ℕ)),
          J ⊆ (window n.succPNat K γ).erase ⟨0, n.succPNat.pos⟩ →
        ∀ w : Fin (n.succPNat : ℕ) → ℝ,
          (w = comparisonWeight n.succPNat K P.val.2 lam ε ∨
            w = augmentedComparisonWeight n.succPNat K P.val.2 lam ε) →
        let χ := nearestTiltedPairs P n.succPNat hθ K γ ε (by linarith)
        ∀ v : AnchoredEuclidean n → AnchoredEuclidean n, Measurable v →
          (∀ᵐ y ∂anchoredMeasureE χ, ∀ i : Fin n, i.succ ∉ J → v y i = 0) →
          (∀ᵐ y ∂anchoredMeasureE χ, ∀ i : Fin n,
            anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y) * |v y i| ≤
              M * K ^ (a * ε) *
                anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y) *
                  (((n : ℝ) + 1) * w i.succ)) →
          ∃ hv : MemLp (fun y =>
              anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y) • v y)
                2 (anchoredMeasureE χ),
            anchoredInverseEnergy χ
              (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P))
              (hv.toLp (fun y =>
                anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y) • v y)) ≤
              C * K ^ (κ₁ * ε) * (K ^ (2 * lam) + K ^ P.val.2))

/-- The summation part of `APrioriComparisonInput` is already proved,
with exponent `κ = 2` and threshold `ε₀ = 1`. This includes the
augmented weights and uses no external hypothesis. -/
theorem a_priori_comparison_input_summation (P : Parameters) (lam γ : ℝ)
    (hlam : 0 ≤ lam) (hγ : 1 < γ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ K : ℝ, 1 ≤ K → K ≤ (n : ℝ) + 1 →
      ∀ J : Finset (Fin (n.succPNat : ℕ)),
        J ⊆ (window n.succPNat K γ).erase ⟨0, n.succPNat.pos⟩ →
        (∑ i ∈ J, comparisonWeight n.succPNat K P.val.2 lam ε i *
            (labelDistToOne n.succPNat i : ℝ) ^ (P.val.2 / 2) ≤
          C * K ^ (2 * ε) * (K ^ lam + K ^ (P.val.2 / 2))) ∧
        (∑ i ∈ J, augmentedComparisonWeight n.succPNat K P.val.2 lam ε i *
            (labelDistToOne n.succPNat i : ℝ) ^ (P.val.2 / 2) ≤
          C * K ^ (2 * ε) * (K ^ lam + K ^ (P.val.2 / 2))) := by
  obtain ⟨C, hC, h⟩ := comparison_sums_le P.val.2 lam γ
    P.2.2.1 P.2.2.2 hlam hγ ε hε hε1
  exact ⟨C, hC, fun n _ K hK _ J hJ => h n.succPNat K hK J hJ⟩

end Riesz1.Internal

end
