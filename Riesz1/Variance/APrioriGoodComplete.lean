/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGood
public import Riesz1.Variance.APrioriGoodGradientEuclid

/-!
# Good event and cutoff in the a priori bound, complete statement

This is part of the proof of Lemma 5.2, with all its claims, conditional on
the rigidity conclusion `Riesz1.Internal.RigidityConclusion`.

The top theorem `Riesz1.Internal.aPrioriGood_of_rigidity` of `Riesz1/Variance/APrioriGood.lean`
proves the probability, deterministic, support and bridging claims, and the vanishing of the
gradient, together with a coordinatewise gradient bound. This file replaces the coordinatewise
bound by the Euclidean bound `|∇η̃| ≤ C K^A` almost everywhere, proved in
`Riesz1/Variance/APrioriGoodGradientEuclid.lean` with `A = 3γ + ε` and `C = 684`.

The statement quantifies `A` and `C` existentially. The gradient is
`η̃` in the dimensionless gaps `z_i = N (x_{i+1} - x_i)`, and its Euclidean norm is
`√(∑_j (∂_j η̃)^2)` with `∂_j η̃ = fderiv η̃ e_j`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

namespace Internal

/-- **Good event and cutoff, complete statement.** This is conditional on the rigidity
conclusion at `(β, s)`. The probability claim takes the Prékopa–Leindler inequality
`External.PrekopaLeindler` as an explicit argument:

1. (probability) for every `ε > 0` and `B > 0` there is `C > 0` with `dGi(η_{ε,γ} ≠ 1) ≤ C K^{-B}`
   for every `N ≥ 2` and `1 ≤ K ≤ N`.
2. (deterministic) for every `0 < ε ≤ ε₀ = γ (1 - s/2)`, on the good event, the comparisons, the
   packing bound and the anchored error bound hold.
3. (support) the cutoff is nonzero only on the good event.
4. (gradient) for every `ε > 0` there are `A` and `C > 0` such that, for every `N` and every `K ≥ 1`,
   in the dimensionless gaps `z`, the gradient of `η̃` vanishes where `η̃ = 1`. It vanishes at gap
   vectors with positive coordinates outside the good event, and `|∇η̃| ≤ C K^A` for almost every
   `z`.
5. (bridging) `η_{ε,γ}(X) = η̃(z)` for `z_i = N (x_{i+1} - x_i)`.

The vanishing claims in part 4 are restricted to positive gap coordinates. This restriction is
necessary: for `N = 2`, `K = 4`, `ε = 1/2`, `γ = 0`, `s = 1/2` and `z = (-1/2, 6/5)`, the cutoff is
`0.8 (z₀ + 1/2)²` near `z`, so its derivative is `4/5` although `z` lies outside the good event. -/
theorem aPrioriGood_complete_of_rigidity (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hRig : Internal.RigidityConclusion beta s hbeta hs hs1) (γ : ℝ) (hγ : 1 < γ) :
    (∀ ε : ℝ, 0 < ε → ∀ B : ℝ, 0 < B →
      ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+), 2 ≤ (N : ℕ) →
        ∀ K : ℝ, 1 ≤ K → K ≤ (N : ℕ) →
          gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N
              {X | goodCutoff N s K γ ε X ≠ 1} ≤
            ENNReal.ofReal (C * K ^ (-B))) ∧
    (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ (N : ℕ+) (K : ℝ), 1 ≤ K →
      ∀ X : Configuration N, X ∈ goodEvent N s K γ ε →
        (∀ i j : Fin (N : ℕ), i ∈ window N K γ → j ∈ window N K γ →
          K ^ (-ε) * (cyclicIndexDistance N i j : ℝ)
              ≤ ((N : ℕ) : ℝ) * circDist 1 (X.val j - X.val i) ∧
            ((N : ℕ) : ℝ) * circDist 1 (X.val j - X.val i)
              ≤ 2 * K ^ ε * (cyclicIndexDistance N i j : ℝ)) ∧
        (∀ t₀ : ℝ, ((({i : Fin (N : ℕ) | i ∈ window N K γ ∧
            ∃ q : ℤ, X.val i + q ∈ Set.Ico t₀ (t₀ + 1 / ((N : ℕ) : ℝ))}).ncard : ℕ) : ℝ)
              ≤ 3 * K ^ ε) ∧
        (∀ i : Fin (N : ℕ), i ∈ window N K γ →
          |((N : ℕ) : ℝ) * (X.val i - X.val ⟨0, N.pos⟩) - ((i : ℕ) : ℝ)|
            ≤ K ^ ε * ((labelDistToOne N i : ℕ) : ℝ) ^ (s / 2))) ∧
    (∀ (N : ℕ+) (ε K : ℝ), 0 < K → ∀ X : Configuration N,
      goodCutoff N s K γ ε X ≠ 0 → X ∈ goodEvent N s K γ ε) ∧
    (∀ ε : ℝ, 0 < ε → ∃ A C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (K : ℝ), 1 ≤ K →
      (∀ z : Fin (N : ℕ) → ℝ, gapCutoff N s K γ ε z = 1 →
        fderiv ℝ (gapCutoff N s K γ ε) z = 0) ∧
      (∀ z : Fin (N : ℕ) → ℝ, (∀ i : Fin (N : ℕ), 0 < z i) → z ∉ gapGoodEvent N s K γ ε →
        fderiv ℝ (gapCutoff N s K γ ε) z = 0) ∧
      (∀ᵐ z ∂(volume : Measure (Fin (N : ℕ) → ℝ)),
        Real.sqrt (∑ j : Fin (N : ℕ),
            (fderiv ℝ (gapCutoff N s K γ ε) z (Pi.single j (1 : ℝ))) ^ 2)
          ≤ C * K ^ A)) ∧
    (∀ (N : ℕ+) (ε K : ℝ) (X : Configuration N),
      goodCutoff N s K γ ε X =
        gapCutoff N s K γ ε (fun i : Fin (N : ℕ) => gap X ((i : ℕ) : ℤ))) := by
  obtain ⟨hprob, hdet, hsupp, hgrad, hbridge⟩ :=
    aPrioriGood_of_rigidity beta s hbeta hs hs1 hRig γ hγ
  refine ⟨hprob, hdet, hsupp, fun ε hε => ⟨3 * γ + ε, 684, by norm_num, fun N K hK => ?_⟩,
    hbridge⟩
  obtain ⟨hz1, hz2, -⟩ := hgrad N ε hε.le K hK
  exact ⟨hz1, hz2, gapCutoff_ae_euclidean_bound s K γ ε hK (by linarith) hs.le hε.le⟩

end Internal

end Riesz1

end
end
