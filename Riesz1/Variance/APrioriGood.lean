/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodCutoff
public import Riesz1.Variance.APrioriGoodComparison
public import Riesz1.Variance.APrioriGoodProbability
public import Riesz1.Variance.APrioriGoodGradientDefs
public import Riesz1.Variance.APrioriGoodGradientVanishing
public import Riesz1.Variance.APrioriGoodGradientBound

/-!
# The good event and its cutoff, part of Lemma 5.2

The probability, packing and cutoff-derivative estimates of Lemma 5.2 for the good-event
cutoff `η_{ε,γ}` and the good event `A_{ε,γ}`.

The statement is conditional on the rigidity conclusion `Riesz1.Internal.RigidityConclusion` at
`(β, s)`. The probability claim takes the Prékopa–Leindler inequality
`External.PrekopaLeindler` as an explicit argument, as the rigidity lemmas do.

Parts of the lemma, with their Lean names:

* probability: `Riesz1.Internal.goodCutoff_prob_le_of_rigidity`.
* deterministic claims on the good event (comparisons, packing, anchored error):
  `Riesz1.aPrioriGood_deterministic`.
* support of the cutoff: `Riesz1.goodEvent_of_goodCutoff_ne_zero`.
* gradient in the dimensionless gaps: `Riesz1.gapCutoff_ae_fderiv_bound`,
  `Riesz1.fderiv_gapCutoff_eq_zero_of_eq_one`, `Riesz1.fderiv_gapCutoff_eq_zero_of_not_mem`.
* bridging identity `η_{ε,γ}(X) = η̃(gaps of X)`: `Riesz1.goodCutoff_eq_gapCutoff`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

namespace Internal

/-- **Good-event estimates of Lemma 5.2.** Conditional on the rigidity conclusion at `(β, s)`:

1. (probability) for every `ε > 0` and `B > 0` there is `C > 0` with `dGi(η_{ε,γ} ≠ 1) ≤ C K^{-B}`
   for every `N ≥ 2` and `1 ≤ K ≤ N`, assuming the Prékopa–Leindler inequality.
2. (deterministic) for every `0 < ε ≤ ε₀ = γ (1 - s/2)`, on the good event, the comparisons, the
   packing bound and the anchored error bound hold (see `Riesz1.aPrioriGood_deterministic`).
3. (support) the cutoff is nonzero only on the good event.
4. (gradient) in the dimensionless gaps `z`, the cutoff `η̃ = gapCutoff` has zero derivative on
   `{η̃ = 1}`, has zero derivative at gap vectors with positive coordinates outside the good event,
   and its coordinate derivatives are bounded by `76 K^{2γ+ε}` almost everywhere, uniformly in `N`.
5. (bridging) `η_{ε,γ}(X) = η̃(z)` for `z_i = N (x_{i+1} - x_i)`.

The restriction to positive gap coordinates in part 4 is necessary: for `N = 2`, `K = 4`,
`ε = 1/2`, `γ = 0`, `s = 1/2` and `z = (-1/2, 6/5)`, the cutoff is `0.8 (z₀ + 1/2)²` near `z`,
so its derivative is `4/5` although `z` lies outside the good event. -/
theorem aPrioriGood_of_rigidity (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
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
    (∀ (N : ℕ+) (ε : ℝ), 0 ≤ ε → ∀ K : ℝ, 1 ≤ K →
      (∀ z : Fin (N : ℕ) → ℝ, gapCutoff N s K γ ε z = 1 →
        fderiv ℝ (gapCutoff N s K γ ε) z = 0) ∧
      (∀ z : Fin (N : ℕ) → ℝ, (∀ i : Fin (N : ℕ), 0 < z i) → z ∉ gapGoodEvent N s K γ ε →
        fderiv ℝ (gapCutoff N s K γ ε) z = 0) ∧
      (∀ i : Fin (N : ℕ), ∀ᵐ z ∂(volume : Measure (Fin (N : ℕ) → ℝ)),
        |fderiv ℝ (gapCutoff N s K γ ε) z (Pi.single i (1 : ℝ))| ≤ 76 * K ^ (2 * γ + ε))) ∧
    (∀ (N : ℕ+) (ε K : ℝ) (X : Configuration N),
      goodCutoff N s K γ ε X =
        gapCutoff N s K γ ε (fun i : Fin (N : ℕ) => gap X ((i : ℕ) : ℤ))) := by
  refine ⟨fun ε hε B hB => goodCutoff_prob_le_of_rigidity beta s hbeta hs hs1 hRig γ ε hγ hε B hB,
    aPrioriGood_deterministic hs hs1 (by linarith), fun N ε K hK X hX =>
      goodEvent_of_goodCutoff_ne_zero N hK hX,
    fun N ε hε K hK => ⟨fun z h => fderiv_gapCutoff_eq_zero_of_eq_one s K γ ε z h,
      fun z hpos hz => fderiv_gapCutoff_eq_zero_of_not_mem s K γ ε (by linarith) z hpos hz,
      fun i => gapCutoff_ae_fderiv_bound s K γ ε hK (by linarith) hs.le hε i⟩,
    fun N ε K X => goodCutoff_eq_gapCutoff s K γ ε X⟩

end Internal

end Riesz1

end
end
