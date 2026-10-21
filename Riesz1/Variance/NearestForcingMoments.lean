/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.NearestForcingBound
public import Riesz1.Rigidity.BlockMoments

/-!
# Unconditional convexification bounds

Lemma 5.2, first two claims, with the single-gap tail bound supplied by
the block-length moments of Lemma 4.2. The only external input is the Prékopa–Leindler
inequality `External.PrekopaLeindler`, passed as an explicit hypothesis.

* `gap_upper_tail` gives `P(gap_j > u) ≤ 3 exp (-c₀ u)` for every `N ≥ 2`, every label `j`, and
  every real `u`, with the absolute exponent `c₀ = blockMomentExponent`.
* `a_priori_convexity` applies the conditional bounds of `NearestForcingBound` with these
  absolute constants. Its constants `c, C` and threshold `K₀` depend only on `γ` and `ε`. They are
  independent of `P`, of the cutoff `θ`, of `N`, and of `K`.
-/

@[expose] public section

open MeasureTheory

namespace Riesz1

/-- The single-gap upper tail, from the block estimate with block length one. -/
theorem gap_upper_tail (hPL : External.PrekopaLeindler) (P : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (j : ℤ) (u : ℝ) :
    (gibbsMeasure P N).real {X | u < gap X j} ≤ 3 * Real.exp (-blockMomentExponent * u) := by
  have h := blockLength_upper_tail hPL P N hN j 1 one_pos u
  have he : {X : Configuration N | u < gap X j} =
      {X : Configuration N | ((1 : ℕ) : ℝ) * u < blockLength X j 1} := by
    ext X
    simp [blockLength_eq_sum]
  rw [he]
  exact h

/-- **Lemma 5.2, first two claims.** Let `0 ≤ γ` and `0 < ε`.
There are `c, C > 0` such that, for every `P`, every cutoff `θ`, every `N ≥ 2`, and every
`K ≥ 1`, the total variation between the Gibbs law and the nearest-neighbour law is at most
`C exp (-c K^ε)`. There is a threshold `K₀` such that, for every `P`, every cutoff `θ`, every
`N ≥ 2`, and every `K ≥ K₀` with `K ≥ 1`, the density `dQ/dP` is at most two almost everywhere.
The external hypothesis is the Prékopa–Leindler inequality `External.PrekopaLeindler`. -/
theorem a_priori_convexity (hPL : External.PrekopaLeindler) {γ ε : ℝ} (hγ : 0 ≤ γ)
    (hε : 0 < ε) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (P : Parameters) (θ : ℝ → ℝ), IsForcingCutoff θ →
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ K : ℝ, 1 ≤ K →
        totalVariation (gibbsMeasure P N) (nearestLaw P θ N K γ ε) ≤
          C * Real.exp (-c * K ^ ε)) ∧
    (∃ K₀ : ℝ, ∀ (P : Parameters) (θ : ℝ → ℝ), IsForcingCutoff θ →
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ K : ℝ, K₀ ≤ K → 1 ≤ K →
        ∀ᵐ X ∂(gibbsMeasure P N), (nearestLaw P θ N K γ ε).rnDeriv (gibbsMeasure P N) X ≤ 2) := by
  have ha : 0 < blockMomentExponent := blockMomentExponent_pos
  have hA : (0 : ℝ) < 3 := by norm_num
  have hc : 0 < nearestBoundc blockMomentExponent := half_pos ha
  have hC : 0 < nearestBoundC 3 blockMomentExponent γ ε := by
    unfold nearestBoundC
    exact mul_pos (mul_pos (by norm_num) hA) (Real.exp_pos _)
  obtain ⟨K₀, hK₀⟩ := eventually_mul_exp_lt_half (nearestBoundC 3 blockMomentExponent γ ε)
    (nearestBoundc blockMomentExponent) ε hc hε
  refine ⟨⟨nearestBoundc blockMomentExponent, nearestBoundC 3 blockMomentExponent γ ε, hc, hC,
    fun P θ hθ N hN K hK => ?_⟩, ⟨K₀, fun P θ hθ N hN K hK₀K hK => ?_⟩⟩
  · exact totalVariation_nearestLaw_le_exp hθ hK hγ hε ha hA.le
      (fun j u => gap_upper_tail hPL P N hN j u)
  · exact ae_rnDeriv_nearestLaw_le_two hθ hK hγ hε ha hA.le
      (fun j u => gap_upper_tail hPL P N hN j u) (hK₀ K hK₀K).le

end Riesz1

end
