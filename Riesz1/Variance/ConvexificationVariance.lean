/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.NearestForcingMoments
public import Riesz1.Variance.NearestForcing
public import Riesz1.ToMathlib.TotalVariation.VarianceTransfer
public import Riesz1.ToMathlib.TotalVariation.Map

/-!
# Variance transfer between the Gibbs law and the convexified law

Lemma 5.2, variance claim. For a real measurable `T` with `|T| ≤ M K^D`,
the variances of `T` under the Gibbs law and under the nearest-neighbour law `nearestLaw` differ by at
most `C M² K^{2D} exp (-c K^ε)`. The same holds for the anchored laws, which are the push-forwards
under `anchorMap`.

The proof combines the total-variation bound `a_priori_convexity` (its first claim) with the
general transfer `abs_variance_sub_le_of_abs_le`. The only external input is
`External.PrekopaLeindler`, passed explicitly.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Riesz1

/-- Total variation does not increase under a measurable push-forward of two finite measures. -/
theorem totalVariation_map_le {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : Ω → Ω'} (hf : Measurable f) :
    totalVariation (μ.map f) (ν.map f) ≤ totalVariation μ ν := by
  unfold totalVariation
  exact div_le_div_of_nonneg_right
    (ENNReal.toReal_mono (etvDist_ne_top μ ν) (etvDist_map_le_etvDist μ ν hf)) (by norm_num)

/-- The identity `K^{2D} = (K^D)²` for the real power, with `K ≥ 0`. -/
theorem rpow_two_mul_eq_sq_rpow {K : ℝ} (hK : 0 ≤ K) (D : ℝ) : K ^ (2 * D) = (K ^ D) ^ 2 := by
  rw [mul_comm, Real.rpow_mul hK, Real.rpow_two]

/-- **Lemma 5.2, variance claim.** Let `0 ≤ γ` and `0 < ε`. There are
`c, C > 0`, depending only on `γ` and `ε`, such that for every `P`, every cutoff `θ`, every `N ≥ 2`,
every `K ≥ 1`, every `M ≥ 0` and `D`, and every measurable `T` with `|T| ≤ M K^D`:
the variances of `T` under the Gibbs law and under `nearestLaw` differ by at most
`C M² K^{2D} exp (-c K^ε)`. The same holds for the anchored laws. The external hypothesis is
`External.PrekopaLeindler`. -/
theorem variance_transfer (hPL : External.PrekopaLeindler) {γ ε : ℝ} (hγ : 0 ≤ γ) (hε : 0 < ε) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (P : Parameters) (θ : ℝ → ℝ), IsForcingCutoff θ →
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (K M D : ℝ), 1 ≤ K → 0 ≤ M →
        (∀ T : Configuration N → ℝ, Measurable T → (∀ X, |T X| ≤ M * K ^ D) →
          |variance T (gibbsMeasure P N) - variance T (nearestLaw P θ N K γ ε)| ≤
            C * M ^ 2 * K ^ (2 * D) * Real.exp (-c * K ^ ε)) ∧
        (∀ T : (Fin ((N : ℕ) - 1) → ℝ) → ℝ, Measurable T → (∀ y, |T y| ≤ M * K ^ D) →
          |variance T ((gibbsMeasure P N).map (anchorMap N)) -
              variance T (nearestAnchoredLaw P θ N K γ ε)| ≤
            C * M ^ 2 * K ^ (2 * D) * Real.exp (-c * K ^ ε)) := by
  obtain ⟨⟨c, C, hc, hC, hTV⟩, -⟩ := a_priori_convexity hPL hγ hε
  refine ⟨c, 6 * C, hc, by linarith, fun P θ hθ N hN K M D hK hM => ⟨fun T hT hTb => ?_,
    fun T hT hTb => ?_⟩⟩
  · have := isProbabilityMeasure_gibbsMeasure P N
    have := isProbabilityMeasure_nearestLaw (P := P) (θ := θ) (N := N) (K := K) (γ := γ)
      (ε := ε) hθ (by linarith)
    have hKpos : 0 ≤ K ^ D := Real.rpow_nonneg (by linarith) D
    have hB : 0 ≤ M * K ^ D := mul_nonneg hM hKpos
    have hvar := abs_variance_sub_le_of_abs_le (gibbsMeasure P N) (nearestLaw P θ N K γ ε) hT hB hTb
    have htv := hTV P θ hθ N hN K hK
    calc |variance T (gibbsMeasure P N) - variance T (nearestLaw P θ N K γ ε)|
        ≤ 6 * (M * K ^ D) ^ 2 * totalVariation (gibbsMeasure P N) (nearestLaw P θ N K γ ε) := hvar
      _ ≤ 6 * (M * K ^ D) ^ 2 * (C * Real.exp (-c * K ^ ε)) :=
          mul_le_mul_of_nonneg_left htv (by positivity)
      _ = 6 * C * M ^ 2 * K ^ (2 * D) * Real.exp (-c * K ^ ε) := by
          rw [rpow_two_mul_eq_sq_rpow (by linarith) D]
          ring
  · have := isProbabilityMeasure_gibbsMeasure P N
    have := isProbabilityMeasure_nearestLaw (P := P) (θ := θ) (N := N) (K := K) (γ := γ)
      (ε := ε) hθ (by linarith)
    have hKpos : 0 ≤ K ^ D := Real.rpow_nonneg (by linarith) D
    have hB : 0 ≤ M * K ^ D := mul_nonneg hM hKpos
    have hvar := abs_variance_sub_le_of_abs_le ((gibbsMeasure P N).map (anchorMap N))
      ((nearestLaw P θ N K γ ε).map (anchorMap N)) hT hB hTb
    have htv := hTV P θ hθ N hN K hK
    have hmap := totalVariation_map_le (gibbsMeasure P N) (nearestLaw P θ N K γ ε)
      (measurable_anchorMap N)
    unfold nearestAnchoredLaw
    calc |variance T ((gibbsMeasure P N).map (anchorMap N)) -
          variance T ((nearestLaw P θ N K γ ε).map (anchorMap N))|
        ≤ 6 * (M * K ^ D) ^ 2 * totalVariation ((gibbsMeasure P N).map (anchorMap N))
            ((nearestLaw P θ N K γ ε).map (anchorMap N)) := hvar
      _ ≤ 6 * (M * K ^ D) ^ 2 * totalVariation (gibbsMeasure P N) (nearestLaw P θ N K γ ε) :=
          mul_le_mul_of_nonneg_left hmap (by positivity)
      _ ≤ 6 * (M * K ^ D) ^ 2 * (C * Real.exp (-c * K ^ ε)) :=
          mul_le_mul_of_nonneg_left htv (by positivity)
      _ = 6 * C * M ^ 2 * K ^ (2 * D) * Real.exp (-c * K ^ ε) := by
          rw [rpow_two_mul_eq_sq_rpow (by linarith) D]
          ring

end Riesz1

end
