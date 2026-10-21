/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriCutoffNormalizer
public import Riesz1.Variance.APrioriCutoffAnchored
public import Riesz1.Variance.NearestForcingMoments
public import Riesz1.Variance.APrioriGoodProbability
public import Riesz1.Rigidity.RigidityTheorem

/-!
# Uniform tilted-law cutoff probabilities

The probability step in the proof of Lemma 5.2, including bounded scales. Rigidity is
supplied by the Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler
inequality `External.PrekopaLeindler`, taken as hypotheses.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

/-- The normalizer is bounded below uniformly for every scale at least
one, by combining the bounded-scale result and the forcing tail. -/
theorem nearestNormalizer_uniform (hPL : External.PrekopaLeindler) (P : Parameters)
    (γ ε : ℝ) (hγ : 0 ≤ γ) (hε : 0 < ε) :
    ∃ z : ℝ, 0 < z ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (θ : ℝ → ℝ), IsForcingCutoff θ →
      ∀ K : ℝ, 1 ≤ K → z ≤ forcedNormalizer P N (nearestForcing θ N K γ ε) := by
  obtain ⟨K₀, hK₀⟩ := eventually_mul_exp_lt_half (nearestBoundC 3 blockMomentExponent γ ε)
    (nearestBoundc blockMomentExponent) ε (half_pos blockMomentExponent_pos) hε
  obtain ⟨z, hz, hsmall⟩ := nearestNormalizer_uniform_bounded P γ ε (max 1 K₀)
    hγ hε.le (le_max_left _ _)
  refine ⟨min z (1 / 2), lt_min hz (by norm_num), fun N hN θ hθ K hK => ?_⟩
  by_cases h : K ≤ max 1 K₀
  · exact (min_le_left _ _).trans (hsmall N hN θ hθ K hK h)
  · have hlarge : K₀ ≤ K := (le_max_right 1 K₀).trans (not_le.mp h).le
    have hprob := (nearestForcing_pos_le_exp (P := P) (N := N) hθ hK hγ hε
      blockMomentExponent_pos (by norm_num : (0 : ℝ) ≤ 3)
      (fun j u => gap_upper_tail hPL P N hN j u)).trans (hK₀ K hlarge).le
    exact (min_le_right _ _).trans (half_le_forcedNormalizer
      (measurable_nearestForcing hθ) (nearestForcing_nonneg hθ (by linarith)) hprob)

namespace Internal

/-- Uniform domination of the tilted configuration law by the Gibbs
law, also at bounded scales. -/
theorem nearestLaw_le_of_normalizer_lower (P : Parameters) {N : ℕ+} {θ : ℝ → ℝ}
    (hθ : IsForcingCutoff θ) {K γ ε z : ℝ} (hK : 0 < K) (hz : 0 < z)
    (hZ : z ≤ forcedNormalizer P N (nearestForcing θ N K γ ε)) :
    nearestLaw P θ N K γ ε ≤ ENNReal.ofReal z⁻¹ • gibbsMeasure P N := by
  rw [← withDensity_const]
  apply withDensity_mono
  apply ae_of_all
  intro X
  apply ENNReal.ofReal_le_ofReal
  have hnorm : 0 < forcedNormalizer P N (nearestForcing θ N K γ ε) := lt_of_lt_of_le hz hZ
  calc (forcedNormalizer P N (nearestForcing θ N K γ ε))⁻¹ *
        Real.exp (-P.val.1 * nearestForcing θ N K γ ε X)
      ≤ (forcedNormalizer P N (nearestForcing θ N K γ ε))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (exp_neg_mul_le_one (nearestForcing_nonneg hθ hK) X)
          (inv_nonneg.mpr hnorm.le)
    _ ≤ z⁻¹ := by rw [mul_one]; exact inv_anti₀ hz hZ

end Internal

/-- **Cutoff probability step in the proof of Lemma 5.2.** The cutoff
bad set has arbitrary polynomial decay under the actual tilted anchored
law. Only `External.BakryEmery` and `External.PrekopaLeindler` supply rigidity. -/
theorem nearestAnchored_cutoff_probability (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (P : Parameters) (γ ε : ℝ) (hγ : 1 < γ)
    (hε : 0 < ε) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (θ : ℝ → ℝ), IsForcingCutoff θ →
      ∀ K : ℝ, 1 ≤ K → K ≤ (N : ℕ) →
        nearestAnchoredLaw P θ N K γ ε {y | anchoredCutoff N P.val.2 K γ ε y ≠ 1} ≤
          ENNReal.ofReal (C * K ^ (-B)) := by
  obtain ⟨z, hz, hZ⟩ := nearestNormalizer_uniform hPL P γ ε (by linarith) hε
  obtain ⟨C, hC, hprob⟩ := Internal.goodCutoff_prob_le_of_rigidity P.val.1 P.val.2 P.2.1 P.2.2.1 P.2.2.2
    (Internal.rigidityConclusion_of_externals hBE hPL _ _ _ _ _) γ ε hγ hε B hB
  refine ⟨z⁻¹ * C, mul_pos (inv_pos.mpr hz) hC, fun N hN θ hθ K hK hKN => ?_⟩
  have hset : MeasurableSet {y | anchoredCutoff N P.val.2 K γ ε y ≠ 1} :=
    (measurable_anchoredCutoff _ _ _ _) (measurableSet_singleton 1) |>.compl
  rw [nearestAnchoredLaw, Measure.map_apply (measurable_anchorMap N) hset]
  have hpre : anchorMap N ⁻¹' {y | anchoredCutoff N P.val.2 K γ ε y ≠ 1} =
      {X | goodCutoff N P.val.2 K γ ε X ≠ 1} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, anchoredCutoff_anchorMap]
  rw [hpre]
  calc nearestLaw P θ N K γ ε {X | goodCutoff N P.val.2 K γ ε X ≠ 1}
      ≤ (ENNReal.ofReal z⁻¹ • gibbsMeasure P N) {X | goodCutoff N P.val.2 K γ ε X ≠ 1} :=
        Measure.le_iff'.mp (Internal.nearestLaw_le_of_normalizer_lower P hθ (by linarith) hz
          (hZ N hN θ hθ K hK)) _
    _ ≤ ENNReal.ofReal z⁻¹ * ENNReal.ofReal (C * K ^ (-B)) := by
      rw [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul_right (hprob hPL N hN K hK hKN) _
    _ = ENNReal.ofReal (z⁻¹ * C * K ^ (-B)) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hz.le), mul_assoc]

end Riesz1

end
