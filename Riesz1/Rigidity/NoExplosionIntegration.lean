/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.NoExplosionEndpoints

/-!
# Transport of weighted marginal integrals to Gibbs expectations

Internal integration helpers for the uniform inverse-moment argument.
Integrability of the weighted real density is established before any
real integral is transported. The test function need not be measurable
outside the support of the actual gap law.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- Internal transfer of a certified weighted density integral to the Gibbs law. -/
theorem gap_integral_transfer_internal (P : Parameters) (n : ℕ) (j : ℤ) (g : ℝ → ℝ)
    (hg : IntegrableOn (fun t => g t * gapMarginalProbabilityDensity P n t)
      (Ioo (0 : ℝ) (n + 2 : ℝ))) :
    Integrable (fun X : Configuration (n + 1).succPNat => g (gap X j))
      (gibbsMeasure P (n + 1).succPNat) ∧
    (∫ X : Configuration (n + 1).succPNat, g (gap X j) ∂gibbsMeasure P (n + 1).succPNat) =
      ∫ t in Ioo (0 : ℝ) (n + 2 : ℝ), g t * gapMarginalProbabilityDensity P n t := by
  have hm : Measurable (gapMarginalProbabilityDensity P n) :=
    ((measurable_gapOffsetMarginalDensity P n).comp
      (measurable_id.div_const (n + 2 : ℝ))).div_const (n + 2 : ℝ)
  have hn (t : ℝ) : 0 ≤ gapMarginalProbabilityDensity P n t :=
    div_nonneg (gapOffsetMarginalDensity_nonneg P n _) (by positivity)
  have hi : Integrable g ((gibbsMeasure P (n + 1).succPNat).map (fun X => gap X j)) := by
    rw [map_gap_gibbsMeasure_marginal_density P n j,
      integrable_withDensity_iff_integrable_smul' hm.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    change Integrable (fun t => g t * gapMarginalProbabilityDensity P n t)
      (volume.restrict (Ioo (0 : ℝ) (n + 2 : ℝ))) at hg
    exact hg.congr (ae_of_all _ fun t => by
      dsimp only
      rw [ENNReal.toReal_ofReal (hn t), smul_eq_mul, mul_comm])
  refine ⟨hi.comp_measurable (measurable_gap j), ?_⟩
  rw [← integral_map (measurable_gap j).aemeasurable hi.aestronglyMeasurable,
    map_gap_gibbsMeasure_marginal_density P n j,
    integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    dsimp only
    rw [ENNReal.toReal_ofReal (hn t), smul_eq_mul, mul_comm]

/-- Strict interior support, needed for the interval covariance signs. -/
theorem gap_lt_particle_number {N : ℕ+} (hN : 2 ≤ (N : ℕ)) (X : Configuration N) (j : ℤ) :
    gap X j < (N : ℝ) := by
  have h := cyclicLift_strictMono X (show j + 1 < j + ((N : ℕ) : ℤ) by omega)
  rw [cyclicLift_add_N] at h
  have hp : (0 : ℝ) < (N : ℕ) := by exact_mod_cast N.pos
  unfold gap
  nlinarith

end Riesz1

end
