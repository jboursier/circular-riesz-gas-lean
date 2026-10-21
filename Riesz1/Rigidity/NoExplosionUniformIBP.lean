/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.NoExplosionIntegration
public import Riesz1.Rigidity.NoExplosionMarginalPotential
public import Riesz1.Rigidity.NoExplosionAlgebra
public import Riesz1.Rigidity.GapLawMoments

/-!
# Single-gap integration by parts under the Gibbs law

The three identities in Lemma 4.5, with integrability
certificates for the actual Gibbs expectations.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- Internal transfer of all three IBP identities. The potential is written as
its explicit logarithmic expression. Only its values on the open support enter. -/
theorem gap_ibp_gibbs_internal (hPL : External.PrekopaLeindler)
    (P : Parameters) (n : ℕ) (j : ℤ) {q : ℝ} (hq : 0 < q) :
    let V := fun t : ℝ => -Real.log (gapMarginalProbabilityDensity P n t) -
      2 * P.val.1 * t ^ (-P.val.2)
    let w := fun t : ℝ => derivWithin V (Ioi t) t - 2 * P.val.1 * P.val.2 * t ^ (-P.val.2 - 1)
    let μ := gibbsMeasure P (n + 1).succPNat
    Integrable (fun X => w (gap X j)) μ ∧
    Integrable (fun X => gap X j * w (gap X j)) μ ∧
    Integrable (fun X => gap X j ^ (-q) * w (gap X j)) μ ∧
    (∫ X, w (gap X j) ∂μ) = 0 ∧
    (∫ X, gap X j * w (gap X j) ∂μ) = 1 ∧
    (∫ X, gap X j ^ (-q) * w (gap X j) ∂μ) =
      -q * ∫ X, gap X j ^ (-(q + 1)) ∂μ := by
  dsimp only
  let V := fun t : ℝ => -Real.log (gapMarginalProbabilityDensity P n t) -
    2 * P.val.1 * t ^ (-P.val.2)
  let w := fun t : ℝ => derivWithin V (Ioi t) t - 2 * P.val.1 * P.val.2 * t ^ (-P.val.2 - 1)
  have hV := convexOn_gapPotential hPL P n
  have hf : ∀ t ∈ Ioo (0 : ℝ) (n + 2 : ℝ), gapMarginalProbabilityDensity P n t =
      Real.exp (-2 * P.val.1 * t ^ (-P.val.2) - V t) := by
    intro t ht
    exact gapMarginalProbabilityDensity_eq_exp_potential P n ⟨t, ht⟩
  obtain ⟨C, _, hC⟩ := gapMarginalProbabilityDensity_endpoint_bound P n
  have h1 := gap_ibp_one (q := q) (by positivity : (0 : ℝ) < n + 2) P.2.1 P.2.2.1 hV hf hC hq
  have h2 := gap_ibp_id (q := q) (by positivity : (0 : ℝ) < n + 2) P.2.1 P.2.2.1 hV hf hC hq
  have h3 := gap_ibp_pow (by positivity : (0 : ℝ) < n + 2) P.2.1 P.2.2.1 hV hf hC hq
  obtain ⟨hi1, he1⟩ := gap_integral_transfer_internal P n j w (by simpa only [one_mul] using h1.2.1)
  obtain ⟨hi2, he2⟩ := gap_integral_transfer_internal P n j (fun t => t * w t) h2.2.1
  obtain ⟨hi3, he3⟩ := gap_integral_transfer_internal P n j (fun t => t ^ (-q) * w t) h3.2.1
  obtain ⟨_, he0⟩ := gap_integral_transfer_internal P n j (fun _ => (1 : ℝ)) h2.1
  obtain ⟨_, hep⟩ := gap_integral_transfer_internal P n j (fun t => -q * t ^ (-q - 1)) h3.1
  let := (modelWellDefined P (n + 1).succPNat).2.2
  refine ⟨hi1, hi2, hi3, ?_, ?_, ?_⟩
  · rw [he1]
    simpa only [zero_mul, one_mul, integral_zero] using h1.2.2.symm
  · rw [he2, ← h2.2.2, ← he0]
    rw [integral_const, probReal_univ, one_smul]
  · rw [he3, ← h3.2.2, ← hep, integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun X => by rw [show -q - 1 = -(q + 1) by ring]

end Riesz1

end
