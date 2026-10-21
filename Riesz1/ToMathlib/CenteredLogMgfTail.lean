/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CenteredConcentration
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Two-sided tail from a centered logarithmic moment bound

Let `Y` be a real random variable on a probability space with `log E exp(t Y) ≤ K t²` for every
real `t`, where `K > 0`. Then `P(v ≤ |Y|) ≤ 2 exp(-v²/(4K))` for every `v ≥ 0`. This is the Chernoff
bound with the optimized coefficient. The proof passes to the sub-Gaussian tail
`Riesz1.Internal.subgaussian_two_sided` with sub-Gaussian constant `2K`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Riesz1

/-- **Two-sided Chernoff tail.** On a probability space, a real variable `Y` with
`log E exp(t Y) ≤ K t²` for every `t`, where `K > 0`, satisfies
`P(v ≤ |Y|) ≤ 2 exp(-v²/(4K))` for every `v ≥ 0`. -/
theorem measureReal_abs_le_of_log_mgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ} {K : ℝ} (hK : 0 < K)
    (hI : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Y ω)) μ)
    (hlog : ∀ t : ℝ, Real.log (∫ ω, Real.exp (t * Y ω) ∂μ) ≤ K * t ^ 2)
    {v : ℝ} (hv : 0 ≤ v) :
    μ.real {ω | v ≤ |Y ω|} ≤ 2 * Real.exp (-v ^ 2 / (4 * K)) := by
  have hK2 : (0 : ℝ) ≤ 2 * K := by linarith
  have hsub : HasSubgaussianMGF Y (Real.toNNReal (2 * K)) μ := by
    refine ⟨hI, fun t => ?_⟩
    have hp : 0 < ∫ ω, Real.exp (t * Y ω) ∂μ := integral_exp_pos (hI t)
    have hb := (Real.log_le_iff_le_exp hp).mp (hlog t)
    change (∫ ω, Real.exp (t * Y ω) ∂μ) ≤
      Real.exp (((Real.toNNReal (2 * K) : NNReal) : ℝ) * t ^ 2 / 2)
    rw [Real.coe_toNNReal _ hK2]
    refine hb.trans (Real.exp_le_exp.mpr (le_of_eq ?_))
    ring
  have h := Internal.subgaussian_two_sided μ hsub hv
  have he : -v ^ 2 / (2 * ((Real.toNNReal (2 * K) : NNReal) : ℝ)) = -v ^ 2 / (4 * K) := by
    rw [Real.coe_toNNReal _ hK2]
    ring
  rw [he] at h
  exact h

end Riesz1

end
