/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriConclusion
public import Riesz1.Gibbs.FluctuationMoments
public import Riesz1.Variance.LoopForce

/-!
# The scaled fluctuation of `q_N` equals the plain sum (Theorem 3)

The variance in Theorem 3 is that of `Fluct_N[q_N(ℓ_N⁻¹ ·)]`, a fluctuation of a
unit-circle function. Here `q_N` lives on the circle `Circle (observationLength ℓ)` of length
`ℓ⁻¹`, and `x ↦ q_N(x/ℓ)` is a function on the unit circle. Lemma `plainSum` of
Lemma 5.2 sums `q_N` over the particles directly.

This file identifies the two:

* `scaledLift ℓ f` is the unit-circle function `x ↦ f(x/ℓ)` for `f` on `ℓ⁻¹ 𝕋`.
* `linearStatistic (scaledLift ℓ f) X = plainSum ℓ N f X`.
* the fluctuation differs from `plainSum` by the constant `N ∫ scaledLift`, so the two variances
  agree (`variance` depends only on the centred integrand).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1.Internal

/-- The unit-circle lift of `x ↦ f(x/ℓ)`, for `f` on the circle `Circle (observationLength ℓ)`
of length `ℓ⁻¹`. The map `t ↦ t/ℓ` carries the unit period to the period `ℓ⁻¹`, so the
function descends to `UnitAddCircle`. -/
def scaledLift (ℓ : Scale) (f : Circle (observationLength ℓ) → ℝ) : UnitAddCircle → ℝ :=
  (show Function.Periodic
      (fun t : ℝ => f (((t / ℓ.val : ℝ)) : Circle (observationLength ℓ))) 1 from
    fun t => by
      have h : (t + 1) / ℓ.val = t / ℓ.val + (observationLength ℓ).val := by
        simp only [observationLength, add_div, one_div]
      simp only [h]
      rw [AddCircle.coe_add_period]).lift

lemma scaledLift_coe (ℓ : Scale) (f : Circle (observationLength ℓ) → ℝ) (t : ℝ) :
    scaledLift ℓ f (t : UnitAddCircle) = f (((t / ℓ.val : ℝ)) : Circle (observationLength ℓ)) :=
  Function.Periodic.lift_coe _ t

/-- The unit-circle lift of a continuous `f` is continuous. -/
lemma continuous_scaledLift (ℓ : Scale) {f : Circle (observationLength ℓ) → ℝ}
    (hf : Continuous f) : Continuous (scaledLift ℓ f) := by
  unfold scaledLift
  refine Riesz1.continuous_lift_periodic ?_ _
  refine hf.comp ?_
  exact (AddCircle.continuous_mk' _).comp (continuous_id.div_const _)

/-- The unit-circle lift of a continuous `f` is square integrable. -/
lemma memLp_scaledLift (ℓ : Scale) {f : Circle (observationLength ℓ) → ℝ}
    (hf : Continuous f) : MemLp (scaledLift ℓ f) 2 volume := by
  have hc := continuous_scaledLift ℓ hf
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine MemLp.of_bound hc.aestronglyMeasurable C (ae_of_all _ fun x => ?_)
  simpa using hC x (Set.mem_univ x)

/-- The linear statistic of the scaled lift is the plain sum of `f` over the particles. -/
lemma linearStatistic_scaledLift (ℓ : Scale) (N : ℕ+) (f : Circle (observationLength ℓ) → ℝ)
    (X : Configuration N) :
    linearStatistic (scaledLift ℓ f) X = plainSum ℓ N f X := by
  unfold linearStatistic plainSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [scaledLift_coe]

/-- The fluctuation of the scaled lift is the plain sum minus the constant `N ∫ scaledLift`. -/
lemma fluctuation_scaledLift_eq (ℓ : Scale) (N : ℕ+) (f : Circle (observationLength ℓ) → ℝ)
    {hint : Integrable (scaledLift ℓ f) volume} (X : Configuration N) :
    fluctuation ⟨scaledLift ℓ f, hint⟩ X =
      plainSum ℓ N f X - (N : ℝ) * ∫ x, scaledLift ℓ f x := by
  unfold fluctuation
  rw [linearStatistic_scaledLift]

/-- The plain sum `Σ_i f(x_i/ℓ)` is integrable for the Gibbs law when `f` is continuous. -/
lemma integrable_plainSum (P : Parameters) (ℓ : Scale) (N : ℕ+)
    {f : Circle (observationLength ℓ) → ℝ} (hf : Continuous f) :
    Integrable (plainSum ℓ N f) (gibbsMeasure P N) := by
  have h := integrable_linearStatistic P N (memLp_scaledLift ℓ hf)
  have heq : plainSum ℓ N f = fun X => linearStatistic (scaledLift ℓ f) X :=
    funext fun X => (linearStatistic_scaledLift ℓ N f X).symm
  rw [heq]
  exact h

/-- **Variance identification.** For a continuous `f` on `ℓ⁻¹ 𝕋`, the variance of the
fluctuation of its unit-circle lift under the Gibbs law equals the variance of the plain sum
`Σ_i f(x_i/ℓ)`. The fluctuation is integrable by hypothesis `h1`. -/
lemma variance_fluctuation_scaledLift_eq (P : Parameters) (ℓ : Scale) (N : ℕ+)
    {f : Circle (observationLength ℓ) → ℝ} (hf : Continuous f)
    (hint : Integrable (scaledLift ℓ f) volume)
    (h1 : Integrable (fun X => fluctuation ⟨scaledLift ℓ f, hint⟩ X) (gibbsMeasure P N)) :
    variance (gibbsMeasure P N) (fun X => fluctuation ⟨scaledLift ℓ f, hint⟩ X) h1 =
      variance (gibbsMeasure P N) (plainSum ℓ N f) (integrable_plainSum P ℓ N hf) := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  -- The fluctuation is the plain sum shifted by a constant, so its mean is shifted the same way.
  have hmean : ∫ Y, fluctuation ⟨scaledLift ℓ f, hint⟩ Y ∂(gibbsMeasure P N) =
      ∫ Y, plainSum ℓ N f Y ∂(gibbsMeasure P N) - (N : ℝ) * ∫ x, scaledLift ℓ f x := by
    simp_rw [fluctuation_scaledLift_eq ℓ N f]
    rw [integral_sub (integrable_plainSum P ℓ N hf) (integrable_const _), integral_const]
    simp
  unfold variance
  refine lintegral_congr fun X => ?_
  dsimp only
  rw [fluctuation_scaledLift_eq ℓ N f, hmean]
  congr 2
  ring

end Riesz1.Internal

end
end
