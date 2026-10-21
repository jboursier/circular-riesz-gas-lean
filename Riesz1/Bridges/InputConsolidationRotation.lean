/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscRotation
public import Riesz1.Gibbs.WellDefined
public import Riesz1.Gibbs.UniformMarginals
public import Riesz1.Variance.APrioriConclusion
public import Riesz1.ToMathlib.VarianceLawTransfer

/-!
# Translating the observation circle: the plain sum has the law of its translate

The plain sum `∑ᵢ f (xᵢ / ℓ)` of a function `f` on the observation circle `ℓ⁻¹ 𝕋` and the plain
sum of the translate `z ↦ f (z + c)` have the same law under the Gibbs measure, for every real
`c`. This is what lets the constant of Lemma 5.2 be chosen before the centre.

The proof writes both sums as linear statistics on the unit circle. The rescaling
`observationRescale ℓ : 𝕋 → ℓ⁻¹ 𝕋`, `x ↦ x / ℓ`, is an isomorphism of additive groups. A rotation
`θ` of the unit circle with `observationRescale ℓ θ = -c` carries one sum to the other. Then
`Riesz1.integral_rotate_linearStatistic` gives equal integrals of every measurable test function,
and `Riesz1.map_eq_of_integral_eq` turns that into equality of the laws.

Main results:
* `observationRescale_coe`: the rescaling sends the class of `x` to the class of `x / ℓ`.
* `measurable_plainSum`: the plain sums are measurable.
* `map_plainSum_eq_map_translate`: the laws of `plainSum f` and of its translate agree.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1.Internal

/-- The rescaling `x ↦ x / ℓ` from the unit circle to the observation circle of `ℓ`, as an
isomorphism of additive groups. -/
def observationRescale (ℓ : Scale) : UnitAddCircle ≃+ Circle (observationLength ℓ) :=
  AddCircle.equivAddCircle 1 (observationLength ℓ).val one_ne_zero
    (observationLength ℓ).property.ne'

/-- The rescaling sends the class of `x` to the class of `x / ℓ`. -/
theorem observationRescale_coe (ℓ : Scale) (x : ℝ) :
    observationRescale ℓ (x : UnitAddCircle) =
      ((x / ℓ.val : ℝ) : Circle (observationLength ℓ)) := by
  unfold observationRescale
  rw [AddCircle.equivAddCircle_apply_mk]
  congr 1
  simp [observationLength, div_eq_mul_inv]

/-- The rescaling is continuous, as the restriction of a homeomorphism. -/
theorem continuous_observationRescale (ℓ : Scale) : Continuous (observationRescale ℓ) :=
  (AddCircle.homeomorphAddCircle (1 : ℝ) (observationLength ℓ).val one_ne_zero
    (observationLength ℓ).property.ne').continuous

/-- The coordinate `t ↦ (t : AddCircle L)` is measurable. -/
theorem measurable_coe_addCircle (L : ℝ) : Measurable fun t : ℝ => (t : AddCircle L) := by
  fun_prop

/-- The plain sum `∑ᵢ f (xᵢ / ℓ)` is measurable on the configuration space when `f` is. -/
theorem measurable_plainSum (ℓ : Scale) (N : ℕ+) {f : Circle (observationLength ℓ) → ℝ}
    (hf : Measurable f) : Measurable (plainSum ℓ N f) := by
  unfold plainSum
  refine Finset.measurable_sum _ fun i _ => ?_
  have hi : Measurable fun X : Configuration N => X.val i :=
    (measurable_pi_apply i).comp measurable_subtype_coe
  exact hf.comp ((measurable_coe_addCircle _).comp (hi.div_const ℓ.val))

/-- **Translation of the observation circle.** For a continuous `f` on the observation circle
`ℓ⁻¹ 𝕋`, and every real `c`, the plain sum of `f` and the plain sum of `z ↦ f (z + c)` have the
same law under the Gibbs measure of `N` particles. -/
theorem map_plainSum_eq_map_translate (P : Parameters) (N : ℕ+) (ℓ : Scale)
    {f : Circle (observationLength ℓ) → ℝ} (hf : Continuous f) (c : ℝ) :
    (gibbsMeasure P N).map (plainSum ℓ N f) =
      (gibbsMeasure P N).map (plainSum ℓ N fun z => f (z + (c : Circle (observationLength ℓ)))) := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  -- The test function on the unit circle. Its linear statistic is the plain sum of the translate.
  have hG : Continuous fun y : UnitAddCircle =>
      f (observationRescale ℓ y + (c : Circle (observationLength ℓ))) :=
    hf.comp ((continuous_observationRescale ℓ).add continuous_const)
  -- The rotation parameter: it is carried by the rescaling to `-c`.
  obtain ⟨θ, hθ⟩ : ∃ θ : UnitAddCircle,
      observationRescale ℓ θ = ((-c : ℝ) : Circle (observationLength ℓ)) :=
    ⟨(observationRescale ℓ).symm _, (observationRescale ℓ).apply_symm_apply _⟩
  -- Moving the translate back by `c` restores the point `[x / ℓ]`.
  have hcancel : ∀ a : ℝ, (a : Circle (observationLength ℓ)) +
      ((-c : ℝ) : Circle (observationLength ℓ)) + (c : Circle (observationLength ℓ)) =
        (a : Circle (observationLength ℓ)) := by
    intro a
    rw [← AddCircle.coe_add, ← AddCircle.coe_add]
    congr 1
    ring
  -- The linear statistic of the translate is the plain sum of the translate.
  have hpt1 : ∀ X : Configuration N,
      linearStatistic (fun x : UnitAddCircle =>
        f (observationRescale ℓ x + (c : Circle (observationLength ℓ)))) X =
        plainSum ℓ N (fun z => f (z + (c : Circle (observationLength ℓ)))) X := by
    intro X
    simp only [linearStatistic, plainSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [observationRescale_coe]
  -- The rotated linear statistic is the plain sum of `f`.
  have hpt2 : ∀ X : Configuration N,
      linearStatistic (fun x : UnitAddCircle =>
        f (observationRescale ℓ (x + θ) + (c : Circle (observationLength ℓ)))) X =
        plainSum ℓ N f X := by
    intro X
    simp only [linearStatistic, plainSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, hθ, observationRescale_coe, hcancel]
  -- Equal integrals of every test function, from the rotation invariance of the Gibbs law.
  have hint : ∀ Φ : ℝ → ℝ, Measurable Φ →
      ∫ X, Φ (plainSum ℓ N f X) ∂(gibbsMeasure P N) =
        ∫ X, Φ (plainSum ℓ N (fun z => f (z + (c : Circle (observationLength ℓ)))) X)
          ∂(gibbsMeasure P N) := by
    intro Φ hΦ
    have key := integral_rotate_linearStatistic P N
      (fun y : UnitAddCircle => f (observationRescale ℓ y + (c : Circle (observationLength ℓ))))
      θ Φ hΦ hG.measurable
    simp only [hpt1, hpt2] at key
    exact key
  have hfc : Continuous fun z : Circle (observationLength ℓ) =>
      f (z + (c : Circle (observationLength ℓ))) :=
    hf.comp (continuous_id.add continuous_const)
  exact map_eq_of_integral_eq (measurable_plainSum ℓ N hf.measurable)
    (measurable_plainSum ℓ N hfc.measurable) hint

end Riesz1.Internal

end
end
