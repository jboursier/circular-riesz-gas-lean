/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.IdentityIBP
public import Riesz1.Gibbs.FluctuationMoments
public import Riesz1.Variance.LoopIBPPeriodic
public import Mathlib.Analysis.Calculus.Deriv.Comp
import all Riesz1.Variance.LoopForce
import all Riesz1.Variance.LoopScale
import all Riesz1.Variance.LoopIBPUniform

/-!
# The statistic `G_N` and its pairing with the potential

Facts about the statistic `G = K^{-s/2} Fluct_N[R(·/ℓ)]` used in
Theorem 3, for a smooth one-periodic profile `R`:

* `G` is torus-smooth, so clause 2 of Proposition 5.5 applies to `u ∘ G`.
* the gradient pairing `∇G·∇Φ` with the potential `Φ = Φ_{ψ,K^{-1+s/2}}` equals
  `K⁻¹ Σₖ ψ(xₖ/ℓ) R'(xₖ/ℓ)`, the sum `Σᵢ q_N(xᵢ/ℓ)`, up to the factor `K⁻¹`.
* the pairing density is bounded, and `G` has mean zero and is integrable on the Gibbs measure.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The scaled fluctuation is unchanged when one coordinate shifts by the period one. -/
lemma fluctIntegral_update_periodic {N : ℕ} {f : ℝ → ℝ} (hper : Function.Periodic f 1)
    (k : Fin N) (x : Fin N → ℝ) :
    fluctIntegral f N (Function.update x k (x k + 1)) = fluctIntegral f N x := by
  unfold fluctIntegral
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hik : i = k
  · subst hik
    rw [Function.update_self]
    exact hper (x i)
  · rw [Function.update_of_ne hik]

/-- The statistic `c · Fluct_N[f]` of a smooth one-periodic `f` is torus-smooth. -/
lemma isTorusSmooth_scaled_fluctIntegral {N : ℕ} (c : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f 1) : IsTorusSmooth (fun x : Fin N → ℝ => c * fluctIntegral f N x) := by
  refine ⟨?_, fun k x => ?_⟩
  · unfold fluctIntegral
    exact contDiff_const.mul ((ContDiff.sum fun i _ => hf.comp (by fun_prop)).sub
      contDiff_const)
  · simp only [fluctIntegral_update_periodic hper k x]

/-- The gradient pairing of the statistic `c · Fluct_N[R(·/ℓ)]` with the potential
`Φ = a ℓ² Σᵢ ∫₀^{xᵢ/ℓ} Ψ` equals `K⁻¹ Σₖ Ψ(xₖ/ℓ) R'(xₖ/ℓ)` when `c = K^{-s/2}` and
`a = K^{-1+s/2}`. -/
lemma gradDotPotential_scaled {N : ℕ} {R Ψ : ℝ → ℝ} (hR : Differentiable ℝ R)
    (hΨ : Continuous Ψ) {ℓ : ℝ} (hℓ : 0 < ℓ) {K s : ℝ} (hK : 0 < K) (x : Fin N → ℝ) :
    gradDotPotential (fun y => K ^ (-(s / 2)) * fluctIntegral (fun u => R (u / ℓ)) N y)
      (fun y => K ^ (-1 + s / 2) * ℓ ^ 2 * ∑ i : Fin N, ∫ u in (0 : ℝ)..(y i / ℓ), Ψ u) x
      = K⁻¹ * ∑ k : Fin N, Ψ (x k / ℓ) * deriv R (x k / ℓ) := by
  unfold gradDotPotential
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [partialDeriv_mul_partialDeriv_scaled hR hΨ hℓ _ _ k x, ← mul_assoc,
    rpow_cltK_pair K s hK]
  ring

/-- The gradient pairing of the statistic `c · Fluct_N[R(·/ℓ)]` with the loop potential
`Φ = loopScalePotential ℓ a Ψ N`, for a `LoopScaleProfile` `Ψ`, equals `K⁻¹ Σₖ Ψ(xₖ/ℓ) R'(xₖ/ℓ)`. -/
lemma gradDotPotential_loopScale {N : ℕ} {R : ℝ → ℝ} (hR : Differentiable ℝ R)
    {ℓ : Ioc (0 : ℝ) 1} (Ψ : LoopScaleProfile ℓ.val) (hΨ : Continuous Ψ.val) {K s : ℝ}
    (hK : 0 < K) (x : Fin N → ℝ) :
    gradDotPotential (fun y => K ^ (-(s / 2)) * fluctIntegral (fun u => R (u / ℓ.val)) N y)
      (loopScalePotential ℓ (K ^ (-1 + s / 2)) Ψ N) x
      = K⁻¹ * ∑ k : Fin N, Ψ.val (x k / ℓ.val) * deriv R (x k / ℓ.val) := by
  unfold loopScalePotential
  exact gradDotPotential_scaled hR hΨ ℓ.property.1 hK x

/-- The pairing density `v ↦ Ψ(v) R'(v)` is continuous and `ℓ⁻¹`-periodic, hence bounded. So the
coordinate sum is bounded uniformly in `x`. -/
lemma abs_sum_pairing_le {N : ℕ} {R Ψ : ℝ → ℝ} (hR : ContDiff ℝ 1 R) (hΨ : Continuous Ψ)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hRp : Function.Periodic R ℓ⁻¹) (hΨp : Function.Periodic Ψ ℓ⁻¹) :
    ∃ C : ℝ, ∀ x : Fin N → ℝ, |∑ k : Fin N, Ψ (x k / ℓ) * deriv R (x k / ℓ)| ≤ C := by
  have hRc : Continuous (deriv R) := hR.continuous_deriv (by norm_num)
  have hdper : Function.Periodic (deriv R) ℓ⁻¹ := by
    intro v
    rw [← deriv_comp_add_const]
    congr 1
    funext w
    exact hRp w
  have hq : Continuous (fun v => Ψ v * deriv R v) := hΨ.mul hRc
  have hqp : Function.Periodic (fun v => Ψ v * deriv R v) ℓ⁻¹ := by
    intro v
    simp only [hΨp v, hdper v]
  obtain ⟨C0, hC0⟩ := isBounded_iff_forall_norm_le.mp
    (hqp.isBounded_of_continuous (inv_ne_zero hℓ.ne') hq)
  refine ⟨N * C0, fun x => ?_⟩
  have hbd : ∀ k : Fin N, |Ψ (x k / ℓ) * deriv R (x k / ℓ)| ≤ C0 := fun k => by
    have := hC0 _ ⟨x k / ℓ, rfl⟩
    simpa [Real.norm_eq_abs] using this
  calc |∑ k : Fin N, Ψ (x k / ℓ) * deriv R (x k / ℓ)|
      ≤ ∑ k : Fin N, |Ψ (x k / ℓ) * deriv R (x k / ℓ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin N, C0 := Finset.sum_le_sum fun k _ => hbd k
    _ = N * C0 := by simp

/-- A continuous one-periodic profile has a square-integrable lift to the unit circle. -/
lemma memLp_lift_of_continuous {R : ℝ → ℝ} (hR : Continuous R) (hper : Function.Periodic R 1) :
    MemLp (hper.lift : UnitAddCircle → ℝ) 2 volume := by
  have hc := Riesz1.continuous_lift_periodic hR hper
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have hb : MemLp (hper.lift : UnitAddCircle → ℝ) ⊤ volume :=
    memLp_top_of_bound hc.aestronglyMeasurable C
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x (mem_univ x))
  exact hb.mono_exponent le_top

/-- The scaled fluctuation is integrable on the Gibbs measure. -/
lemma integrable_fluctIntegral (P : Parameters) (N : ℕ+) {R : ℝ → ℝ} (hR : Continuous R)
    (hper : Function.Periodic R 1) :
    Integrable (fun X : Configuration N => fluctIntegral R N X.val) (gibbsMeasure P N) := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hmem := memLp_lift_of_continuous hR hper
  have h : (fun X : Configuration N => fluctIntegral R N X.val)
      = fun X => fluctuation ⟨hper.lift, hmem.integrable one_le_two⟩ X :=
    funext fun X => (fluctuation_eq_fluctIntegral hR hper X).symm
  rw [h]
  unfold fluctuation
  exact ((memLp_linearStatistic P N hmem).integrable one_le_two).sub (integrable_const _)

/-- The scaled fluctuation has mean zero on the Gibbs measure. -/
lemma integral_fluctIntegral_eq_zero (P : Parameters) (N : ℕ+) {R : ℝ → ℝ} (hR : Continuous R)
    (hper : Function.Periodic R 1) :
    ∫ X : Configuration N, fluctIntegral R N X.val ∂(gibbsMeasure P N) = 0 := by
  have hmem := memLp_lift_of_continuous hR hper
  have h : (fun X : Configuration N => fluctIntegral R N X.val)
      = fun X => fluctuation ⟨hper.lift, hmem.integrable one_le_two⟩ X :=
    funext fun X => (fluctuation_eq_fluctIntegral hR hper X).symm
  rw [h]
  exact integral_fluctuation_eq_zero P N hmem

end Riesz1

end
