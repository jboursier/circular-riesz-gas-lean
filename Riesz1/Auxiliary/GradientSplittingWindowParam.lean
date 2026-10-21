/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingWindowKernel

/-!
# Regularity of the divided difference in the segment direction

For a smooth real `ψ` and `x ∈ ℝ`, the map `v ↦ Z(x, x + v) = ∫_0^1 ψ'((x + θ v)/ℓ) dθ` is `C¹`
(with the second argument at the lift `x + v`). This is the coefficient
needed to apply the truncated integration by parts of `GradientSplittingWindowPVLimit` to the
principal values of `Z_x h` and `Z h'`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The divided difference `Z(x, x + v)` is `C¹` in the increment `v`. -/
lemma contDiff_one_gradZ_shift {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : ℓ ≠ 0) (x : ℝ) :
    ContDiff ℝ 1 (fun v : ℝ => gradZ ψ ℓ x (x + v)) := by
  have hψd : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.1 hψ).2
  have hc1 : Continuous (deriv ψ) := hψd.continuous
  have hc2 : Continuous (deriv (deriv ψ)) := hψd.continuous_deriv (by simp)
  have hdiff1 : Differentiable ℝ (deriv ψ) := hψd.differentiable (by simp)
  -- the parametric integrands
  set F : ℝ → ℝ → ℝ := fun v θ => deriv ψ ((x + θ * v) / ℓ) with hF
  set F' : ℝ → ℝ → ℝ := fun v θ => deriv (deriv ψ) ((x + θ * v) / ℓ) * (θ / ℓ) with hF'
  have hFc : Continuous (Function.uncurry F) := by
    have : Continuous fun p : ℝ × ℝ => deriv ψ ((x + p.2 * p.1) / ℓ) :=
      hc1.comp (by fun_prop)
    exact this
  have hF'c : Continuous (Function.uncurry F') := by
    have : Continuous fun p : ℝ × ℝ => deriv (deriv ψ) ((x + p.2 * p.1) / ℓ) * (p.2 / ℓ) :=
      (hc2.comp (by fun_prop)).mul (by fun_prop)
    exact this
  have hrw : (fun v : ℝ => gradZ ψ ℓ x (x + v)) = fun v => ∫ θ in (0 : ℝ)..1, F v θ := by
    funext v
    simp only [gradZ, add_sub_cancel_left, hF]
  rw [hrw]
  -- the derivative at every point, by differentiation under the integral sign
  have hderiv : ∀ v0 : ℝ, HasDerivAt (fun v => ∫ θ in (0 : ℝ)..1, F v θ)
      (∫ θ in (0 : ℝ)..1, F' v0 θ) v0 := by
    intro v0
    have hHc : Continuous fun p : ℝ × ℝ => deriv (deriv ψ) ((x + p.2 * p.1) / ℓ) :=
      hc2.comp (by fun_prop)
    obtain ⟨M, hM⟩ := ((isCompact_closedBall v0 1).prod
      (isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_bound_of_continuousOn hHc.continuousOn
    have hMb : ∀ v ∈ Metric.ball v0 1, ∀ θ ∈ Icc (0 : ℝ) 1, ‖F' v θ‖ ≤ max M 0 * (1 / |ℓ|) := by
      intro v hv θ hθ
      have hvb : v ∈ Metric.closedBall v0 1 := Metric.ball_subset_closedBall hv
      have h1 : ‖deriv (deriv ψ) ((x + θ * v) / ℓ)‖ ≤ M := hM (v, θ) ⟨hvb, hθ⟩
      have h1' : ‖deriv (deriv ψ) ((x + θ * v) / ℓ)‖ ≤ max M 0 := h1.trans (le_max_left _ _)
      have hθ0 : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
      have h2 : |θ| / |ℓ| ≤ 1 / |ℓ| := div_le_div_of_nonneg_right hθ0 (abs_nonneg _)
      show ‖deriv (deriv ψ) ((x + θ * v) / ℓ) * (θ / ℓ)‖ ≤ _
      rw [norm_mul, norm_div, Real.norm_eq_abs θ, Real.norm_eq_abs ℓ]
      exact mul_le_mul h1' h2 (by positivity) (le_max_right _ _)
    have hH : ∀ᶠ v in 𝓝 v0, AEStronglyMeasurable (F v) (volume.restrict (uIoc (0 : ℝ) 1)) :=
      Eventually.of_forall fun v => ((hFc.comp (by fun_prop : Continuous fun θ : ℝ => (v, θ)))).aestronglyMeasurable
    have hint : IntervalIntegrable (F v0) volume 0 1 :=
      (hFc.comp (by fun_prop : Continuous fun θ : ℝ => (v0, θ))).intervalIntegrable 0 1
    have hmeas : AEStronglyMeasurable (F' v0) (volume.restrict (uIoc (0 : ℝ) 1)) :=
      (hF'c.comp (by fun_prop : Continuous fun θ : ℝ => (v0, θ))).aestronglyMeasurable
    have hbd : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ uIoc (0 : ℝ) 1 → ∀ v ∈ Metric.ball v0 1,
        ‖F' v θ‖ ≤ max M 0 * (1 / |ℓ|) := by
      refine ae_of_all _ fun θ hθ v hv => hMb v hv θ ?_
      rw [uIoc_of_le zero_le_one] at hθ
      exact ⟨hθ.1.le, hθ.2⟩
    have hdiff : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ uIoc (0 : ℝ) 1 → ∀ v ∈ Metric.ball v0 1,
        HasDerivAt (fun v => F v θ) (F' v θ) v := by
      refine ae_of_all _ fun θ _ v _ => ?_
      have hlin : HasDerivAt (fun v : ℝ => (x + θ * v) / ℓ) (θ / ℓ) v := by
        have := ((hasDerivAt_id v).const_mul θ |>.const_add x).div_const ℓ
        simpa using this
      have hpsi : HasDerivAt (deriv ψ) (deriv (deriv ψ) ((x + θ * v) / ℓ)) ((x + θ * v) / ℓ) :=
        (hdiff1 _).hasDerivAt
      exact hpsi.comp v hlin
    exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (F := F) (F' := F') (x₀ := v0) (s := Metric.ball v0 1)
      (bound := fun _ => max M 0 * (1 / |ℓ|)) (Metric.ball_mem_nhds v0 one_pos)
      hH hint hmeas hbd (by simp) hdiff).2
  -- the derivative is continuous in the increment
  have hdcont : Continuous (fun v0 : ℝ => ∫ θ in (0 : ℝ)..1, F' v0 θ) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF'c 0 1
  rw [contDiff_one_iff_deriv]
  refine ⟨fun v => (hderiv v).differentiableAt, ?_⟩
  have hfun : deriv (fun v => ∫ θ in (0 : ℝ)..1, F v θ) = fun v0 => ∫ θ in (0 : ℝ)..1, F' v0 θ := by
    funext v0
    exact (hderiv v0).deriv
  rw [hfun]
  exact hdcont

end

end Riesz1
