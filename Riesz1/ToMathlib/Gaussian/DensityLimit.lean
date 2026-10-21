/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Dominated convergence for normalized densities

These general measure lemmas give convergence of expectations after normalization. They
are used when smooth approximations of a Gaussian perturbation share an integrable
majorant. No probability measure is defined at a zero normalizing integral.
-/

public section

open MeasureTheory Filter Topology

namespace Riesz1.Gaussian

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Integration against a nonnegative real density with positive mass. -/
theorem integral_normalized_density {p : α → ℝ} (hp : Measurable p)
    (hp0 : ∀ x, 0 ≤ p x) (hZ : 0 < ∫ x, p x ∂μ) (g : α → ℝ) :
    ∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (p x / ∫ y, p y ∂μ)) =
      (∫ x, p x * g x ∂μ) / ∫ y, p y ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul
    (hp.div_const _).ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (hp0 _) hZ.le), smul_eq_mul,
    div_mul_eq_mul_div]
  exact integral_div _ _

/-- A common integrable majorant and almost everywhere convergence imply convergence of
normalized expectations of every bounded measurable real test. Positivity of the limiting
normalizer is essential. -/
theorem tendsto_integral_normalized_density {pn : ℕ → α → ℝ} {p bound : α → ℝ}
    (hpn : ∀ n, Measurable (pn n)) (hp : Measurable p)
    (hpn0 : ∀ n x, 0 ≤ pn n x) (hp0 : ∀ x, 0 ≤ p x)
    (hZn : ∀ n, 0 < ∫ x, pn n x ∂μ) (hZ : 0 < ∫ x, p x ∂μ)
    (hbound : Integrable bound μ) (hbn : ∀ n, ∀ᵐ x ∂μ, ‖pn n x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => pn n x) atTop (𝓝 (p x)))
    {g : α → ℝ} (hg : AEStronglyMeasurable g μ) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    Tendsto (fun n => ∫ x, g x ∂μ.withDensity
      (fun x => ENNReal.ofReal (pn n x / ∫ y, pn n y ∂μ))) atTop
      (𝓝 (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (p x / ∫ y, p y ∂μ)))) := by
  have htZ := tendsto_integral_of_dominated_convergence bound
    (fun n => (hpn n).aestronglyMeasurable) hbound hbn hlim
  have htN : Tendsto (fun n => ∫ x, pn n x * g x ∂μ) atTop
      (𝓝 (∫ x, p x * g x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖bound x‖ * |C|)
    · exact fun n => (hpn n).aestronglyMeasurable.mul hg
    · exact hbound.norm.mul_const _
    · intro n
      filter_upwards [hbn n] with x hx
      rw [norm_mul]
      exact mul_le_mul (hx.trans (le_abs_self _)) ((hC x).trans (le_abs_self C))
        (norm_nonneg _) (norm_nonneg _)
    · filter_upwards [hlim] with x hx
      exact hx.mul_const _
  simp_rw [integral_normalized_density (hpn _) (hpn0 _) (hZn _) g,
    integral_normalized_density hp hp0 hZ g]
  exact htN.div htZ hZ.ne'

end Riesz1.Gaussian
