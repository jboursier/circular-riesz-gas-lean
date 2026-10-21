/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Stein.Solution
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Expectation of the Stein equation

The last clause of Theorem 3 (equation (6.4)): for a `C¹` test `f`
with `|f| ≤ 1` and `|f'| ≤ 1`, a real random variable `G` on a probability space, and `σ > 0`,
the Stein solution `u = u_{f,σ}` satisfies

`E f(G) - E f(σ Z₀) = E[σ² u'(G) - G u(G)]`.

The proof evaluates the pointwise Stein equation `σ² u'(x) - x u(x) = f(x) - E f(σ Z₀)` at
`x = G(ω)` and integrates. The solution is the explicit `steinSolution`, whose
equation is `stein_ode`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Riesz1

/-- **Expectation of the Stein equation** (Theorem 3, equation (6.4)).
Let `μ` be a probability measure on `Ω`, let `σ > 0`, and let `f` be `C¹` with `|f| ≤ 1` and
`|f'| ≤ 1`. Let `G : Ω → ℝ` be measurable. Then the Stein solution `u = steinSolution σ f`
gives `∫ f(G) dμ - ∫ f(σ z) dγ(z) = ∫ (σ² u'(G) - G u(G)) dμ`, where `γ` is the standard
Gaussian. -/
theorem stein_expectation_identity {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (σ : ℝ) (hσ : 0 < σ) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hfb : ∀ x, |f x| ≤ 1) (hf' : ∀ x, |deriv f x| ≤ 1)
    (G : Ω → ℝ) (hGm : AEStronglyMeasurable G μ) :
    ∫ ω, f (G ω) ∂μ - ∫ z, f (σ * z) ∂(gaussianReal 0 1)
      = ∫ ω, (σ ^ 2 * deriv (steinSolution σ f) (G ω) - G ω * steinSolution σ f (G ω)) ∂μ := by
  set c : ℝ := ∫ z, f (σ * z) ∂(gaussianReal 0 1) with hc
  have hpt : ∀ ω, σ ^ 2 * deriv (steinSolution σ f) (G ω) - G ω * steinSolution σ f (G ω)
      = f (G ω) - c := fun ω => stein_ode (x := G ω) hf hσ hfb hf'
  have hfG : Integrable (fun ω => f (G ω)) μ :=
    Integrable.of_bound (hf.continuous.comp_aestronglyMeasurable hGm) 1
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hfb (G ω))
  simp_rw [hpt]
  rw [integral_sub hfG (integrable_const c), integral_const, probReal_univ, one_smul]

end Riesz1

end
