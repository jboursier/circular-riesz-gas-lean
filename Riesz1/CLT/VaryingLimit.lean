/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.BLDistance
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Convergence in law with a varying companion law

The bounded-Lipschitz distance satisfies the triangle inequality, so a law that is close to a
companion law, which is itself close to the limit, converges in law to the limit. The companion
law may vary with the index. This gives the varying-limit bridge for the central limit theorem,
where the comparison law is `N(0, σ²_{ℓ_N})` and the variance depends on `N`.

The second part shows that centred Gaussian laws `gaussianReal 0 (σ ^ 2)` depend continuously on
the standard deviation `σ` in the bounded-Lipschitz distance. The proof writes each Gaussian as the
image of the standard Gaussian under multiplication by `σ`, and uses that a test function `f` with
`|f'| ≤ 1` moves points by at most the displacement.
-/

public section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Riesz1

/-- If the bounded-Lipschitz distances from the laws to companion laws and from the companion
laws to a limit both tend to zero, then the laws converge in law to the limit. -/
theorem convergesInLaw_of_blDistance_varying_limit (laws mid : ℕ → ProbabilityMeasure ℝ)
    (limit : ProbabilityMeasure ℝ)
    (h₁ : Tendsto (fun n => blDistance (laws n) (mid n)) atTop (𝓝 0))
    (h₂ : Tendsto (fun n => blDistance (mid n) limit) atTop (𝓝 0)) :
    ConvergesInLaw (fun n => (laws n : Measure ℝ)) (limit : Measure ℝ) := by
  refine convergesInLaw_of_blDistance_tendsto_zero laws limit
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le)
      (fun n => blDistance_triangle (laws n) limit (mid n)))
  simpa using h₁.add h₂

/-- The centred Gaussian law of variance `σ ^ 2` is the image of the standard Gaussian under
multiplication by `σ`. -/
lemma gaussianReal_zero_sq_eq_map (σ : ℝ≥0) :
    gaussianReal 0 (σ ^ 2) = (gaussianReal 0 1).map (fun x => (σ : ℝ) * x) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp

/-- A test function integrates against `gaussianReal 0 (σ ^ 2)` as it integrates the rescaled
variable `σ * x` against the standard Gaussian. -/
lemma integral_gaussianReal_zero_sq {f : ℝ → ℝ} (hf : BLTest f) (σ : ℝ≥0) :
    ∫ x, f x ∂(gaussianReal 0 (σ ^ 2)) = ∫ x, f ((σ : ℝ) * x) ∂(gaussianReal 0 1) := by
  rw [gaussianReal_zero_sq_eq_map, integral_map (measurable_const_mul _).aemeasurable
    hf.1.continuous.aestronglyMeasurable]

/-- A bounded-Lipschitz test function moves points by at most their distance, so
`|f a - f b| ≤ |a - b|`. -/
lemma abs_sub_le_of_blTest {f : ℝ → ℝ} (hf : BLTest f) (a b : ℝ) : |f a - f b| ≤ |a - b| := by
  obtain ⟨h1, -, h2⟩ := hf
  have key : ‖f a - f b‖ ≤ 1 * ‖a - b‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Set.univ) (x := b) (y := a) (C := 1)
      (fun x _ => (h1.differentiable (by norm_num)) x)
      (fun x _ => by simpa [Real.norm_eq_abs] using h2 x) convex_univ (Set.mem_univ _)
      (Set.mem_univ _)
  simpa [Real.norm_eq_abs] using key

/-- The integral of a bounded-Lipschitz test function against `gaussianReal 0 (σ ^ 2)` changes
by at most `|σ - τ|` times the first absolute moment of the standard Gaussian. -/
lemma abs_integral_gaussianReal_sub_le {f : ℝ → ℝ} (hf : BLTest f) (σ τ : ℝ≥0) :
    |(∫ x, f x ∂(gaussianReal 0 (σ ^ 2))) - ∫ x, f x ∂(gaussianReal 0 (τ ^ 2))| ≤
      |(σ : ℝ) - τ| * ∫ x, |x| ∂(gaussianReal 0 1) := by
  have hbd : ∀ c : ℝ, Integrable (fun x => f (c * x)) (gaussianReal 0 1) := fun c =>
    integrable_of_continuous_abs_le (C := 1) (hf.1.continuous.comp (continuous_const.mul continuous_id))
      (fun x => hf.2.1 _)
  have hint : Integrable (fun x : ℝ => |(σ : ℝ) - τ| * |x|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal' 1 ENNReal.one_ne_top).integrable le_rfl).abs.const_mul _
  rw [integral_gaussianReal_zero_sq hf σ, integral_gaussianReal_zero_sq hf τ,
    ← integral_sub (hbd σ) (hbd τ)]
  have key : ‖∫ x, f ((σ : ℝ) * x) - f ((τ : ℝ) * x) ∂(gaussianReal 0 1)‖ ≤
      ∫ x, |(σ : ℝ) - τ| * |x| ∂(gaussianReal 0 1) := by
    refine norm_integral_le_of_norm_le hint (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    have h := abs_sub_le_of_blTest hf ((σ : ℝ) * x) ((τ : ℝ) * x)
    rwa [← sub_mul, abs_mul] at h
  rw [integral_const_mul, Real.norm_eq_abs] at key
  exact key

/-- The bounded-Lipschitz distance between centred Gaussian laws is bounded by a fixed multiple of
the difference of their standard deviations. -/
lemma blDistance_gaussianReal_le (σ τ : ℝ≥0) :
    blDistance ⟨gaussianReal 0 (σ ^ 2), inferInstance⟩ ⟨gaussianReal 0 (τ ^ 2), inferInstance⟩ ≤
      ENNReal.ofReal (|(σ : ℝ) - τ| * ∫ x, |x| ∂(gaussianReal 0 1)) := by
  refine iSup_le fun f => ?_
  exact ENNReal.ofReal_le_ofReal (abs_integral_gaussianReal_sub_le f.2 σ τ)

/-- Centred Gaussian laws `gaussianReal 0 (σ n ^ 2)` converge to `gaussianReal 0 (σ₀ ^ 2)` in the
bounded-Lipschitz distance when the standard deviations `σ n` converge to `σ₀`. The argument
does not use `σ₀ > 0`. -/
theorem blDistance_gaussianReal_tendsto_zero (σ : ℕ → ℝ≥0) (σ₀ : ℝ≥0)
    (hσ : Tendsto σ atTop (𝓝 σ₀)) :
    Tendsto (fun n => blDistance ⟨gaussianReal 0 (σ n ^ 2), inferInstance⟩
      ⟨gaussianReal 0 (σ₀ ^ 2), inferInstance⟩) atTop (𝓝 0) := by
  have hreal : Tendsto (fun n => |(σ n : ℝ) - σ₀| * ∫ x, |x| ∂(gaussianReal 0 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (σ n : ℝ)) atTop (𝓝 (σ₀ : ℝ)) := NNReal.tendsto_coe.mpr hσ
    have h2 : Tendsto (fun n => |(σ n : ℝ) - σ₀|) atTop (𝓝 0) := by
      simpa using (h1.sub_const (σ₀ : ℝ)).abs
    simpa using h2.mul_const (∫ x, |x| ∂(gaussianReal 0 1))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le)
    (fun n => blDistance_gaussianReal_le (σ n) σ₀)
  simpa using ENNReal.tendsto_ofReal hreal

/-- Laws that are close in the bounded-Lipschitz distance to centred Gaussians with converging
standard deviations converge in law to the centred Gaussian of the limiting standard deviation.
This is the varying-limit bridge for the comparison laws `N(0, σ²_{ℓ_N})`. -/
theorem convergesInLaw_of_blDistance_gaussianReal (laws : ℕ → ProbabilityMeasure ℝ)
    (σ : ℕ → ℝ≥0) (σ₀ : ℝ≥0) (hσ : Tendsto σ atTop (𝓝 σ₀))
    (h : Tendsto (fun n => blDistance (laws n) ⟨gaussianReal 0 (σ n ^ 2), inferInstance⟩)
      atTop (𝓝 0)) :
    ConvergesInLaw (fun n => (laws n : Measure ℝ)) (gaussianReal 0 (σ₀ ^ 2)) :=
  convergesInLaw_of_blDistance_varying_limit laws
    (fun n => ⟨gaussianReal 0 (σ n ^ 2), inferInstance⟩) ⟨gaussianReal 0 (σ₀ ^ 2), inferInstance⟩ h
    (blDistance_gaussianReal_tendsto_zero σ σ₀ hσ)

end Riesz1
