/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.TestConvergence
public import Riesz1.Frozen.BlDistance

/-!
# Elementary properties of the bounded-Lipschitz distance

The distance `blDistance` is a supremum over `C¹` bounded-Lipschitz test functions. This file
proves that it is at most two, symmetric, subadditive, and zero on the diagonal. It also shows
that a distance tending to zero forces convergence in law, by way of
`convergesInLaw_of_blTest`.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Riesz1

/-- Each bounded-Lipschitz test function `f` bounds its own term of the supremum defining
`blDistance`. -/
lemma ofReal_abs_integral_sub_le_blDistance (μ ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf : BLTest f) :
    ENNReal.ofReal |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ blDistance μ ν :=
  le_iSup (fun g : {g : ℝ → ℝ // BLTest g} =>
    ENNReal.ofReal |(∫ x, g.val x ∂μ) - ∫ x, g.val x ∂ν|) ⟨f, hf⟩

/-- The bounded-Lipschitz distance is at most two. -/
lemma blDistance_le_two (μ ν : ProbabilityMeasure ℝ) : blDistance μ ν ≤ 2 := by
  refine iSup_le fun f => ?_
  obtain ⟨-, hb, -⟩ := f.property
  -- Every test function has integral at most one in absolute value under a probability measure.
  have hle : ∀ x, ‖f.val x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs]
    exact hb x
  have hbd : ∀ ρ : ProbabilityMeasure ℝ, |∫ x, f.val x ∂(ρ : Measure ℝ)| ≤ 1 := fun ρ => by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := 1) (ae_of_all _ hle)).trans_eq ?_
    simp
  have hab : |(∫ x, f.val x ∂μ) - ∫ x, f.val x ∂ν| ≤ 2 := by
    linarith [abs_sub (∫ x, f.val x ∂(μ : Measure ℝ)) (∫ x, f.val x ∂(ν : Measure ℝ)), hbd μ, hbd ν]
  calc ENNReal.ofReal |(∫ x, f.val x ∂μ) - ∫ x, f.val x ∂ν|
      ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hab
    _ = 2 := ENNReal.ofReal_ofNat 2

/-- The bounded-Lipschitz distance is symmetric. -/
lemma blDistance_comm (μ ν : ProbabilityMeasure ℝ) : blDistance μ ν = blDistance ν μ := by
  unfold blDistance
  congr 1
  funext f
  rw [abs_sub_comm]

/-- The bounded-Lipschitz distance satisfies the triangle inequality. -/
lemma blDistance_triangle (μ ν ρ : ProbabilityMeasure ℝ) :
    blDistance μ ν ≤ blDistance μ ρ + blDistance ρ ν := by
  refine iSup_le fun f => ?_
  have h1 := ofReal_abs_integral_sub_le_blDistance μ ρ f.property
  have h2 := ofReal_abs_integral_sub_le_blDistance ρ ν f.property
  calc ENNReal.ofReal |(∫ x, f.val x ∂μ) - ∫ x, f.val x ∂ν|
      ≤ ENNReal.ofReal (|(∫ x, f.val x ∂μ) - ∫ x, f.val x ∂ρ| +
          |(∫ x, f.val x ∂ρ) - ∫ x, f.val x ∂ν|) :=
        ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
    _ ≤ ENNReal.ofReal |(∫ x, f.val x ∂μ) - ∫ x, f.val x ∂ρ| +
          ENNReal.ofReal |(∫ x, f.val x ∂ρ) - ∫ x, f.val x ∂ν| := ENNReal.ofReal_add_le
    _ ≤ blDistance μ ρ + blDistance ρ ν := add_le_add h1 h2

/-- The bounded-Lipschitz distance vanishes on the diagonal. -/
lemma blDistance_self (μ : ProbabilityMeasure ℝ) : blDistance μ μ = 0 := by
  refine le_antisymm (iSup_le fun f => ?_) zero_le
  simp

/-- If the bounded-Lipschitz distance from the laws to the limit tends to zero, then the laws
converge in law. The distance bounds each test integral, so every `C¹` test integral converges,
and `convergesInLaw_of_blTest` finishes the argument. -/
theorem convergesInLaw_of_blDistance_tendsto_zero (laws : ℕ → ProbabilityMeasure ℝ)
    (limit : ProbabilityMeasure ℝ)
    (h : Tendsto (fun n => blDistance (laws n) limit) atTop (𝓝 0)) :
    ConvergesInLaw (fun n => (laws n : Measure ℝ)) (limit : Measure ℝ) := by
  -- The distance is finite, so its real part tends to zero.
  have hfin : ∀ n, blDistance (laws n) limit ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top (by norm_num) (blDistance_le_two (laws n) limit)
  have hreal : Tendsto (fun n => (blDistance (laws n) limit).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [ENNReal.toReal_zero] at this
    exact this
  refine convergesInLaw_of_blTest (fun n => (laws n : Measure ℝ)) (limit : Measure ℝ)
    (fun n => inferInstance) inferInstance ?_
  intro f hf
  refine tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hreal)
  have h1 := ofReal_abs_integral_sub_le_blDistance (laws n) limit hf
  have h2 := ENNReal.toReal_mono (hfin n) h1
  rw [ENNReal.toReal_ofReal (abs_nonneg _)] at h2
  rw [Real.dist_eq]
  exact h2

end Riesz1
