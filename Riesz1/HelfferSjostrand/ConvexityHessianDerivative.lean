/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.ConvexityHessianLine
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Twice differentiating the fiber integral along a line (part of the proof of Lemma 3.7)

Fix `z` in the projected interior of `Q`, a direction `b`, and a ball `ball 0 ε` of parameters
whose line `z + s b` stays in a closed ball `closedBall z r` inside the projected interior.
Let `ψ_y(t) = zeroExtension (z + t b, y)`. Under the majorant hypotheses
(integrable majorants of the zero extension and of its first and second `z`-derivatives, uniform
on the closed ball, and `C²` in `z` for almost every `y`), the function
`j(s) = ∫ ψ_y(s) dy = J(z + s b)` is differentiable on the parameter ball with derivative
`∫ firstCoef (z + s b, y) dy`, and that derivative is differentiable at `0` with derivative
`∫ secondCoef (z, y) dy`.

The pointwise derivative formulas `firstCoef` and `secondCoef` hold for almost every `y`
(`ConvexityHessianLine`). Mathlib's dominated-differentiation theorem with Lipschitz bounds on the
parameter ball carries the integrals. The last section gives the one-variable identity for the
second derivative of `-log j` at `0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace Riesz1.ConvexityHessian

variable {m n : ℕ}

section Bounds

/-- The derivative of `t ↦ f (z + t b)` at `s` is bounded by the derivative bound of `f` times
`‖b‖`. -/
theorem norm_deriv_comp_line_le (f : EuclideanSpace ℝ (Fin m) → ℝ) (z b : EuclideanSpace ℝ (Fin m))
    (s : ℝ) (hf : DifferentiableAt ℝ f (z + s • b)) {M : ℝ}
    (hM : ‖fderiv ℝ f (z + s • b)‖ ≤ M) :
    ‖deriv (fun t : ℝ => f (z + t • b)) s‖ ≤ M * ‖b‖ := by
  rw [(hasDerivAt_comp_line hf).deriv]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))

/-- The derivative of `t ↦ deriv (f (z + · b)) t` at `s` is bounded by the second derivative bound
of `f` times `‖b‖²`, for a `C²` function `f`. -/
theorem norm_deriv_deriv_comp_line_le (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (z b : EuclideanSpace ℝ (Fin m)) (s : ℝ) (hf : ContDiff ℝ 2 f) {M : ℝ}
    (hM : ‖fderiv ℝ (fderiv ℝ f) (z + s • b)‖ ≤ M) :
    ‖deriv (fun t : ℝ => deriv (fun t' : ℝ => f (z + t' • b)) t) s‖ ≤ M * ‖b‖ * ‖b‖ := by
  have hd1 : (fun t : ℝ => deriv (fun t' : ℝ => f (z + t' • b)) t) =
      fun t : ℝ => fderiv ℝ f (z + t • b) b := by
    funext t
    exact (hasDerivAt_comp_line (s := t) (hf.differentiable (by norm_num) _)).deriv
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) (z + s • b) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) _
  rw [hd1, (hasDerivAt_fderiv_comp_line_at hdf).deriv]
  have h2 : ‖fderiv ℝ (fderiv ℝ f) (z + s • b) b‖ ≤ M * ‖b‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  exact ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h2
    (norm_nonneg _)))

end Bounds

section FirstDerivative

variable {Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))}
  {K : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ}
  (b : EuclideanSpace ℝ (Fin m))

/-- The fiber slices of the zero extension of `e^{-K}` are a.e. strongly measurable. -/
theorem aestronglyMeasurable_zeroExtension_slice (hQo : IsOpen Q) (hK : ContDiffOn ℝ 2 K Q)
    (w : EuclideanSpace ℝ (Fin m)) :
    AEStronglyMeasurable (fun y => zeroExtension Q K (w, y)) volume :=
  aestronglyMeasurable_indicator_slice hQo
    (Real.continuous_exp.comp_continuousOn hK.continuousOn.neg) w

/-- The first derivative of the fiber integral along the line through `z`: at a parameter `s₀` of
the ball `ball 0 ε`, the function `s ↦ ∫ zeroExtension (z + s b, y) dy` has derivative
`∫ firstCoef (z + s₀ b, y) dy`. The majorants are uniform on the closed ball `closedBall z r`,
which contains the line over `ball 0 ε`. -/
theorem hasDerivAt_integral_zeroExtension_line (hQo : IsOpen Q) (hQc : Convex ℝ Q)
    (hK : ContDiffOn ℝ 2 K Q) {z : EuclideanSpace ℝ (Fin m)} {r ε : ℝ}
    (hr : closedBall z r ⊆ Prod.fst '' Q)
    (hε : ∀ s ∈ ball (0 : ℝ) ε, z + s • b ∈ closedBall z r)
    (hsmooth : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ContDiff ℝ 2 (fun w => zeroExtension Q K (w, y)))
    {M₀ M₁ : EuclideanSpace ℝ (Fin n) → ℝ} (hM₀ : Integrable M₀)
    (hM₁ : Integrable M₁)
    (hmaj0 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ w ∈ closedBall z r, |zeroExtension Q K (w, y)| ≤ M₀ y)
    (hmaj1 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ w ∈ closedBall z r,
        ‖fderiv ℝ (fun w' => zeroExtension Q K (w', y)) w‖ ≤ M₁ y)
    {s₀ : ℝ} (hs₀ : s₀ ∈ ball (0 : ℝ) ε) :
    HasDerivAt (fun s : ℝ => ∫ y, zeroExtension Q K (z + s • b, y))
      (∫ y, firstCoef Q K b (z + s₀ • b, y)) s₀ := by
  have hpi : ∀ s ∈ ball (0 : ℝ) ε, z + s • b ∈ Prod.fst '' Q := fun s hs => hr (hε s hs)
  have hLip : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      LipschitzOnWith (Real.nnabs (M₁ y * ‖b‖))
        (fun s : ℝ => zeroExtension Q K (z + s • b, y)) (ball (0 : ℝ) ε) := by
    filter_upwards [hmaj1, hsmooth] with y hy1 hy2
    refine (convex_ball _ _).lipschitzOnWith_of_nnnorm_deriv_le (fun s _ => ?_) (fun s hs => ?_)
    · exact (hasDerivAt_comp_line (f := fun w => zeroExtension Q K (w, y)) (s := s)
        (hy2.differentiable (by norm_num) _)).differentiableAt
    · have hb := norm_deriv_comp_line_le (fun w => zeroExtension Q K (w, y)) z b s
        (hy2.differentiable (by norm_num) _) (hy1 _ (hε s hs))
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs]
      exact hb.trans (le_abs_self _)
  have hball : ball (0 : ℝ) ε ∈ 𝓝 s₀ := isOpen_ball.mem_nhds hs₀
  have hmeas : ∀ᶠ s in 𝓝 s₀,
      AEStronglyMeasurable (fun y => zeroExtension Q K (z + s • b, y)) volume :=
    Eventually.of_forall fun s => aestronglyMeasurable_zeroExtension_slice hQo hK _
  have hint : Integrable (fun y => zeroExtension Q K (z + s₀ • b, y)) volume := by
    refine Integrable.mono' hM₀ (aestronglyMeasurable_zeroExtension_slice hQo hK _) ?_
    filter_upwards [hmaj0] with y hy
    rw [Real.norm_eq_abs]
    exact hy _ (hε s₀ hs₀)
  have hae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      HasDerivAt (fun s : ℝ => zeroExtension Q K (z + s • b, y))
        (firstCoef Q K b (z + s₀ • b, y)) s₀ :=
    ae_hasDerivAt_zeroExtension_line b hQo hQc hK z (hpi s₀ hs₀)
  exact (hasDerivAt_integral_of_dominated_loc_of_lip hball hmeas hint
    (aestronglyMeasurable_firstCoef b hQo hK _) hLip (hM₁.mul_const _) hae).2

end FirstDerivative

section SecondDerivative

variable {Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))}
  {K : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ}
  (b : EuclideanSpace ℝ (Fin m))

/-- The second derivative of the fiber integral along the line through `z`, at the base point:
the derivative of the first derivative `s ↦ ∫ ∂_s ψ_y(s) dy` at `0` is `∫ secondCoef (z, y) dy`. -/
theorem hasDerivAt_integral_deriv_zeroExtension_line (hQo : IsOpen Q) (hQc : Convex ℝ Q)
    (hK : ContDiffOn ℝ 2 K Q) {z : EuclideanSpace ℝ (Fin m)} {r ε : ℝ} (hεpos : 0 < ε)
    (hr : closedBall z r ⊆ Prod.fst '' Q)
    (hε : ∀ s ∈ ball (0 : ℝ) ε, z + s • b ∈ closedBall z r)
    (hsmooth : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ContDiff ℝ 2 (fun w => zeroExtension Q K (w, y)))
    {M₁ M₂ : EuclideanSpace ℝ (Fin n) → ℝ} (hM₁ : Integrable M₁) (hM₂ : Integrable M₂)
    (hmaj1 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ w ∈ closedBall z r,
        ‖fderiv ℝ (fun w' => zeroExtension Q K (w', y)) w‖ ≤ M₁ y)
    (hmaj2 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ w ∈ closedBall z r,
        ‖fderiv ℝ (fderiv ℝ (fun w' => zeroExtension Q K (w', y))) w‖ ≤ M₂ y) :
    HasDerivAt (fun s : ℝ => ∫ y, deriv (fun t : ℝ => zeroExtension Q K (z + t • b, y)) s)
      (∫ y, secondCoef Q K b (z, y)) 0 := by
  have hpi : ∀ s ∈ ball (0 : ℝ) ε, z + s • b ∈ Prod.fst '' Q := fun s hs => hr (hε s hs)
  have hball : ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := ball_mem_nhds 0 hεpos
  have hz : z ∈ Prod.fst '' Q := by simpa using hpi 0 (mem_ball_self hεpos)
  -- The first derivative of the zero extension agrees a.e. with `firstCoef`.
  have hfirst : ∀ s ∈ ball (0 : ℝ) ε,
      ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        deriv (fun t : ℝ => zeroExtension Q K (z + t • b, y)) s = firstCoef Q K b (z + s • b, y) :=
    fun s hs => (ae_hasDerivAt_zeroExtension_line b hQo hQc hK z (hpi s hs)).mono
      fun y hy => hy.deriv
  have hmeas : ∀ᶠ s in 𝓝 (0 : ℝ), AEStronglyMeasurable
      (fun y => deriv (fun t : ℝ => zeroExtension Q K (z + t • b, y)) s) volume := by
    filter_upwards [hball] with s hs
    exact (aestronglyMeasurable_firstCoef b hQo hK (z + s • b)).congr
      ((hfirst s hs).mono fun y hy => hy.symm)
  have hint : Integrable (fun y => deriv (fun t : ℝ => zeroExtension Q K (z + t • b, y)) 0)
      volume := by
    refine Integrable.mono' (hM₁.mul_const ‖b‖) hmeas.self_of_nhds ?_
    filter_upwards [hmaj1, hsmooth] with y hy1 hy2
    exact norm_deriv_comp_line_le (fun w => zeroExtension Q K (w, y)) z b 0
      (hy2.differentiable (by norm_num) _) (hy1 _ (hε 0 (mem_ball_self hεpos)))
  have hLip : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      LipschitzOnWith (Real.nnabs (M₂ y * ‖b‖ * ‖b‖))
        (fun s : ℝ => deriv (fun t : ℝ => zeroExtension Q K (z + t • b, y)) s) (ball (0 : ℝ) ε) := by
    filter_upwards [hmaj2, hsmooth] with y hy2 hy3
    refine (convex_ball _ _).lipschitzOnWith_of_nnnorm_deriv_le (fun s _ => ?_) (fun s hs => ?_)
    · have hfun : (fun t : ℝ => deriv (fun t' : ℝ => zeroExtension Q K (z + t' • b, y)) t) =
          fun t : ℝ => fderiv ℝ (fun w => zeroExtension Q K (w, y)) (z + t • b) b :=
        funext fun t => (hasDerivAt_comp_line (f := fun w => zeroExtension Q K (w, y)) (s := t)
          (hy3.differentiable (by norm_num) _)).deriv
      have hdf : DifferentiableAt ℝ (fderiv ℝ (fun w => zeroExtension Q K (w, y))) (z + s • b) :=
        ((hy3.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) _
      rw [hfun]
      exact (hasDerivAt_fderiv_comp_line_at hdf).differentiableAt
    · have hb := norm_deriv_deriv_comp_line_le (fun w => zeroExtension Q K (w, y)) z b s hy3
        (hy2 _ (hε s hs))
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs]
      exact hb.trans (le_abs_self _)
  refine (hasDerivAt_integral_of_dominated_loc_of_lip hball hmeas hint
    (aestronglyMeasurable_secondCoef b hQo hK z) hLip ((hM₂.mul_const _).mul_const _) ?_).2
  filter_upwards [ae_hasDerivAt_deriv_zeroExtension_line b hQo hQc hK z hz] with y hy
  exact hy

end SecondDerivative

section LogSecondDerivative

/-- The second derivative at `0` of `s ↦ -log j(s)`, when `j` has derivative `j'` near `0` and
`j'` has derivative `j''` at `0`, is `j'(0)² / j(0)² - j''(0) / j(0)`. -/
theorem deriv_deriv_neg_log_zero {j j' : ℝ → ℝ} {j'' : ℝ}
    (hj : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt j (j' s) s) (hj' : HasDerivAt j' j'' 0)
    (hpos : 0 < j 0) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => -Real.log (j s)) t) 0 =
      j' 0 ^ 2 / j 0 ^ 2 - j'' / j 0 := by
  have hj0 : HasDerivAt j (j' 0) 0 := hj.self_of_nhds
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < j t :=
    hj0.continuousAt.tendsto.eventually_const_lt hpos
  have hd1 : (fun t : ℝ => deriv (fun s : ℝ => -Real.log (j s)) t) =ᶠ[𝓝 0]
      fun t => -(j' t / j t) := by
    filter_upwards [hj, hev] with t ht hpt
    exact ((ht.log hpt.ne').neg).deriv
  have hd2 : HasDerivAt (fun t => -(j' t / j t)) (-((j'' * j 0 - j' 0 * j' 0) / j 0 ^ 2)) 0 :=
    (hj'.div hj0 hpos.ne').neg
  rw [hd1.deriv_eq, hd2.deriv]
  field_simp
  ring

end LogSecondDerivative

end Riesz1.ConvexityHessian

end

end
