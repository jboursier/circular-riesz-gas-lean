/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.ConvexityHessianDerivative
public import Riesz1.ToMathlib.Calculus.ParametricMeasurable
public import Riesz1.ToMathlib.Calculus.FrechetSecondLine
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Twice Fréchet differentiability of the fiber integral (part of Lemma 3.7)

Let `Q ⊆ ℝ^m × ℝ^n` be open with `K` of class `C^∞` on `Q`, and let `J(z) = ∫_{Q_z} e^{-K(z,y)} dy`.
Under the majorant hypothesis on the zero extension of `e^{-K}` and its first two `z`-derivatives,
and the almost-everywhere `C²` regularity in `z`, this file proves that `-log J` is twice
differentiable at each `z` with `J(z) > 0` in the Fréchet sense: `-log J` is differentiable on a
neighbourhood of `z`, and its derivative is differentiable at `z`.

The proof differentiates `J` under the integral sign twice, using Mathlib's dominated
differentiation theorem for Fréchet derivatives. The integrability and measurability side
conditions for the derivative `z ↦ ∂_z ζ(z, y)` are supplied by
`Riesz1.aestronglyMeasurable_fderiv`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

namespace Riesz1.ConvexityHessian

variable {m n : ℕ}

variable {Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))}
  {K : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ}

/-- The derivative of a `C²` function is differentiable. -/
theorem differentiable_fderiv_of_contDiff_two {g : EuclideanSpace ℝ (Fin m) → ℝ}
    (hg : ContDiff ℝ 2 g) : Differentiable ℝ (fderiv ℝ g) :=
  (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)

/-- First-order differentiation of the fiber integral of the zero extension in the base point.
At every point `x` of a ball around `z` on which the majorants hold, the map
`w ↦ ∫ zeroExtension (w, y) dy` has Fréchet derivative `∫ ∂_w zeroExtension (x, y) dy`. -/
theorem hasFDerivAt_integral_zeroExtension (hQo : IsOpen Q) (hK : ContDiffOn ℝ 2 K Q)
    {z x : EuclideanSpace ℝ (Fin m)} {r : ℝ} (hx : x ∈ ball z r)
    {M₀ M₁ : EuclideanSpace ℝ (Fin n) → ℝ} (hM₀ : Integrable M₀) (hM₁ : Integrable M₁)
    (hmaj0 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ w ∈ closedBall z r,
      |zeroExtension Q K (w, y)| ≤ M₀ y)
    (hmaj1 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ w ∈ closedBall z r,
      ‖fderiv ℝ (fun w' => zeroExtension Q K (w', y)) w‖ ≤ M₁ y)
    (hsmooth : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ContDiff ℝ 2 (fun w => zeroExtension Q K (w, y))) :
    HasFDerivAt (fun w => ∫ y, zeroExtension Q K (w, y))
      (∫ y, fderiv ℝ (fun w' => zeroExtension Q K (w', y)) x) x := by
  have hball : ball z r ∈ 𝓝 x := isOpen_ball.mem_nhds hx
  have hmeas : ∀ w : EuclideanSpace ℝ (Fin m),
      AEStronglyMeasurable (fun y => zeroExtension Q K (w, y)) volume :=
    fun w => aestronglyMeasurable_zeroExtension_slice hQo hK w
  have hdiff : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Differentiable ℝ (fun w => zeroExtension Q K (w, y)) :=
    hsmooth.mono fun y hy => hy.differentiable (by norm_num)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun w y => zeroExtension Q K (w, y))
    (F' := fun w y => fderiv ℝ (fun w' => zeroExtension Q K (w', y)) w) (bound := M₁) hball
    (Eventually.of_forall fun w => hmeas w) ?_ ?_ ?_ hM₁ ?_
  · refine Integrable.mono' hM₀ (hmeas x) ?_
    filter_upwards [hmaj0] with y hy
    rw [Real.norm_eq_abs]
    exact hy x (ball_subset_closedBall hx)
  · exact aestronglyMeasurable_fderiv (g := fun y w => zeroExtension Q K (w, y))
      (fun w => hmeas w) hdiff x
  · filter_upwards [hmaj1] with y hy w hw
    exact hy w (ball_subset_closedBall hw)
  · filter_upwards [hdiff] with y hy w _
    exact (hy w).hasFDerivAt

/-- Second-order differentiation of the fiber integral in the base point. At every point `x` of a
ball around `z` on which the majorants hold, the map `w ↦ ∫ ∂_w zeroExtension (w, y) dy` has
Fréchet derivative `∫ ∂²_w zeroExtension (x, y) dy`. -/
theorem hasFDerivAt_integral_fderiv_zeroExtension (hQo : IsOpen Q) (hK : ContDiffOn ℝ 2 K Q)
    {z x : EuclideanSpace ℝ (Fin m)} {r : ℝ} (hx : x ∈ ball z r)
    {M₁ M₂ : EuclideanSpace ℝ (Fin n) → ℝ} (hM₁ : Integrable M₁) (hM₂ : Integrable M₂)
    (hmaj1 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ w ∈ closedBall z r,
      ‖fderiv ℝ (fun w' => zeroExtension Q K (w', y)) w‖ ≤ M₁ y)
    (hmaj2 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ w ∈ closedBall z r,
      ‖fderiv ℝ (fderiv ℝ (fun w' => zeroExtension Q K (w', y))) w‖ ≤ M₂ y)
    (hsmooth : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ContDiff ℝ 2 (fun w => zeroExtension Q K (w, y))) :
    HasFDerivAt (fun w => ∫ y, fderiv ℝ (fun w' => zeroExtension Q K (w', y)) w)
      (∫ y, fderiv ℝ (fderiv ℝ (fun w' => zeroExtension Q K (w', y))) x) x := by
  have hball : ball z r ∈ 𝓝 x := isOpen_ball.mem_nhds hx
  have hmeas : ∀ w : EuclideanSpace ℝ (Fin m),
      AEStronglyMeasurable (fun y => zeroExtension Q K (w, y)) volume :=
    fun w => aestronglyMeasurable_zeroExtension_slice hQo hK w
  have hdiff : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Differentiable ℝ (fun w => zeroExtension Q K (w, y)) :=
    hsmooth.mono fun y hy => hy.differentiable (by norm_num)
  have hdiff1 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Differentiable ℝ (fun w => fderiv ℝ (fun w' => zeroExtension Q K (w', y)) w) :=
    hsmooth.mono fun y hy => differentiable_fderiv_of_contDiff_two hy
  have hmeas1 : ∀ w : EuclideanSpace ℝ (Fin m),
      AEStronglyMeasurable (fun y => fderiv ℝ (fun w' => zeroExtension Q K (w', y)) w) volume :=
    fun w => aestronglyMeasurable_fderiv (g := fun y w => zeroExtension Q K (w, y))
      (fun w => hmeas w) hdiff w
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun w y => fderiv ℝ (fun w' => zeroExtension Q K (w', y)) w)
    (F' := fun w y => fderiv ℝ (fderiv ℝ (fun w' => zeroExtension Q K (w', y))) w)
    (bound := M₂) hball (Eventually.of_forall fun w => hmeas1 w) ?_ ?_ ?_ hM₂ ?_
  · refine Integrable.mono' hM₁ (hmeas1 x) ?_
    filter_upwards [hmaj1] with y hy
    exact hy x (ball_subset_closedBall hx)
  · exact aestronglyMeasurable_fderiv
      (g := fun y w => fderiv ℝ (fun w' => zeroExtension Q K (w', y)) w) hmeas1 hdiff1 x
  · filter_upwards [hmaj2] with y hy w hw
    exact hy w (ball_subset_closedBall hw)
  · filter_upwards [hdiff1] with y hy w _
    exact (hy w).hasFDerivAt

/-- **Twice differentiability of `-log J`** (Lemma 3.7, the
differentiability part). Let `J(z) = ∫_{Q_z} e^{-K(z,y)} dy` with `J(z) > 0`. Then `-log J` is
differentiable on a neighbourhood of `z`, and its derivative is differentiable at `z`. -/
theorem twiceDifferentiableAt_neg_log_fiberIntegral (hQo : IsOpen Q)
    (hK : ContDiffOn ℝ ∞ K Q)
    (hmaj : ∀ C : Set (EuclideanSpace ℝ (Fin m)), IsCompact C → C ⊆ Prod.fst '' Q →
      ∃ M₀ M₁ M₂ : EuclideanSpace ℝ (Fin n) → ℝ, Integrable M₀ ∧ Integrable M₁ ∧
        Integrable M₂ ∧
        ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ w ∈ C,
          |zeroExtension Q K (w, y)| ≤ M₀ y ∧
          ‖fderiv ℝ (fun w' => zeroExtension Q K (w', y)) w‖ ≤ M₁ y ∧
          ‖fderiv ℝ (fderiv ℝ (fun w' => zeroExtension Q K (w', y))) w‖ ≤ M₂ y)
    (hsmooth : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ContDiff ℝ 2 (fun w => zeroExtension Q K (w, y)))
    {z : EuclideanSpace ℝ (Fin m)} (hz : 0 < fiberIntegral Q K z) :
    (∀ᶠ x in 𝓝 z, DifferentiableAt ℝ (fun x => -Real.log (fiberIntegral Q K x)) x) ∧
      DifferentiableAt ℝ (fderiv ℝ (fun x => -Real.log (fiberIntegral Q K x))) z := by
  have hK2 : ContDiffOn ℝ 2 K Q := hK.of_le (by simp)
  -- The point `z` projects into `Q`, since the fiber integral is positive.
  have hzP : z ∈ Prod.fst '' Q := by
    by_contra hnot
    have hempty : fiber Q z = ∅ := by
      ext y
      simp only [mem_empty_iff_false, iff_false]
      exact fun hy => hnot ⟨(z, y), hy, rfl⟩
    simp [fiberIntegral, hempty] at hz
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ Prod.fst '' Q := by
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (isOpenMap_fst Q hQo) z hzP
    exact ⟨ρ / 2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hball⟩
  obtain ⟨M₀, M₁, M₂, hM₀, hM₁, hM₂, hmaj'⟩ :=
    hmaj (closedBall z r) (isCompact_closedBall z r) hr
  have hmaj0 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ w ∈ closedBall z r,
      |zeroExtension Q K (w, y)| ≤ M₀ y := hmaj'.mono fun y hy w hw => (hy w hw).1
  have hmaj1 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ w ∈ closedBall z r,
      ‖fderiv ℝ (fun w' => zeroExtension Q K (w', y)) w‖ ≤ M₁ y :=
    hmaj'.mono fun y hy w hw => (hy w hw).2.1
  have hmaj2 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ w ∈ closedBall z r,
      ‖fderiv ℝ (fderiv ℝ (fun w' => zeroExtension Q K (w', y))) w‖ ≤ M₂ y :=
    hmaj'.mono fun y hy w hw => (hy w hw).2.2
  -- The fiber integral is the integral of the zero extension.
  have hJ : (fun x => -Real.log (fiberIntegral Q K x)) =
      fun x => -Real.log (∫ y, zeroExtension Q K (x, y)) := by
    funext x
    rw [fiberIntegral_eq_integral hQo x]
  have hzball : z ∈ ball z r := mem_ball_self hr0
  have hΦ1 : ∀ x ∈ ball z r, HasFDerivAt (fun w => ∫ y, zeroExtension Q K (w, y))
      (∫ y, fderiv ℝ (fun w' => zeroExtension Q K (w', y)) x) x := fun x hx =>
    hasFDerivAt_integral_zeroExtension hQo hK2 hx hM₀ hM₁ hmaj0 hmaj1 hsmooth
  have hΦ2 := hasFDerivAt_integral_fderiv_zeroExtension hQo hK2 hzball hM₁ hM₂ hmaj1 hmaj2 hsmooth
  have hpos : 0 < ∫ y, zeroExtension Q K (z, y) := by
    rw [← fiberIntegral_eq_integral hQo z]
    exact hz
  have hev : ∀ᶠ x in 𝓝 z, 0 < ∫ y, zeroExtension Q K (x, y) :=
    Tendsto.eventually_const_lt hpos (hΦ1 z hzball).continuousAt
  have hev' : ∀ᶠ x in 𝓝 z, x ∈ ball z r ∧ 0 < ∫ y, zeroExtension Q K (x, y) :=
    Filter.Eventually.and (Filter.eventually_of_mem (ball_mem_nhds z hr0) fun x hx => hx) hev
  -- The derivative of `-log J` near `z`.
  have hlog : ∀ x ∈ ball z r, 0 < ∫ y, zeroExtension Q K (x, y) →
      HasFDerivAt (fun x => -Real.log (∫ y, zeroExtension Q K (x, y)))
        (-((∫ y, zeroExtension Q K (x, y))⁻¹ •
          ∫ y, fderiv ℝ (fun w' => zeroExtension Q K (w', y)) x)) x :=
    fun x hx hxpos => ((hΦ1 x hx).log hxpos.ne').neg
  have hdiff_f : ∀ᶠ x in 𝓝 z,
      DifferentiableAt ℝ (fun x => -Real.log (∫ y, zeroExtension Q K (x, y))) x :=
    hev'.mono fun x hx => (hlog x hx.1 hx.2).differentiableAt
  have hfder : fderiv ℝ (fun x => -Real.log (∫ y, zeroExtension Q K (x, y))) =ᶠ[𝓝 z]
      fun x => -((∫ y, zeroExtension Q K (x, y))⁻¹ •
        ∫ y, fderiv ℝ (fun w' => zeroExtension Q K (w', y)) x) :=
    hev'.mono fun x hx => (hlog x hx.1 hx.2).fderiv
  -- The derivative of the derivative at `z`, from the product and inverse rules.
  have hinv := (hasFDerivAt_inv hpos.ne').comp z (hΦ1 z hzball)
  have hG : DifferentiableAt ℝ
      (fun x => -((∫ y, zeroExtension Q K (x, y))⁻¹ •
        ∫ y, fderiv ℝ (fun w' => zeroExtension Q K (w', y)) x)) z :=
    ((hinv.smul hΦ2).neg).differentiableAt
  rw [hJ]
  exact ⟨hdiff_f, hG.congr_of_eventuallyEq hfder⟩

end Riesz1.ConvexityHessian

end

end
