/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.Completion
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Compactly supported smooth approximants of weighted `H¹` pairs

Let `ν` be a finite measure on a finite-dimensional inner product space `E`, and let
`IsWeightedH1 ν U F G` hold. This file shows that every such pair is approximated, in the
weighted `H¹` error, by smooth functions with compact support. The construction has three steps:

* a globally smooth `ψ` agrees with a given smooth approximant `φ` on a neighbourhood of
  `closure U`, so `ψ` and `φ` have equal values and gradients at every point of `closure U`.
* a radial cutoff `x ↦ θ(R⁻¹ • x) ψ(x)`, with `θ` a fixed bump equal to `1` on the unit ball, has
  error tending to zero as `R → ∞`, by dominated convergence.
* a finite-dimensional `H¹` error is controlled by the errors of its two pieces.

The statements are general and carry no log-Sobolev content. They feed the entropy argument in
`Riesz1.LogSobolevEntropy.logSobolev_conditioning_H1`.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff NNReal Manifold

namespace Riesz1.WeightedSobolev

section Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A function `φ`, smooth on an open set `W`, is replaced near a closed set `A ⊆ W` by a globally
smooth function `ψ`: each point of `A` has a neighbourhood on which `ψ = φ`. -/
theorem exists_contDiff_eventuallyEq {A W : Set E} (hA : IsClosed A) (hW : IsOpen W) (hAW : A ⊆ W)
    {φ : E → ℝ} (hφ : ContDiffOn ℝ ∞ φ W) :
    ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ ∀ x ∈ A, ψ =ᶠ[𝓝 x] φ := by
  obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (I := 𝓘(ℝ, E)) (n := ⊤) hW.isClosed_compl hA (Set.disjoint_compl_left_iff_subset.2 hAW)
  have hfC : ContDiff ℝ ∞ (f : E → ℝ) := contMDiff_iff_contDiff.1 f.contMDiff
  refine ⟨fun x => f x * φ x, ?_, fun x hx => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hxW : x ∈ W
    · exact hfC.contDiffAt.mul (hφ.contDiffAt (hW.mem_nhds hxW))
    · have h0 : (fun y => f y * φ y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [(eventually_nhdsSet_iff_forall.1 hf0) x hxW] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  · filter_upwards [(eventually_nhdsSet_iff_forall.1 hf1) x hx] with y hy
    simp [hy]

end Smoothing

section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A fixed smooth bump on `E`: compactly supported, valued in `[0, 1]`, equal to `1` on the
closed unit ball, vanishing outside the ball of radius `2`, with bounded derivative. -/
theorem exists_unit_cutoff :
    ∃ θ : E → ℝ, ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧
      (∀ x ∈ closedBall (0 : E) 1, θ x = 1) ∧ (∀ x, 2 ≤ ‖x‖ → θ x = 0) ∧
      ∃ M : ℝ, ∀ x, ‖fderiv ℝ θ x‖ ≤ M := by
  let b : ContDiffBump (0 : E) :=
    { rIn := 1, rOut := 2, rIn_pos := one_pos, rIn_lt_rOut := one_lt_two }
  have hC : ContDiff ℝ ∞ b := b.contDiff
  have hcs : HasCompactSupport b := b.hasCompactSupport
  have hfd : Continuous (fun x => ‖fderiv ℝ b x‖) :=
    (hC.continuous_fderiv (by simp)).norm
  obtain ⟨M, hM⟩ := hfd.bounded_above_of_compact_support (HasCompactSupport.fderiv (𝕜 := ℝ) hcs).norm
  refine ⟨b, hC, hcs, fun x => ⟨b.nonneg, b.le_one⟩, fun x hx => b.one_of_mem_closedBall hx,
    fun x hx => b.zero_of_le_dist ?_, M, fun x => ?_⟩
  · simpa [dist_zero_right] using hx
  · have := hM x
    rwa [Real.norm_of_nonneg (norm_nonneg _)] at this

omit [FiniteDimensional ℝ E] in
/-- The derivative of the rescaled bump `y ↦ θ(R⁻¹ • y)` is bounded by `M / R`. -/
theorem norm_fderiv_scaled_le {θ : E → ℝ} (hθ : Differentiable ℝ θ) {M : ℝ}
    (hM : ∀ y, ‖fderiv ℝ θ y‖ ≤ M) {R : ℝ} (hR : 0 < R) (x : E) :
    ‖fderiv ℝ (fun y => θ (R⁻¹ • y)) x‖ ≤ M / R := by
  have h1 : HasFDerivAt θ (fderiv ℝ θ (R⁻¹ • x)) (R⁻¹ • x) := (hθ (R⁻¹ • x)).hasFDerivAt
  have h2 : HasFDerivAt (fun y : E => R⁻¹ • y) (R⁻¹ • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_smul R⁻¹
  have h3 : fderiv ℝ (fun y => θ (R⁻¹ • y)) x =
      (fderiv ℝ θ (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ E) := (h1.comp x h2).fderiv
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rw [h3]
  calc ‖(fderiv ℝ θ (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ E)‖
      ≤ ‖fderiv ℝ θ (R⁻¹ • x)‖ * ‖R⁻¹ • ContinuousLinearMap.id ℝ E‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ M * R⁻¹ := by
        have hid : ‖R⁻¹ • ContinuousLinearMap.id ℝ E‖ ≤ R⁻¹ := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
          exact mul_le_of_le_one_right (inv_nonneg.2 hR.le) ContinuousLinearMap.norm_id_le
        exact mul_le_mul (hM _) hid (norm_nonneg _) hM0
    _ = M / R := by ring

/-- The gradient is the Riesz representative of the derivative, an isometric identification,
so the extended-real norm of a gradient difference is that of the derivative difference. -/
theorem enorm_gradient_sub_gradient (g h : E → ℝ) (x : E) :
    ‖gradient g x - gradient h x‖ₑ = ‖fderiv ℝ g x - fderiv ℝ h x‖ₑ := by
  simp only [gradient, ← map_sub, LinearIsometryEquiv.enorm_map]

/-- Elementary inequality for extended-real numbers: squares of sums are at most twice the sum of
squares. -/
theorem ennreal_add_sq_le (a b : ENNReal) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  have key : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    have h : ((a + b : ℝ≥0) : ℝ) ^ 2 ≤ ((2 * (a ^ 2 + b ^ 2) : ℝ≥0) : ℝ) := by
      push_cast
      nlinarith [sq_nonneg ((a : ℝ) - b)]
    exact_mod_cast h
  exact_mod_cast key

/-- The extended-real `L²` error of a sum is at most twice the sum of the errors. -/
theorem lintegral_enorm_sq_add_le {α V : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] {f g : α → V}
    (hf : AEMeasurable f μ) :
    ∫⁻ x, ‖f x + g x‖ₑ ^ 2 ∂μ ≤ 2 * (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ + ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ) := by
  calc ∫⁻ x, ‖f x + g x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x, 2 * (‖f x‖ₑ ^ 2 + ‖g x‖ₑ ^ 2) ∂μ := by
        refine lintegral_mono fun x => ?_
        exact (pow_le_pow_left₀ zero_le (enorm_add_le _ _) 2).trans (ennreal_add_sq_le _ _)
    _ = 2 * (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ + ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
          lintegral_add_left' (hf.enorm.pow_const 2)]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The value error of the cutoff is `|a - 1| |b|` for the weight `a = θ(R⁻¹ • x)` and `b = ψ x`. -/
theorem enorm_mul_sub_self (a b : ℝ) : ‖a * b - b‖ₑ = ‖a - 1‖ₑ * ‖b‖ₑ := by
  rw [← enorm_mul]
  congr 1
  ring

/-- The gradient error of the cutoff, pointwise: the derivative of the product splits into the
term `(θ - 1) • ∇ψ` and the term `ψ • ∇(θ(R⁻¹ • ·))`, the latter of size at most `M / R`. -/
theorem enorm_gradient_cutoff_sub_le {θ : E → ℝ} (hθ : Differentiable ℝ θ) {M : ℝ}
    (hM : ∀ y, ‖fderiv ℝ θ y‖ ≤ M) {R : ℝ} (hR : 0 < R) {ψ : E → ℝ} (hψ : Differentiable ℝ ψ)
    (x : E) :
    ‖gradient (fun y => θ (R⁻¹ • y) * ψ y) x - gradient ψ x‖ₑ ≤
      ‖θ (R⁻¹ • x) - 1‖ₑ * ‖gradient ψ x‖ₑ + ‖ψ x‖ₑ * ENNReal.ofReal (M / R) := by
  have hθR : Differentiable ℝ (fun y => θ (R⁻¹ • y)) := by
    intro y
    exact (hθ (R⁻¹ • y)).comp y ((differentiableAt_id).const_smul R⁻¹)
  have hprod : fderiv ℝ (fun y => θ (R⁻¹ • y) * ψ y) x =
      θ (R⁻¹ • x) • fderiv ℝ ψ x + ψ x • fderiv ℝ (fun y => θ (R⁻¹ • y)) x :=
    fderiv_mul (hθR x) (hψ x)
  rw [enorm_gradient_sub_gradient, hprod]
  have hdiff : θ (R⁻¹ • x) • fderiv ℝ ψ x + ψ x • fderiv ℝ (fun y => θ (R⁻¹ • y)) x -
      fderiv ℝ ψ x = (θ (R⁻¹ • x) - 1) • fderiv ℝ ψ x +
        ψ x • fderiv ℝ (fun y => θ (R⁻¹ • y)) x := by
    rw [sub_smul, one_smul]
    abel
  rw [hdiff]
  refine (enorm_add_le ((θ (R⁻¹ • x) - 1) • fderiv ℝ ψ x)
    (ψ x • fderiv ℝ (fun y => θ (R⁻¹ • y)) x)).trans (add_le_add ?_ ?_)
  · rw [enorm_smul]
    have hg : ‖fderiv ℝ ψ x‖ₑ = ‖gradient ψ x‖ₑ := by
      simp only [gradient, LinearIsometryEquiv.enorm_map]
    rw [hg]
  · have hL : ‖fderiv ℝ (fun y => θ (R⁻¹ • y)) x‖ₑ ≤ ENNReal.ofReal (M / R) := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_fderiv_scaled_le hθ hM hR x)
    rw [enorm_smul]
    exact mul_le_mul_of_nonneg_left hL zero_le

/-- The radial cutoff error tends to zero as the radius `R` tends to infinity. The value error
and the gradient error are controlled by dominated convergence, and the scaling error by
`M / R`. -/
theorem tendsto_cutoff_error [MeasurableSpace E] [BorelSpace E] {ν : Measure E}
    [IsFiniteMeasure ν] {θ : E → ℝ} (hθ : ContDiff ℝ ∞ θ) (h01 : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1)
    (h1 : ∀ x ∈ closedBall (0 : E) 1, θ x = 1) {M : ℝ} (hM : ∀ x, ‖fderiv ℝ θ x‖ ≤ M)
    {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψL2 : ∫⁻ x, ‖ψ x‖ₑ ^ 2 ∂ν ≠ ⊤)
    (hψG : ∫⁻ x, ‖gradient ψ x‖ₑ ^ 2 ∂ν ≠ ⊤) :
    Tendsto (fun R : ℝ => ∫⁻ x, ‖θ (R⁻¹ • x) * ψ x - ψ x‖ₑ ^ 2 ∂ν +
      ∫⁻ x, ‖gradient (fun y => θ (R⁻¹ • y) * ψ y) x - gradient ψ x‖ₑ ^ 2 ∂ν) atTop (𝓝 0) := by
  have hθc : Continuous θ := hθ.continuous
  have hgc : Continuous (fun x => gradient ψ x) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hψ.continuous_fderiv (by simp))
  -- the weight `θ(R⁻¹ • ·) - 1` vanishes on the ball of radius `R` and is at most one
  have hzero : ∀ x : E, ∀ᶠ R : ℝ in atTop, ‖θ (R⁻¹ • x) - 1‖ₑ = 0 := by
    intro x
    filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop ‖x‖] with R hR hRx
    have hmem : R⁻¹ • x ∈ closedBall (0 : E) 1 := by
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le),
        inv_mul_le_iff₀ hR, mul_one]
      exact hRx
    rw [h1 _ hmem, sub_self, enorm_zero]
  have hw1 : ∀ (R : ℝ) (x : E), ‖θ (R⁻¹ • x) - 1‖ₑ ≤ 1 := by
    intro R x
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_one.2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(h01 (R⁻¹ • x)).1, (h01 (R⁻¹ • x)).2]
  have hmeasw : ∀ R : ℝ, Measurable (fun x : E => ‖θ (R⁻¹ • x) - 1‖ₑ) := fun R =>
    ((hθc.comp (continuous_const_smul R⁻¹)).sub continuous_const).enorm.measurable
  have hmeasψ : Measurable (fun x : E => ‖ψ x‖ₑ) := hψ.continuous.enorm.measurable
  have hmeasG : Measurable (fun x : E => ‖gradient ψ x‖ₑ) := hgc.enorm.measurable
  -- the value term `A R`
  have hA : Tendsto (fun R : ℝ => ∫⁻ x, (‖θ (R⁻¹ • x) - 1‖ₑ * ‖ψ x‖ₑ) ^ 2 ∂ν) atTop (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence (μ := ν) (l := atTop)
      (F := fun R x => (‖θ (R⁻¹ • x) - 1‖ₑ * ‖ψ x‖ₑ) ^ 2) (f := fun _ => 0)
      (fun x => ‖ψ x‖ₑ ^ 2)
      (Eventually.of_forall fun R => (((hmeasw R).mul hmeasψ)).pow_const 2)
      (Eventually.of_forall fun R => Eventually.of_forall fun x => ?_) hψL2
      (Eventually.of_forall fun x => ?_)
    · simpa using h
    · rw [mul_pow]
      exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le (hw1 R x))
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hzero x] with R hR
      simp [hR]
  -- the gradient term `B R`
  have hB : Tendsto (fun R : ℝ => ∫⁻ x, (‖θ (R⁻¹ • x) - 1‖ₑ * ‖gradient ψ x‖ₑ) ^ 2 ∂ν)
      atTop (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence (μ := ν) (l := atTop)
      (F := fun R x => (‖θ (R⁻¹ • x) - 1‖ₑ * ‖gradient ψ x‖ₑ) ^ 2) (f := fun _ => 0)
      (fun x => ‖gradient ψ x‖ₑ ^ 2)
      (Eventually.of_forall fun R => (((hmeasw R).mul hmeasG)).pow_const 2)
      (Eventually.of_forall fun R => Eventually.of_forall fun x => ?_) hψG
      (Eventually.of_forall fun x => ?_)
    · simpa using h
    · rw [mul_pow]
      exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le (hw1 R x))
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hzero x] with R hR
      simp [hR]
  -- the scaling term `C R`, of size `(M / R)² ∫ |ψ|²`
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hsq : Tendsto (fun R : ℝ => ENNReal.ofReal ((M / R) ^ 2)) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := M)).div_atTop tendsto_id (l := atTop)).pow 2
    simpa using ENNReal.tendsto_ofReal h
  have hC : Tendsto (fun R : ℝ => ∫⁻ x, (‖ψ x‖ₑ * ENNReal.ofReal (M / R)) ^ 2 ∂ν) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.mul_const hsq (Or.inr hψL2)
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    simp only [mul_pow]
    rw [lintegral_mul_const' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
      ENNReal.ofReal_pow (div_nonneg hM0 hR.le), mul_comm]
  -- the squeeze: the total error is bounded by `A R + 2 B R + 2 C R` for `R > 0`
  have hup : Tendsto (fun R : ℝ => (∫⁻ x, (‖θ (R⁻¹ • x) - 1‖ₑ * ‖ψ x‖ₑ) ^ 2 ∂ν) +
      (2 * (∫⁻ x, (‖θ (R⁻¹ • x) - 1‖ₑ * ‖gradient ψ x‖ₑ) ^ 2 ∂ν) +
        2 * ∫⁻ x, (‖ψ x‖ₑ * ENNReal.ofReal (M / R)) ^ 2 ∂ν)) atTop (𝓝 0) := by
    simpa using hA.add ((ENNReal.Tendsto.const_mul hB (Or.inr (by norm_num))).add
      (ENNReal.Tendsto.const_mul hC (Or.inr (by norm_num))))
  have hθd : Differentiable ℝ θ := hθ.differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun R => zero_le) ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  have hmeasB : Measurable (fun x => ‖θ (R⁻¹ • x) - 1‖ₑ * ‖gradient ψ x‖ₑ) :=
    (hmeasw R).mul hmeasG
  have hval : ∫⁻ x, ‖θ (R⁻¹ • x) * ψ x - ψ x‖ₑ ^ 2 ∂ν =
      ∫⁻ x, (‖θ (R⁻¹ • x) - 1‖ₑ * ‖ψ x‖ₑ) ^ 2 ∂ν :=
    lintegral_congr fun x => by rw [enorm_mul_sub_self]
  have hgrad : ∫⁻ x, ‖gradient (fun y => θ (R⁻¹ • y) * ψ y) x - gradient ψ x‖ₑ ^ 2 ∂ν ≤
      2 * (∫⁻ x, (‖θ (R⁻¹ • x) - 1‖ₑ * ‖gradient ψ x‖ₑ) ^ 2 ∂ν +
        ∫⁻ x, (‖ψ x‖ₑ * ENNReal.ofReal (M / R)) ^ 2 ∂ν) := by
    calc ∫⁻ x, ‖gradient (fun y => θ (R⁻¹ • y) * ψ y) x - gradient ψ x‖ₑ ^ 2 ∂ν
        ≤ ∫⁻ x, 2 * ((‖θ (R⁻¹ • x) - 1‖ₑ * ‖gradient ψ x‖ₑ) ^ 2 +
            (‖ψ x‖ₑ * ENNReal.ofReal (M / R)) ^ 2) ∂ν := by
          refine lintegral_mono fun x => ?_
          exact (pow_le_pow_left₀ zero_le (enorm_gradient_cutoff_sub_le hθd hM hR hψd x) 2).trans
            (ennreal_add_sq_le _ _)
      _ = 2 * (∫⁻ x, (‖θ (R⁻¹ • x) - 1‖ₑ * ‖gradient ψ x‖ₑ) ^ 2 ∂ν +
            ∫⁻ x, (‖ψ x‖ₑ * ENNReal.ofReal (M / R)) ^ 2 ∂ν) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
            lintegral_add_left' ((hmeasB.pow_const 2).aemeasurable)]
  rw [hval]
  calc ∫⁻ x, (‖θ (R⁻¹ • x) - 1‖ₑ * ‖ψ x‖ₑ) ^ 2 ∂ν +
        ∫⁻ x, ‖gradient (fun y => θ (R⁻¹ • y) * ψ y) x - gradient ψ x‖ₑ ^ 2 ∂ν
      ≤ (∫⁻ x, (‖θ (R⁻¹ • x) - 1‖ₑ * ‖ψ x‖ₑ) ^ 2 ∂ν) +
          2 * (∫⁻ x, (‖θ (R⁻¹ • x) - 1‖ₑ * ‖gradient ψ x‖ₑ) ^ 2 ∂ν +
            ∫⁻ x, (‖ψ x‖ₑ * ENNReal.ofReal (M / R)) ^ 2 ∂ν) :=
        add_le_add le_rfl hgrad
    _ = _ := by ring

/-- Doubling preserves strict inequalities of extended-real numbers. -/
theorem ennreal_two_mul_lt {a b : ENNReal} (h : a < b) : 2 * a < 2 * b := by
  rw [mul_comm 2 a, mul_comm 2 b]
  exact ENNReal.mul_lt_mul_left two_ne_zero ENNReal.ofNat_ne_top h

/-- The gradient of a smooth function is continuous. -/
theorem continuous_gradient_of_contDiff {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (fun x => gradient f x) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hf.continuous_fderiv (by simp))

/-- An `L²` function has finite extended-real second moment. -/
theorem lintegral_enorm_sq_ne_top_of_memLp {α V : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup V] {f : α → V} (hf : MemLp f 2 μ) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≠ ⊤ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (μ := μ) (p := 2)
    (by norm_num) (by norm_num) hf.eLpNorm_lt_top
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
  exact h.ne

/-- Approximation of a weighted `H¹` pair by smooth functions with compact support, in the
extended-real weighted `H¹` error `∫ |ζ - F|² + ∫ |∇ζ - G|²`, below any positive threshold. -/
theorem exists_hasCompactSupport_close [MeasurableSpace E] [BorelSpace E] {ν : Measure E}
    [IsFiniteMeasure ν] {U : Set E} (hU : ∀ᵐ x ∂ν, x ∈ closure U) {F : E → ℝ} {G : E → E}
    (hFG : IsWeightedH1 ν U F G) {ε : ENNReal} (hε0 : 0 < ε) :
    ∃ ζ : E → ℝ, ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧
      ∫⁻ x, ‖ζ x - F x‖ₑ ^ 2 ∂ν + ∫⁻ x, ‖gradient ζ x - G x‖ₑ ^ 2 ∂ν < ε := by
  obtain ⟨hF, hG, φ, hφS, hφF, hφG⟩ := hFG
  have hδ : 0 < ε / 4 := ENNReal.div_pos hε0.ne' (by norm_num)
  -- an approximant with small error, and a globally smooth function that agrees with it on
  -- `closure U`
  have hD : Tendsto (fun k => (∫⁻ x, ‖φ k x - F x‖ₑ ^ 2 ∂ν) +
      ∫⁻ x, ‖gradient (φ k) x - G x‖ₑ ^ 2 ∂ν) atTop (𝓝 0) := by
    simpa using hφF.add hφG
  obtain ⟨k, hk⟩ := (hD.eventually (gt_mem_nhds hδ)).exists
  obtain ⟨W, hWo, hUW, hφW⟩ := hφS k
  obtain ⟨ψ, hψC, hψeq⟩ := exists_contDiff_eventuallyEq isClosed_closure hWo hUW hφW
  have hψvals : ∫⁻ x, ‖ψ x - F x‖ₑ ^ 2 ∂ν = ∫⁻ x, ‖φ k x - F x‖ₑ ^ 2 ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [hU] with x hx
    rw [(hψeq x hx).eq_of_nhds]
  have hψgrads : ∫⁻ x, ‖gradient ψ x - G x‖ₑ ^ 2 ∂ν = ∫⁻ x, ‖gradient (φ k) x - G x‖ₑ ^ 2 ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [hU] with x hx
    have hgr : gradient ψ x = gradient (φ k) x := by
      unfold gradient
      rw [(hψeq x hx).fderiv_eq]
    rw [hgr]
  have hk1 : ∫⁻ x, ‖φ k x - F x‖ₑ ^ 2 ∂ν ≠ ⊤ := ne_top_of_lt (lt_of_le_of_lt le_self_add hk)
  have hk2 : ∫⁻ x, ‖gradient (φ k) x - G x‖ₑ ^ 2 ∂ν ≠ ⊤ :=
    ne_top_of_lt (lt_of_le_of_lt le_add_self hk)
  have hFfin : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν ≠ ⊤ := lintegral_enorm_sq_ne_top_of_memLp hF
  have hGfin : ∫⁻ x, ‖G x‖ₑ ^ 2 ∂ν ≠ ⊤ := lintegral_enorm_sq_ne_top_of_memLp hG
  -- finite energy of `ψ`
  have hψL2 : ∫⁻ x, ‖ψ x‖ₑ ^ 2 ∂ν ≠ ⊤ := by
    have h := lintegral_enorm_sq_add_le (μ := ν) (f := fun x => ψ x - F x) (g := F)
      (hψC.continuous.aemeasurable.sub hF.aemeasurable)
    simp only [sub_add_cancel] at h
    refine ne_top_of_le_ne_top ?_ h
    refine ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.add_ne_top.2 ⟨?_, hFfin⟩)
    rw [hψvals]
    exact hk1
  have hψG : ∫⁻ x, ‖gradient ψ x‖ₑ ^ 2 ∂ν ≠ ⊤ := by
    have h := lintegral_enorm_sq_add_le (μ := ν) (f := fun x => gradient ψ x - G x) (g := G)
      ((continuous_gradient_of_contDiff hψC).aemeasurable.sub hG.aemeasurable)
    simp only [sub_add_cancel] at h
    refine ne_top_of_le_ne_top ?_ h
    refine ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.add_ne_top.2 ⟨?_, hGfin⟩)
    rw [hψgrads]
    exact hk2
  -- the radial cutoff of `ψ`
  obtain ⟨θ, hθC, hθcs, h01, h1, h2, M, hM⟩ := exists_unit_cutoff (E := E)
  have hT := tendsto_cutoff_error hθC h01 h1 hM hψC hψL2 hψG
  obtain ⟨R, hRδ, hR0⟩ := ((hT.eventually (gt_mem_nhds hδ)).and (eventually_gt_atTop 0)).exists
  have hζC : ContDiff ℝ ∞ (fun y => θ (R⁻¹ • y) * ψ y) :=
    (hθC.comp (contDiff_const.smul contDiff_id)).mul hψC
  refine ⟨fun y => θ (R⁻¹ • y) * ψ y, hζC, ?_, ?_⟩
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * R)) fun x hx => ?_
    have hx' : 2 * R < ‖x‖ := by simpa [mem_closedBall, dist_zero_right, not_le] using hx
    have hw : 2 ≤ ‖R⁻¹ • x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR0.le)]
      calc (2 : ℝ) = R⁻¹ * (2 * R) := by field_simp
        _ ≤ R⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_left hx'.le (inv_nonneg.2 hR0.le)
    simp [h2 _ hw]
  · -- the error estimate
    have hgc := continuous_gradient_of_contDiff hζC
    have hsplit1 := lintegral_enorm_sq_add_le (μ := ν)
      (f := fun x => (θ (R⁻¹ • x) * ψ x) - ψ x) (g := fun x => ψ x - F x)
      ((hζC.continuous.aemeasurable).sub hψC.continuous.aemeasurable)
    have hsplit2 := lintegral_enorm_sq_add_le (μ := ν)
      (f := fun x => gradient (fun y => θ (R⁻¹ • y) * ψ y) x - gradient ψ x)
      (g := fun x => gradient ψ x - G x)
      ((hgc.aemeasurable).sub (continuous_gradient_of_contDiff hψC).aemeasurable)
    simp only [sub_add_sub_cancel] at hsplit1 hsplit2
    have hcd : ∫⁻ x, ‖ψ x - F x‖ₑ ^ 2 ∂ν + ∫⁻ x, ‖gradient ψ x - G x‖ₑ ^ 2 ∂ν < ε / 4 := by
      rw [hψvals, hψgrads]
      exact hk
    have htot := add_le_add hsplit1 hsplit2
    have hsum : 2 * (∫⁻ x, ‖θ (R⁻¹ • x) * ψ x - ψ x‖ₑ ^ 2 ∂ν +
          ∫⁻ x, ‖ψ x - F x‖ₑ ^ 2 ∂ν) +
        2 * (∫⁻ x, ‖gradient (fun y => θ (R⁻¹ • y) * ψ y) x - gradient ψ x‖ₑ ^ 2 ∂ν +
          ∫⁻ x, ‖gradient ψ x - G x‖ₑ ^ 2 ∂ν) < ε := by
      have hδ4 : 4 * (ε / 4) = ε := ENNReal.mul_div_cancel' (by norm_num) (by norm_num)
      calc _ = 2 * (∫⁻ x, ‖θ (R⁻¹ • x) * ψ x - ψ x‖ₑ ^ 2 ∂ν +
            ∫⁻ x, ‖gradient (fun y => θ (R⁻¹ • y) * ψ y) x - gradient ψ x‖ₑ ^ 2 ∂ν) +
          2 * (∫⁻ x, ‖ψ x - F x‖ₑ ^ 2 ∂ν + ∫⁻ x, ‖gradient ψ x - G x‖ₑ ^ 2 ∂ν) := by ring
        _ < 2 * (ε / 4) + 2 * (ε / 4) :=
          ENNReal.add_lt_add (ennreal_two_mul_lt hRδ)
            (ennreal_two_mul_lt hcd)
        _ = 4 * (ε / 4) := by ring
        _ = ε := hδ4
    exact lt_of_le_of_lt htot hsum

end Cutoff

end Riesz1.WeightedSobolev

end

end
