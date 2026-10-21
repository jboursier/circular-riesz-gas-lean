/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Mollification of Lipschitz functions

The derivative of a mollification is the mollification of the almost everywhere
classical derivative. This supplies the approximation bridge for the weighted Sobolev completion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff NNReal Convolution

namespace Riesz1.WeightedSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : E → ℝ} {C : ℝ≥0}

/-- The classical derivative of a Lipschitz function is locally integrable,
including its specified value at points of nondifferentiability. -/
theorem locallyIntegrable_fderiv_of_lipschitz (hF : LipschitzWith C F) :
    LocallyIntegrable (fderiv ℝ F) (volume : Measure E) := by
  apply (memLp_top_of_bound (measurable_fderiv ℝ F).aestronglyMeasurable
    (C : ℝ) (Eventually.of_forall fun _ => norm_fderiv_le_of_lipschitz ℝ hF)).locallyIntegrable
  exact le_top

/-- Differentiation of a bump convolution of a Lipschitz function. Rademacher's
theorem supplies differentiability only almost everywhere, which is sufficient. -/
theorem fderiv_normed_convolution_lipschitz (hF : LipschitzWith C F)
    (b : ContDiffBump (0 : E)) (x : E) :
    fderiv ℝ (b.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) x =
      (b.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ F) x := by
  let k := b.normed (volume : Measure E)
  have hk : Continuous k := b.continuous_normed
  have hki : Integrable k volume := hk.integrable_of_hasCompactSupport b.hasCompactSupport_normed
  have hm : AEStronglyMeasurable (fun y => k y • fderiv ℝ F (x - y)) volume :=
    hk.aestronglyMeasurable.smul
      ((measurable_fderiv ℝ F).aestronglyMeasurable.comp_measurePreserving
        (volume.measurePreserving_sub_left x))
  have hd : ∀ᵐ y ∂(volume : Measure E), DifferentiableAt ℝ F (x - y) :=
    (volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae
      (hF.ae_differentiableAt (μ := volume))
  have ht := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (𝕜 := ℝ) (F := fun z y => k y * F (z - y)) (x₀ := x) (s := univ)
    (F' := fun y => k y • fderiv ℝ F (x - y)) (bound := fun y => ‖k y‖ * C)
    univ_mem (fun z _ => hk.aestronglyMeasurable.mul
      (hF.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (b.hasCompactSupport_normed.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      hk hF.continuous.locallyIntegrable x) hm
    (Eventually.of_forall fun y z _ => by
      rw [← mul_sub, norm_mul]
      calc
        ‖k y‖ * ‖F (z - y) - F (x - y)‖ ≤
            ‖k y‖ * ((C : ℝ) * ‖(z - y) - (x - y)‖) :=
          mul_le_mul_of_nonneg_left (hF.norm_sub_le _ _) (norm_nonneg _)
        _ = (‖k y‖ * C) * ‖z - x‖ := by rw [sub_sub_sub_cancel_right]; ring)
    (hki.norm.mul_const _) (by
      filter_upwards [hd] with y hy
      simpa using (hy.hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const y)).const_mul (k y))
  exact ht.2.fderiv

/-- A nonnegative normalized bump preserves a pointwise norm bound. -/
theorem norm_normed_convolution_le {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] (b : ContDiffBump (0 : E))
    {g : E → V} {D : ℝ} (hg : ∀ x, ‖g x‖ ≤ D) (x : E) :
    ‖(b.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x‖ ≤ D := by
  calc
    _ ≤ ∫ y, b.normed volume y * D :=
      norm_integral_le_of_norm_le (b.integrable_normed.mul_const D)
        (Eventually.of_forall fun y => by
          simp only [ContinuousLinearMap.lsmul_apply, norm_smul,
            Real.norm_of_nonneg (b.nonneg_normed y)]
          exact mul_le_mul_of_nonneg_left (hg _) (b.nonneg_normed y))
    _ = D := by rw [integral_mul_const, b.integral_normed, one_mul]

/-- Smooth approximations to a globally Lipschitz function with a common gradient
bound and almost everywhere convergence of the gradients. -/
theorem exists_smooth_approximation_lipschitz (hF : LipschitzWith C F) :
    ∃ φ : ℕ → E → ℝ, (∀ k, ContDiff ℝ ∞ (φ k)) ∧
      (∀ k x, ‖φ k x - F x‖ ≤ C) ∧
      (∀ k x, ‖gradient (φ k) x‖ ≤ C) ∧
      (∀ x, Tendsto (fun k => φ k x) atTop (𝓝 (F x))) ∧
      ∀ᵐ x ∂(volume : Measure E),
        Tendsto (fun k => gradient (φ k) x) atTop (𝓝 (gradient F x)) := by
  have hr (k : ℕ) : 0 < (1 : ℝ) / (k + 1) := by positivity
  let b (k : ℕ) : ContDiffBump (0 : E) :=
    { rIn := (1 / (k + 1)) / 2
      rOut := 1 / (k + 1)
      rIn_pos := half_pos (hr k)
      rIn_lt_rOut := half_lt_self (hr k) }
  let φ (k : ℕ) := b k |>.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F
  have hb : Tendsto (fun k => (b k).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hd k x := fderiv_normed_convolution_lipschitz hF (b k) x
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (b k).hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (b k).contDiff_normed hF.continuous.locallyIntegrable
  · intro k x
    change dist (φ k x) (F x) ≤ C
    apply (b k).dist_normed_convolution_le hF.continuous.aestronglyMeasurable
    intro y hy
    apply (hF.dist_le_mul y x).trans
    have hr1 : (b k).rOut ≤ 1 := by
      dsimp [b]
      exact div_le_one_of_le₀ (by norm_cast; omega) (by positivity)
    exact mul_le_of_le_one_right C.coe_nonneg ((mem_ball.mp hy).le.trans hr1)
  · intro k x
    change ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (φ k) x)‖ ≤ C
    rw [LinearIsometryEquiv.norm_map, hd]
    exact norm_normed_convolution_le (b k)
      (fun _ => norm_fderiv_le_of_lipschitz ℝ hF) x
  · exact ContDiffBump.convolution_tendsto_right_of_continuous hb hF.continuous
  · have ha := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hb
      (K := 2) (Eventually.of_forall fun k => by dsimp [b]; linarith)
      (locallyIntegrable_fderiv_of_lipschitz hF)
    filter_upwards [ha] with x hx
    have ht := (InnerProductSpace.toDual ℝ E).symm.continuous.continuousAt.tendsto.comp hx
    simpa only [Function.comp_def, gradient, ← hd] using ht

end Riesz1.WeightedSobolev

end
