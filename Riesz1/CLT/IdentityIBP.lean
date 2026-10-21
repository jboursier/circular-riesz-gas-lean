/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.IdentityDerivatives
public import Riesz1.ToMathlib.MollifierPointwise.Smoothing
public import Riesz1.Variance.LoopIBPProposition
public import Riesz1.Variance.LoopIBPUniform
import all Riesz1.Variance.LoopScale
import all Riesz1.Variance.LoopForce
import all Riesz1.Variance.LoopForceEnergy
import all Riesz1.Variance.LoopIBPUniform

/-!
# Integration by parts for `u(G_N)` in Theorem 3

The second assertion of Theorem 3, equation (6.5), rests on the Gibbs
integration by parts of Proposition 5.5 (clause 2), which is stated only for
torus-smooth test functions. This file extends it to `F = u ∘ G` for a `C¹` function `u` with
bounded `u` and `u'`:

`E[u(G) 𝓛Φ] = E[u'(G) ∇G·∇Φ]`.

The extension smooths `u` by `u_ε = u ⋆ ρ_ε` (`IdentitySmoothing`), applies clause 2 to
`u_ε ∘ G`, and lets `ε ↓ 0` by dominated convergence on both sides.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The product of the statistic and the potential amplitudes is `K⁻¹`:
`K^{-s/2} K^{-1+s/2} = K⁻¹`. -/
lemma rpow_cltK_pair (K s : ℝ) (hK : 0 < K) : K ^ (-(s / 2)) * K ^ (-1 + s / 2) = K⁻¹ := by
  rw [← Real.rpow_add hK, show -(s / 2) + (-1 + s / 2) = (-1 : ℝ) by ring, Real.rpow_neg_one]

/-- In each coordinate, the product `∂ₖ(c·Fluct[R(·/ℓ)]) · ∂ₖ(a ℓ² Σᵢ ∫₀^{xᵢ/ℓ} Ψ)` equals
`c a R'(xₖ/ℓ) Ψ(xₖ/ℓ)`. -/
lemma partialDeriv_mul_partialDeriv_scaled {N : ℕ} {R Ψ : ℝ → ℝ} (hR : Differentiable ℝ R)
    (hΨ : Continuous Ψ) {ℓ : ℝ} (hℓ : 0 < ℓ) (c a : ℝ) (k : Fin N) (x : Fin N → ℝ) :
    partialDeriv (fun y => c * fluctIntegral (fun u => R (u / ℓ)) N y) k x *
      partialDeriv (fun y : Fin N → ℝ => a * ℓ ^ 2 * ∑ i : Fin N,
        ∫ u in (0 : ℝ)..(y i / ℓ), Ψ u) k x
      = c * a * (deriv R (x k / ℓ) * Ψ (x k / ℓ)) := by
  rw [partialDeriv_const_mul, partialDeriv_fluctIntegral_scaled hR,
    partialDeriv_primitive_sum hΨ hℓ]
  field_simp

/-- The covariance with a centered second argument is the integral of the product. -/
lemma gibbsCov_eq_integral_mul_of_mean_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {F H : Ω → ℝ} (hH : Integrable H μ)
    (hFH : Integrable (fun X => F X * H X) μ) (hHm : ∫ X, H X ∂μ = 0) :
    (∫ X, (F X - ∫ Y, F Y ∂μ) * (H X - ∫ Y, H Y ∂μ) ∂μ) = ∫ X, F X * H X ∂μ := by
  simp only [hHm, sub_zero]
  have hexp : ∀ X, (F X - ∫ Y, F Y ∂μ) * H X = F X * H X - (∫ Y, F Y ∂μ) * H X :=
    fun X => by ring
  simp_rw [hexp]
  rw [integral_sub hFH (hH.const_mul _), integral_const_mul, hHm, mul_zero, sub_zero]

/-- The gradient pairing of a composition: `∇(u ∘ G)·∇Φ = u'(G) ∇G·∇Φ`. -/
lemma gradDotPotential_comp_outer {N : ℕ} {u : ℝ → ℝ} {G Φ : (Fin N → ℝ) → ℝ}
    (hu : Differentiable ℝ u) (hG : Differentiable ℝ G) (x : Fin N → ℝ) :
    gradDotPotential (fun y => u (G y)) Φ x = deriv u (G x) * gradDotPotential G Φ x := by
  unfold gradDotPotential
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [partialDeriv_comp_outer hu hG k x]; ring

/-- The bound `|∫ g(x - t) ρ_ε(t) dt| ≤ M` when `|g| ≤ M`, for `ε > 0`. -/
lemma abs_integral_scaledMollifier_le {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → ℝ} {M : ℝ} (hM : ∀ y, |g y| ≤ M) (x : ℝ) :
    |∫ t, g (x - t) * scaledMollifier ρ ε t| ≤ M := by
  have hle : ∀ᵐ t ∂(volume : Measure ℝ), ‖g (x - t) * scaledMollifier ρ ε t‖ ≤
      M * scaledMollifier ρ ε t := by
    refine Eventually.of_forall fun t => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (scaledMollifier_nonneg' hρ hε t)]
    exact mul_le_mul_of_nonneg_right (hM _) (scaledMollifier_nonneg' hρ hε t)
  have h := norm_integral_le_of_norm_le (μ := volume)
    ((integrable_scaledMollifier' hρ hε).const_mul M) hle
  rw [integral_const_mul, integral_scaledMollifier hρ hε, mul_one, Real.norm_eq_abs] at h
  exact h

/-- A bounded measurable function times an integrable one is integrable. -/
lemma integrable_mul_of_abs_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {F H : Ω → ℝ}
    (hH : Integrable H μ) (hF : AEStronglyMeasurable F μ) {M : ℝ} (hM : ∀ x, |F x| ≤ M) :
    Integrable (fun X => F X * H X) μ := by
  refine Integrable.mono' (hH.norm.const_mul M) (hF.mul hH.aestronglyMeasurable)
    (Eventually.of_forall fun X => ?_)
  simp only [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hM X) (abs_nonneg _)

/-- **Integration by parts for `u ∘ G`** (the extension of clause 2 of
Proposition 5.5 to `C¹` functions of the statistic). Let `μ` be a probability
measure on configurations and `H` an integrable function with mean zero satisfying the covariance
identity of clause 2 for torus-smooth tests. Let `G` be torus-smooth, and let `u` be `C¹` with
bounded `u` and `u'`. Then `E[u(G) H] = E[u'(G) ∇G·∇Φ]`. -/
theorem clt_ibp_of_torus {N : ℕ+} (μ : Measure (Configuration N)) [IsProbabilityMeasure μ]
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (H : Configuration N → ℝ) (hH : Integrable H μ) (hHm : ∫ X, H X ∂μ = 0)
    (Φ : (Fin (N : ℕ) → ℝ) → ℝ)
    (hcov : ∀ F : (Fin (N : ℕ) → ℝ) → ℝ, IsTorusSmooth F →
      gibbsCov μ (fun X => F X.val) H = ∫ X, gradDotPotential F Φ X.val ∂μ)
    (G : (Fin (N : ℕ) → ℝ) → ℝ) (hG : IsTorusSmooth G)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) {M0 M1 : ℝ} (hM0 : ∀ y, |u y| ≤ M0)
    (hM1 : ∀ y, |deriv u y| ≤ M1)
    (hPc : Continuous (gradDotPotential G Φ)) {C : ℝ} (hPb : ∀ x, |gradDotPotential G Φ x| ≤ C) :
    ∫ X, u (G X.val) * H X ∂μ = ∫ X, deriv u (G X.val) * gradDotPotential G Φ X.val ∂μ := by
  have hGd : Differentiable ℝ G := hG.1.differentiable (by norm_num)
  have hGc : Continuous G := hG.1.continuous
  have huc : Continuous u := hu.continuous
  have hdu : Continuous (deriv u) := hu.continuous_deriv (by norm_num)
  have hXc : Continuous (fun X : Configuration N => X.val) := continuous_subtype_val
  -- Step A: the identity for the smoothed function `u_ε`.
  have hstepA : ∀ ε : ℝ, 0 < ε →
      ∫ X, mollifyLine ρ ε u (G X.val) * H X ∂μ
        = ∫ X, deriv (mollifyLine ρ ε u) (G X.val) * gradDotPotential G Φ X.val ∂μ := by
    intro ε hε
    have hsm : ContDiff ℝ ∞ (mollifyLine ρ ε u) :=
      contDiff_mollifyLine_of_locallyIntegrable hρ hε huc.locallyIntegrable
    have hF : IsTorusSmooth (fun x => mollifyLine ρ ε u (G x)) := by
      refine ⟨hsm.comp hG.1, fun k x => ?_⟩
      simp only [hG.2 k x]
    have hc := hcov _ hF
    have hgrad : ∀ x, gradDotPotential (fun y => mollifyLine ρ ε u (G y)) Φ x
        = deriv (mollifyLine ρ ε u) (G x) * gradDotPotential G Φ x :=
      fun x => gradDotPotential_comp_outer (hsm.differentiable (by norm_num)) hGd x
    simp only [hgrad] at hc
    have hFc : Continuous (fun X : Configuration N => mollifyLine ρ ε u (G X.val)) :=
      hsm.continuous.comp (hGc.comp hXc)
    have hFint : Integrable (fun X : Configuration N => mollifyLine ρ ε u (G X.val)) μ :=
      Integrable.of_bound hFc.aestronglyMeasurable M0
        (Eventually.of_forall fun X => by
          rw [Real.norm_eq_abs]
          exact abs_mollifyLine_le_of_bound hρ hε hM0 _)
    have hFH := integrable_mul_of_abs_le hH hFc.aestronglyMeasurable
      (fun X => abs_mollifyLine_le_of_bound hρ hε hM0 _)
    have hcov' := gibbsCov_eq_integral_mul_of_mean_zero μ hH hFH hHm
    unfold gibbsCov at hc
    rw [hcov'] at hc
    exact hc
  -- Step B: the limit `ε ↓ 0` of both sides.
  have hL : Tendsto (fun ε : ℝ => ∫ X, mollifyLine ρ ε u (G X.val) * H X ∂μ) (𝓝[>] 0)
      (𝓝 (∫ X, u (G X.val) * H X ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun X => M0 * ‖H X‖) ?_ ?_
      (hH.norm.const_mul M0) ?_
    · refine eventually_mem_nhdsWithin.mono fun ε hε => ?_
      have hFc : Continuous (fun X : Configuration N => mollifyLine ρ ε u (G X.val)) :=
        (contDiff_mollifyLine_of_locallyIntegrable hρ hε huc.locallyIntegrable).continuous.comp
          (hGc.comp hXc)
      exact (integrable_mul_of_abs_le hH hFc.aestronglyMeasurable
        (fun X => abs_mollifyLine_le_of_bound hρ hε hM0 _)).aestronglyMeasurable
    · refine eventually_mem_nhdsWithin.mono fun ε hε => Eventually.of_forall fun X => ?_
      simp only [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_mollifyLine_le_of_bound hρ hε hM0 _) (abs_nonneg _)
    · refine Eventually.of_forall fun X => ?_
      exact (tendsto_mollifyLine_fun hρ huc (G X.val)).mul_const (H X)
  have hR : Tendsto (fun ε : ℝ => ∫ X, deriv (mollifyLine ρ ε u) (G X.val)
        * gradDotPotential G Φ X.val ∂μ) (𝓝[>] 0)
      (𝓝 (∫ X, deriv u (G X.val) * gradDotPotential G Φ X.val ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => M1 * C) ?_ ?_
      (integrable_const _) ?_
    · refine eventually_mem_nhdsWithin.mono fun ε hε => ?_
      have hsm : ContDiff ℝ ∞ (mollifyLine ρ ε u) :=
        contDiff_mollifyLine_of_locallyIntegrable hρ hε huc.locallyIntegrable
      have hc : Continuous (fun X : Configuration N =>
          deriv (mollifyLine ρ ε u) (G X.val) * gradDotPotential G Φ X.val) :=
        ((hsm.continuous_deriv (by norm_num)).comp (hGc.comp hXc)).mul (hPc.comp hXc)
      exact hc.aestronglyMeasurable
    · refine eventually_mem_nhdsWithin.mono fun ε hε => Eventually.of_forall fun X => ?_
      have hd : |deriv (mollifyLine ρ ε u) (G X.val)| ≤ M1 := by
        rw [(hasDerivAt_mollifyLine_of_bounded hρ hε hu hM0 hM1 (G X.val)).deriv]
        exact abs_integral_scaledMollifier_le hρ hε hM1 _
      have hM1C : 0 ≤ M1 := le_trans (abs_nonneg _) (hM1 0)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul hd (hPb _) (abs_nonneg _) hM1C
    · refine Eventually.of_forall fun X => ?_
      refine Tendsto.congr' ?_ ((tendsto_mollifyLine_deriv hρ hu (G X.val)).mul_const
        (gradDotPotential G Φ X.val))
      filter_upwards [eventually_mem_nhdsWithin] with ε hε
      rw [(hasDerivAt_mollifyLine_of_bounded hρ hε hu hM0 hM1 (G X.val)).deriv]
  exact tendsto_nhds_unique_of_eventuallyEq hL hR
    (eventually_mem_nhdsWithin.mono fun ε hε => hstepA ε hε)

end Riesz1

end
