/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.IdentityDefs
public import Riesz1.Bridges.Mollifier
public import Riesz1.ToMathlib.Mollifier.RegularizationSobolev
public import Riesz1.ToMathlib.Mollifier.Multiplier
public import Riesz1.ToMathlib.CircleFourierPairing
public import Riesz1.ToMathlib.CircleMollifyFourier
public import Riesz1.ToMathlib.CirclePullback
public import Riesz1.Variance.LoopMasterScaling
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Approximation of the covariance profile in `L²`

The approximation step in Proposition 5.6: the covariance of the statistic of a
general `L²` profile is the limit of the covariances of statistics of smooth profiles. The smooth
profiles are the regularizations `ξ_h = ξ ⋆ ρ_h` on the circle of length `ℓ⁻¹`,
pulled back to the unit circle (`loopMasterPullback`).

The Fourier coefficients of the pulled-back regularization are those of the profile multiplied by
the real mollifier multiplier `ρ̂(h k / L)` (`fourierCoeff_circleMollify`). Parseval's identity then
turns the `L²` distance `‖ξ_h - ξ‖` into a series whose terms tend to zero and are dominated by
`64 |ξ̂_k|²`, so dominated convergence applies (`tendsto_tsum_of_dominated_convergence`).

The main results are `Riesz1.circleCoeff_pullback_cltRegCircle`,
`Riesz1.integral_sq_pullback_regularize_sub` and `Riesz1.exists_pullback_regularize_sub_lt`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology ComplexConjugate Real
open scoped ContDiff

namespace Riesz1

/-- The Fourier coefficients of the pulled-back regularization are those of the pulled-back
profile times the real mollifier multiplier at the scale `h k / L`. -/
theorem circleCoeff_pullback_cltRegCircle {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (L : Length)
    (f : {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)}) {h : ℝ}
    (hh : 0 < h) (k : ℤ) :
    circleCoeff (loopMasterPullback L (cltRegCircle hρ L hh f)) k =
      circleCoeff (loopMasterPullback L f.val) k * (mollifierFT ρ (h * k / L.val) : ℂ) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hF : LocallyIntegrable (fun t : ℝ => f.val (t : Circle L)) volume :=
    Internal.locallyIntegrable_circle_lift (complexL2Integrable L _ f.property).re
  have hp : Function.Periodic (fun t : ℝ => f.val (t : Circle L)) L.val := by
    intro x
    simp only [AddCircle.coe_add_period]
  have hreg : circleCoeff (loopMasterPullback L (cltRegCircle hρ L hh f)) k =
      coeff L ⟨(fun z => ((cltRegCircle hρ L hh f) z : ℂ)),
        complexL2Integrable L _ (loopMasterLengthTest L (cltRegCircle hρ L hh f)
          (cltRegCircle_contDiff hρ L hh f)).property⟩ k :=
    loopMaster_coeff_pullback L (loopMasterLengthTest L (cltRegCircle hρ L hh f)
      (cltRegCircle_contDiff hρ L hh f)) k
  rw [hreg, loopMaster_coeff_pullback L f k]
  unfold coeff
  dsimp only
  exact Internal.fourierCoeff_circleMollify hρ hh hF hp f.val (cltRegCircle hρ L hh f) (fun _ => rfl)
    (fun x => cltRegCircle_coe hρ L hh f x) k

/-- The Fourier coefficients of a difference of real `L²` functions on the unit circle. -/
lemma circleCoeff_sub_of_memLp (f g : UnitAddCircle → ℝ)
    (hf : MemLp (fun x : UnitAddCircle => (f x : ℂ)) 2 volume)
    (hg : MemLp (fun x : UnitAddCircle => (g x : ℂ)) 2 volume) (k : ℤ) :
    circleCoeff (fun x => f x - g x) k = circleCoeff f k - circleCoeff g k := by
  have hint : ∀ φ : UnitAddCircle → ℂ, MemLp φ 2 volume →
      Integrable (fun x : UnitAddCircle => fourier (-k) x * φ x) volume := fun φ hφ =>
    (hφ.integrable one_le_two).bdd_mul (c := 1) (fourier (-k)).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => (norm_fourier_apply _ _).le)
  unfold circleCoeff
  rw [fourierCoeff_eq_volume, fourierCoeff_eq_volume, fourierCoeff_eq_volume,
    ← integral_sub (hint _ hf) (hint _ hg)]
  congr 1
  funext x
  simp only [Complex.ofReal_sub]
  ring

/-- The multiplier error of a mollified Fourier series sums to zero as the smoothing radius
vanishes, dominated by `64 c_k²`. -/
theorem tendsto_tsum_mollifier_sub_sq {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {L : ℝ} (_hL : 0 < L)
    {c : ℤ → ℝ} (hc : Summable fun k : ℤ => c k ^ 2) :
    Tendsto (fun h : ℝ => ∑' k : ℤ, c k ^ 2 * (mollifierFT ρ (h * k / L) - 1) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hcm := hρ.isCircleMollifier
  have hlim : ∀ k : ℤ, Tendsto (fun h : ℝ => c k ^ 2 * (mollifierFT ρ (h * k / L) - 1) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    intro k
    have hup : Tendsto (fun h : ℝ => 8 * (h * k / L) ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have hcont : Continuous (fun h : ℝ => 8 * (h * k / L) ^ 2) := by fun_prop
      have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    have h1 : Tendsto (fun h : ℝ => 1 - mollifierFT ρ (h * k / L)) (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
        (Eventually.of_forall fun h => mollifierFT_one_sub_nonneg hcm _) ?_
      refine Eventually.of_forall fun h => ?_
      refine (mollifierFT_one_sub_le hcm _).trans ?_
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
    have h2 : Tendsto (fun h : ℝ => (mollifierFT ρ (h * k / L) - 1) ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have := h1.pow 2
      rw [zero_pow two_ne_zero] at this
      exact this.congr fun h => by ring
    simpa using (tendsto_const_nhds (x := c k ^ 2)).mul h2
  have hbd : ∀ (h : ℝ) (k : ℤ), ‖c k ^ 2 * (mollifierFT ρ (h * k / L) - 1) ^ 2‖ ≤ 64 * c k ^ 2 := by
    intro h k
    have h0 := mollifierFT_one_sub_nonneg hcm (h * k / L)
    have h8 := mollifierFT_one_sub_le hcm (h * k / L)
    have hmin : 1 - mollifierFT ρ (h * k / L) ≤ 8 := by
      have := min_le_right ((h * k / L) ^ 2) 1
      linarith
    have hsq : (mollifierFT ρ (h * k / L) - 1) ^ 2 ≤ 64 := by nlinarith
    have hnn : 0 ≤ c k ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn (sq_nonneg _))]
    nlinarith [mul_nonneg hnn (sub_nonneg.2 hsq)]
  have hsum := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
    (f := fun h k => c k ^ 2 * (mollifierFT ρ (h * k / L) - 1) ^ 2)
    (g := fun _ => (0 : ℝ)) (bound := fun k => 64 * c k ^ 2) (hc.mul_left 64)
    (fun k => hlim k) (Eventually.of_forall fun h k => hbd h k)
  simpa using hsum

/-- The squared `L²` distance of the pulled-back regularization from the pulled-back profile is the
Fourier series of the multiplier error. -/
theorem integral_sq_pullback_regularize_sub {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (L : Length)
    (f : {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)}) {h : ℝ}
    (hh : 0 < h) :
    ∫ x : UnitAddCircle, (loopMasterPullback L (cltRegCircle hρ L hh f) x -
        loopMasterPullback L f.val x) ^ 2 =
      ∑' k : ℤ, ‖circleCoeff (loopMasterPullback L f.val) k‖ ^ 2 *
        (mollifierFT ρ (h * k / L.val) - 1) ^ 2 := by
  have hGL2 : MemLp (fun z : Circle L => ((cltRegCircle hρ L hh f) z : ℂ)) 2 (arclength L) :=
    (loopMasterLengthTest L (cltRegCircle hρ L hh f)
      (cltRegCircle_contDiff hρ L hh f)).property
  have hGm : MemLp (fun x : UnitAddCircle => (loopMasterPullback L (cltRegCircle hρ L hh f) x : ℂ))
      2 volume :=
    loopMasterPullback_memLp L ⟨cltRegCircle hρ L hh f, hGL2⟩
  have hξm : MemLp (fun x : UnitAddCircle => (loopMasterPullback L f.val x : ℂ)) 2 volume :=
    loopMasterPullback_memLp L f
  have hDm : MemLp (fun x : UnitAddCircle =>
      ((loopMasterPullback L (cltRegCircle hρ L hh f) x - loopMasterPullback L f.val x : ℝ) : ℂ))
      2 volume := by
    refine MemLp.ae_eq (Eventually.of_forall fun x => ?_) (hGm.sub hξm)
    simp [Complex.ofReal_sub]
  have hs := hasSum_norm_sq_circleCoeff (fun x => loopMasterPullback L (cltRegCircle hρ L hh f) x -
    loopMasterPullback L f.val x) hDm
  have hcoeff : ∀ k : ℤ, ‖circleCoeff (fun x => loopMasterPullback L (cltRegCircle hρ L hh f) x -
      loopMasterPullback L f.val x) k‖ ^ 2 = ‖circleCoeff (loopMasterPullback L f.val) k‖ ^ 2 *
        (mollifierFT ρ (h * k / L.val) - 1) ^ 2 := by
    intro k
    rw [circleCoeff_sub_of_memLp _ _ hGm hξm k, circleCoeff_pullback_cltRegCircle hρ L f hh k]
    have hm : circleCoeff (loopMasterPullback L f.val) k * (mollifierFT ρ (h * k / L.val) : ℂ) -
        circleCoeff (loopMasterPullback L f.val) k =
          circleCoeff (loopMasterPullback L f.val) k *
            ((mollifierFT ρ (h * k / L.val) - 1 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hm, norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]
  have hint : ∫ x, (loopMasterPullback L (cltRegCircle hρ L hh f) x -
      loopMasterPullback L f.val x) ^ 2 = ∫ x, (loopMasterPullback L (cltRegCircle hρ L hh f) x -
      loopMasterPullback L f.val x) * (loopMasterPullback L (cltRegCircle hρ L hh f) x -
      loopMasterPullback L f.val x) :=
    integral_congr_ae (Eventually.of_forall fun x => sq _)
  rw [hint, ← hs.tsum_eq]
  exact tsum_congr hcoeff

/-- The `L²` distance of the pulled-back regularization tends to zero: for every positive `ε`
there is a radius `δ` such that all smaller positive radii give distance below `ε`. -/
theorem exists_pullback_regularize_sub_lt {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (L : Length)
    (f : {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)}) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : ℝ, ∀ hh : 0 < h, h < δ →
      ∫ x : UnitAddCircle, (loopMasterPullback L (cltRegCircle hρ L hh f) x -
        loopMasterPullback L f.val x) ^ 2 < ε := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hξm : MemLp (fun x : UnitAddCircle => (loopMasterPullback L f.val x : ℂ)) 2 volume :=
    loopMasterPullback_memLp L f
  have hs := hasSum_norm_sq_circleCoeff (loopMasterPullback L f.val) hξm
  have hT := tendsto_tsum_mollifier_sub_sq hρ L.property
    (c := fun k : ℤ => ‖circleCoeff (loopMasterPullback L f.val) k‖) hs.summable
  have hev := (Metric.tendsto_nhds.mp hT) ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  refine ⟨δ, hδ, fun h hh hlt => ?_⟩
  rw [integral_sq_pullback_regularize_sub hρ L f hh]
  have hd := hball (y := h) (by rw [Real.dist_eq, sub_zero, abs_of_pos hh]; exact hlt) hh
  rw [Real.dist_eq, sub_zero] at hd
  exact (abs_lt.mp hd).2

end Riesz1

end
