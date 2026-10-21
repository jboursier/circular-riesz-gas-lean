/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.Basic
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Smoothing a bounded `C¹` function

For the Gibbs integration by parts of Theorem 3, a `C¹` function `u` with bounded `u`
and `u'` is approximated by the smooth functions `u_ε = u ⋆ ρ_ε` of the mollifier family. The
approximation has three properties, uniformly in `ε > 0`:

* `u_ε` is `C^∞`, so `u_ε ∘ G` is a torus-smooth test in Proposition 5.5.
* `|u_ε| ≤ sup |u|` and `|u_ε'| ≤ sup |u'|`, since `ρ_ε ≥ 0` has integral one.
* `u_ε → u` and `u_ε' → u'` pointwise as `ε ↓ 0`, by the approximate identity.

The convolution `u_ε(x) = ∫ u(x - t) ρ_ε(t) dt` is `mollifyLine` of `Riesz1.MollifierPointwise`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The scaled mollifier is nonnegative for `ε > 0`. -/
lemma scaledMollifier_nonneg' {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    0 ≤ scaledMollifier ρ ε y := by
  unfold scaledMollifier
  exact mul_nonneg (inv_nonneg.mpr hε.le) (hρ.nonneg _)

/-- The scaled mollifier is integrable for `ε > 0`. -/
lemma integrable_scaledMollifier' {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (scaledMollifier ρ ε) volume :=
  (contDiff_scaledMollifier hρ (h := ε)).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_scaledMollifier hρ hε)

/-- The mollified function `u_ε(x) = ∫ u(x - t) ρ_ε(t) dt` is `C^∞` for locally integrable `u`. -/
lemma contDiff_mollifyLine_of_locallyIntegrable {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) :
    ContDiff ℝ ∞ (mollifyLine ρ ε f) := by
  have hfun : mollifyLine ρ ε f = convolution f (scaledMollifier ρ ε)
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext y
    simp [mollifyLine, convolution_def]
  rw [hfun]
  exact HasCompactSupport.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (hasCompactSupport_scaledMollifier hρ hε) hf (contDiff_scaledMollifier hρ (h := ε))

/-- The derivative of `u_ε` is `∫ u'(x - t) ρ_ε(t) dt`, when `u` is `C¹` with bounded `u` and
`u'`. -/
lemma hasDerivAt_mollifyLine_of_bounded {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) {M0 M1 : ℝ} (hM0 : ∀ y, |u y| ≤ M0)
    (hM1 : ∀ y, |deriv u y| ≤ M1) (x : ℝ) :
    HasDerivAt (mollifyLine ρ ε u) (∫ t, deriv u (x - t) * scaledMollifier ρ ε t) x := by
  have hdiff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hcont : Continuous (deriv u) := hu.continuous_deriv (by norm_num)
  have hφi : Integrable (scaledMollifier ρ ε) volume := integrable_scaledMollifier' hρ hε
  have hφc : Continuous (scaledMollifier ρ ε) :=
    (contDiff_scaledMollifier hρ (h := ε)).continuous
  have hmollEq : mollifyLine ρ ε u = fun y => ∫ t, u (y - t) * scaledMollifier ρ ε t := by
    funext y
    rw [mollifyLine_eq]
  have hint : ∀ y, Integrable (fun t => u (y - t) * scaledMollifier ρ ε t) volume := by
    intro y
    refine Integrable.mono' (hφi.const_mul M0) ?_ (Eventually.of_forall fun t => ?_)
    · exact ((hu.continuous.comp (continuous_const.sub continuous_id)).mul hφc).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (scaledMollifier_nonneg' hρ hε t)]
      exact mul_le_mul_of_nonneg_right (hM0 _) (scaledMollifier_nonneg' hρ hε t)
  have hbound : Integrable (fun t => M1 * scaledMollifier ρ ε t) volume := hφi.const_mul M1
  have hF'meas : AEStronglyMeasurable (fun t => deriv u (x - t) * scaledMollifier ρ ε t) volume :=
    ((hcont.comp (continuous_const.sub continuous_id)).mul hφc).aestronglyMeasurable
  have hF'bd : ∀ᵐ t ∂(volume : Measure ℝ), ∀ y ∈ (univ : Set ℝ),
      ‖deriv u (y - t) * scaledMollifier ρ ε t‖ ≤ M1 * scaledMollifier ρ ε t := by
    refine Eventually.of_forall fun t y _ => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (scaledMollifier_nonneg' hρ hε t)]
    exact mul_le_mul_of_nonneg_right (hM1 _) (scaledMollifier_nonneg' hρ hε t)
  have hF'deriv : ∀ᵐ t ∂(volume : Measure ℝ), ∀ y ∈ (univ : Set ℝ),
      HasDerivAt (fun y => u (y - t) * scaledMollifier ρ ε t)
        (deriv u (y - t) * scaledMollifier ρ ε t) y := by
    refine Eventually.of_forall fun t y _ => ?_
    have hd : HasDerivAt (fun y => u (y - t)) (deriv u (y - t)) y :=
      ((hdiff (y - t)).hasDerivAt).comp_sub_const y t
    exact hd.mul_const _
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun y t => u (y - t) * scaledMollifier ρ ε t)
    (F' := fun y t => deriv u (y - t) * scaledMollifier ρ ε t) (x₀ := x) (s := univ)
    (bound := fun t => M1 * scaledMollifier ρ ε t) univ_mem
    (Eventually.of_forall fun y => (hint y).aestronglyMeasurable)
    (hint x) hF'meas hF'bd hbound hF'deriv
  rw [hmollEq]
  exact hderiv.2

/-- Bound on the mollified function: `|u_ε(x)| ≤ M` when `|u| ≤ M` and `ε > 0`. -/
lemma abs_mollifyLine_le_of_bound {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {u : ℝ → ℝ} {M : ℝ} (hM : ∀ y, |u y| ≤ M) (x : ℝ) :
    |mollifyLine ρ ε u x| ≤ M := by
  rw [mollifyLine_eq]
  have hφi : Integrable (scaledMollifier ρ ε) volume := integrable_scaledMollifier' hρ hε
  have hle : ∀ᵐ t ∂(volume : Measure ℝ), ‖u (x - t) * scaledMollifier ρ ε t‖ ≤
      M * scaledMollifier ρ ε t := by
    refine Eventually.of_forall fun t => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (scaledMollifier_nonneg' hρ hε t)]
    exact mul_le_mul_of_nonneg_right (hM _) (scaledMollifier_nonneg' hρ hε t)
  have h := norm_integral_le_of_norm_le (μ := volume) (hφi.const_mul M) hle
  rw [integral_const_mul, integral_scaledMollifier hρ hε, mul_one, Real.norm_eq_abs] at h
  exact h

/-- The approximate identity for a continuous `g`: `∫ g(x - t) ρ_ε(t) dt → g(x)` as `ε ↓ 0`. -/
lemma tendsto_mollifyLine_of_continuous {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {g : ℝ → ℝ}
    (hg : Continuous g) (x : ℝ) :
    Tendsto (fun ε : ℝ => ∫ t, g (x - t) * scaledMollifier ρ ε t) (𝓝[>] 0) (𝓝 (g x)) := by
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := eventually_mem_nhdsWithin
  have hsupp : Tendsto (fun ε : ℝ => Function.support (scaledMollifier ρ ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (0 : ℝ)).smallSets := by
    rw [tendsto_smallSets_iff]
    intro V hV
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hV
    have hwin : Ioo (0 : ℝ) (2 * r) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by linarith)
    filter_upwards [hwin] with ε hε
    intro y hy
    apply hball
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    by_contra hcon
    have hcon' : r ≤ |y| := not_lt.mp hcon
    exact (Function.mem_support.mp hy) (scaledMollifier_eq_zero hρ hε.1 (by linarith [hε.2]))
  have hcg : Tendsto (Function.uncurry (fun _ : ℝ => g)) ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) (𝓝 (g x)) :=
    (hg.tendsto x).comp tendsto_snd
  have hconv := MeasureTheory.convolution_tendsto_right (μ := volume) (l := 𝓝[>] (0 : ℝ))
    (g := fun _ : ℝ => g) (x₀ := x) (z₀ := g x) (φ := fun ε t => scaledMollifier ρ ε t)
    (k := fun _ => x)
    (hpos.mono fun ε hε t => scaledMollifier_nonneg' hρ hε t)
    (hpos.mono fun ε hε => integral_scaledMollifier hρ hε)
    hsupp (Eventually.of_forall fun _ => hg.aestronglyMeasurable) hcg tendsto_const_nhds
  refine Tendsto.congr (fun ε => ?_) hconv
  rw [convolution_def]
  congr 1
  funext t
  simp [mul_comm]

/-- The approximate identity for the derivative: `∫ u'(x - t) ρ_ε(t) dt → u'(x)` as `ε ↓ 0`. -/
lemma tendsto_mollifyLine_deriv {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 1 u) (x : ℝ) :
    Tendsto (fun ε : ℝ => ∫ t, deriv u (x - t) * scaledMollifier ρ ε t) (𝓝[>] 0)
      (𝓝 (deriv u x)) :=
  tendsto_mollifyLine_of_continuous hρ (hu.continuous_deriv (by norm_num)) x

/-- The approximate identity for the function: `u_ε(x) → u(x)` as `ε ↓ 0`. -/
lemma tendsto_mollifyLine_fun {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {u : ℝ → ℝ}
    (hu : Continuous u) (x : ℝ) :
    Tendsto (fun ε : ℝ => mollifyLine ρ ε u x) (𝓝[>] 0) (𝓝 (u x)) := by
  refine (tendsto_mollifyLine_of_continuous hρ hu x).congr fun ε => ?_
  rw [mollifyLine_eq]

end Riesz1

end
