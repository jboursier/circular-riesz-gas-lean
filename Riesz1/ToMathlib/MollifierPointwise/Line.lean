/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.Basic

/-!
# Pointwise regularization on the line

Line version of Lemma 5.1. Let `ρ` be a mollifier
(`IsMollifier ρ`), let `0 ≤ γ < 1` and let `f : ℝ → ℝ` be locally integrable with
`|f(y)| ≤ |y| ^ (-γ)` for almost every `y ≠ 0`. Then, for all `0 < h` and `x`,
`|(f ⋆ ρ_h)(x)| ≤ C max(|x|, h) ^ (-γ)`, with `C` depending only on `ρ` and `γ`.

If in addition `γ > 0`, `f` is `C¹` off zero and `|f'(y)| ≤ |y| ^ (-1 - γ)` for `y ≠ 0`, then
`f ⋆ ρ_h` is differentiable and `|(f ⋆ ρ_h)'(x)| ≤ C max(|x|, h) ^ (-1 - γ)`.

The derivative estimate uses both hypotheses. The derivative hypothesis alone does not suffice on
the line: the function `f = (J/2) sign(y)` satisfies it for every `J`, while
`(f ⋆ ρ_h)'(0) = -J ρ_h(0)` is unbounded in `J`.

Main results:
* `Riesz1.mollifyLine_sup_bound`: the sup estimate, for `0 ≤ γ < 1`.
* `Riesz1.mollifyLine_deriv_bound`: the derivative estimate, for `0 < γ < 1`.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology
open scoped ContDiff

namespace Riesz1

variable {ρ : ℝ → ℝ} {h γ : ℝ}

/-- The pointwise hypothesis, stated for almost every point (the point `0` is a null set). -/
lemma ae_abs_le_of_ae_ne_zero {f : ℝ → ℝ} (γ : ℝ)
    (hfb : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 0 → |f y| ≤ |y| ^ (-γ)) :
    ∀ᵐ y ∂(volume : Measure ℝ), |f y| ≤ |y| ^ (-γ) := by
  have h0 : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 0 := by
    rw [ae_iff]
    simp
  exact (hfb.and h0).mono fun y hy => hy.1 hy.2

/-- Window bound near the singularity: if `|x| ≤ h`, the integral of `|f|` over the window
`(x - h/2, x + h/2)` is at most `2 (3h/2)^(1-γ) / (1-γ)`, provided `|f(y)| ≤ |y|^(-γ)` for
almost every `y` in `[-3h/2, 3h/2]`. -/
lemma window_abs_le_near {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (hγ1 : γ < 1)
    (hh : 0 < h) (hfb : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Icc (-(3 / 2 * h)) (3 / 2 * h) →
      |f y| ≤ |y| ^ (-γ)) {x : ℝ} (hx : |x| ≤ h) :
    ∫ y in Ioo (x - h / 2) (x + h / 2), |f y| ≤ 2 * (3 / 2 * h) ^ (1 - γ) / (1 - γ) := by
  have hr : -1 < -γ := by linarith
  have ha : 0 ≤ 3 / 2 * h := by linarith
  have hsub : Ioo (x - h / 2) (x + h / 2) ⊆ Icc (-(3 / 2 * h)) (3 / 2 * h) := by
    intro y hy
    rw [abs_le] at hx
    rw [mem_Ioo] at hy
    exact ⟨by linarith [hy.1, hx.1], by linarith [hy.2, hx.2]⟩
  have hint_abs : IntegrableOn (fun y => |f y|) (Ioo (x - h / 2) (x + h / 2)) :=
    ((hf.integrableOn_isCompact (isCompact_Icc (a := -(3 / 2 * h)) (b := 3 / 2 * h))).mono_set
      hsub).abs
  have hint_rpow : IntegrableOn (fun y : ℝ => |y| ^ (-γ)) (Ioo (x - h / 2) (x + h / 2)) :=
    (integrableOn_abs_rpow hr ha).mono_set hsub
  have hae : ∀ᵐ y ∂(volume.restrict (Ioo (x - h / 2) (x + h / 2))),
      |f y| ≤ |y| ^ (-γ) := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hfb] with y hy hyW
    exact hy (hsub hyW)
  calc ∫ y in Ioo (x - h / 2) (x + h / 2), |f y|
      ≤ ∫ y in Ioo (x - h / 2) (x + h / 2), |y| ^ (-γ) :=
        setIntegral_mono_ae_restrict hint_abs hint_rpow hae
    _ ≤ ∫ y in Icc (-(3 / 2 * h)) (3 / 2 * h), |y| ^ (-γ) :=
        setIntegral_mono_set (integrableOn_abs_rpow hr ha)
          (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (abs_nonneg y) _)
          (hsub.eventuallyLE)
    _ = 2 * (3 / 2 * h) ^ (1 - γ) / (1 - γ) := integral_abs_rpow_symm hγ1 ha

/-- If `δ` is `1`-Lipschitz for the absolute value, `|u| < h/2`, `h ≤ δ x` and
`|x' - x| < δ x / 4`, then `δ x / 4 ≤ δ (x' - u)`. -/
lemma le_of_lipschitz_sub {δ : ℝ → ℝ} (hδ : ∀ y z, δ y ≤ δ z + |y - z|) {x x' u h : ℝ}
    (hx : h ≤ δ x) (hu : |u| < h / 2) (hx' : |x' - x| < δ x / 4) : δ x / 4 ≤ δ (x' - u) := by
  have h1 := hδ x (x' - u)
  have h2 : |x - (x' - u)| ≤ |x' - x| + |u| := by
    have e : x - (x' - u) = -(x' - x) + u := by ring
    calc |x - (x' - u)| = |-(x' - x) + u| := by rw [e]
      _ ≤ |-(x' - x)| + |u| := abs_add_le _ _
      _ = |x' - x| + |u| := by rw [abs_neg]
  linarith

/-- The absolute value is `1`-Lipschitz (the triangle inequality). -/
lemma abs_lipschitz : ∀ y z : ℝ, |y| ≤ |z| + |y - z| := fun y z => by
  linarith [abs_sub_abs_le_abs_sub y z]

/-- The far window estimate for a distance-like function `δ` (for `δ = |·|` on the line, and
for the circle distance on a circle). -/
lemma window_abs_le_far_gen {δ f : ℝ → ℝ} (hδ : ∀ y z, δ y ≤ δ z + |y - z|)
    (hf : LocallyIntegrable f volume) (hγ0 : 0 ≤ γ) (hh : 0 < h)
    (hfb : ∀ᵐ y ∂(volume : Measure ℝ), δ y ≠ 0 → |f y| ≤ δ y ^ (-γ)) {x : ℝ} (hx : h ≤ δ x) :
    ∫ y in Ioo (x - h / 2) (x + h / 2), |f y| ≤ h * (δ x / 2) ^ (-γ) := by
  have hpos : 0 < δ x / 2 := by linarith
  have hW : ∀ y ∈ Ioo (x - h / 2) (x + h / 2), δ x / 2 ≤ δ y := by
    intro y hy
    rw [mem_Ioo] at hy
    have h1 : |x - y| < h / 2 := by
      rw [abs_lt]
      constructor <;> linarith [hy.1, hy.2]
    have h2 := hδ x y
    linarith
  have hint_abs : IntegrableOn (fun y => |f y|) (Ioo (x - h / 2) (x + h / 2)) :=
    ((hf.integrableOn_isCompact (isCompact_Icc (a := x - h / 2) (b := x + h / 2))).mono_set
      Ioo_subset_Icc_self).abs
  have hbound : ∀ᵐ y ∂(volume.restrict (Ioo (x - h / 2) (x + h / 2))),
      |f y| ≤ (δ x / 2) ^ (-γ) := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hfb] with y hy hyW
    have hne : δ y ≠ 0 := (lt_of_lt_of_le hpos (hW y hyW)).ne'
    exact (hy hne).trans (Real.rpow_le_rpow_of_nonpos hpos (hW y hyW) (by linarith))
  calc ∫ y in Ioo (x - h / 2) (x + h / 2), |f y|
      ≤ ∫ y in Ioo (x - h / 2) (x + h / 2), (δ x / 2) ^ (-γ) :=
        setIntegral_mono_ae_restrict hint_abs (integrableOn_const (by simp)) hbound
    _ = h * (δ x / 2) ^ (-γ) := by
        rw [setIntegral_const, measureReal_def, Real.volume_Ioo, smul_eq_mul,
          ENNReal.toReal_ofReal (by linarith)]
        ring

/-- The line convolution is bounded by the window integral of `|f|` against the mollifier. -/
lemma abs_mollifyLine_le_window (hρ : IsMollifier ρ) (hh : 0 < h) {M' : ℝ}
    (hM : ∀ x, |ρ x| ≤ M') {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (x : ℝ) :
    |mollifyLine ρ h f x| ≤ M' * h⁻¹ * ∫ y in Ioo (x - h / 2) (x + h / 2), |f y| := by
  exact norm_integral_mul_le_window (g := f) (φ := scaledMollifier ρ h) (x := x)
    (r := h / 2) (K := M' * h⁻¹) hf (contDiff_scaledMollifier hρ).continuous
    (fun u => abs_scaledMollifier_le hh hM u) (fun u hu => scaledMollifier_eq_zero hρ hh hu)

/-- The sup estimate on the line: for `0 ≤ γ < 1`, the convolution `f ⋆ ρ_h` is bounded by
`C max(|x|, h) ^ (-γ)`, uniformly in `f`, `h` and `x`. -/
theorem mollifyLine_sup_bound (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ, LocallyIntegrable f volume →
      (∀ᵐ y ∂(volume : Measure ℝ), y ≠ 0 → |f y| ≤ |y| ^ (-γ)) →
      ∀ h : ℝ, 0 < h → ∀ x : ℝ, |mollifyLine ρ h f x| ≤ C * (max |x| h) ^ (-γ) := by
  obtain ⟨M, hM0, hM⟩ := hρ.exists_bound
  set M' := M + 1 with hM'
  have hM'pos : 0 < M' := by linarith
  have hM'' : ∀ x, |ρ x| ≤ M' := fun x => (hM x).trans (by linarith)
  have hA0 : 0 ≤ 2 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ) := by
    have : 0 < 1 - γ := by linarith
    positivity
  refine ⟨M' * (2 ^ γ + 2 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)), ?_, ?_⟩
  · have : 0 < 1 - γ := by linarith
    have hA : 0 < 2 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ) := by positivity
    have h2 : 0 < (2 : ℝ) ^ γ := by positivity
    exact mul_pos hM'pos (by linarith)
  intro f hf hfb h hh x
  have hmol := abs_mollifyLine_le_window hρ hh hM'' hf x
  have hfb' : ∀ᵐ y ∂(volume : Measure ℝ), |y| ≠ 0 → |f y| ≤ |y| ^ (-γ) :=
    hfb.mono fun y hy hne => hy (abs_ne_zero.1 hne)
  rcases le_total h |x| with hx | hx
  · -- Far from the singularity: the window integral is controlled by `|x| / 2`.
    have hfar := window_abs_le_far_gen abs_lipschitz hf hγ0 hh hfb' hx
    have hmax : max |x| h = |x| := max_eq_left hx
    rw [hmax]
    have hx0 : 0 ≤ |x| ^ (-γ) := Real.rpow_nonneg (abs_nonneg x) _
    calc |mollifyLine ρ h f x|
        ≤ M' * h⁻¹ * (h * (|x| / 2) ^ (-γ)) :=
          hmol.trans (mul_le_mul_of_nonneg_left hfar (by positivity))
      _ = M' * (|x| ^ (-γ) * 2 ^ γ) := by
          rw [div_two_rpow_neg (abs_nonneg x)]
          field_simp
      _ ≤ M' * (2 ^ γ + 2 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)) * |x| ^ (-γ) := by
          have h2 : 0 ≤ (2 : ℝ) ^ γ := by positivity
          have hA : 0 ≤ 2 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ) := hA0
          have : 0 ≤ M' * (2 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)) * |x| ^ (-γ) :=
            mul_nonneg (mul_nonneg hM'pos.le hA) hx0
          nlinarith
  · -- Near the singularity: the window integral is controlled by `(3h/2)^(1-γ)`.
    have hnear_hyp : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Icc (-(3 / 2 * h)) (3 / 2 * h) →
        |f y| ≤ |y| ^ (-γ) :=
      (ae_abs_le_of_ae_ne_zero γ hfb).mono fun y hy _ => hy
    have hnear := window_abs_le_near hf hγ1 hh hnear_hyp hx
    have hmax : max |x| h = h := max_eq_right hx
    rw [hmax]
    have hkey : M' * h⁻¹ * (2 * (3 / 2 * h) ^ (1 - γ) / (1 - γ)) =
        M' * (2 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)) * h ^ (-γ) := by
      rw [Real.mul_rpow (by norm_num) hh.le, ← inv_mul_rpow_one_sub hh]
      ring
    have hhp : 0 ≤ h ^ (-γ) := Real.rpow_nonneg hh.le _
    have h2 : 0 ≤ (2 : ℝ) ^ γ := by positivity
    calc |mollifyLine ρ h f x|
        ≤ M' * h⁻¹ * (2 * (3 / 2 * h) ^ (1 - γ) / (1 - γ)) :=
          hmol.trans (mul_le_mul_of_nonneg_left hnear (by positivity))
      _ = M' * (2 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)) * h ^ (-γ) := hkey
      _ ≤ M' * (2 ^ γ + 2 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)) * h ^ (-γ) := by
          have : 0 ≤ M' * 2 ^ γ * h ^ (-γ) := mul_nonneg (mul_nonneg hM'pos.le h2) hhp
          nlinarith

/-- Away from the singularity, the derivative of `f ⋆ ρ_h` is `∫ f'(x - u) ρ_h(u) du`, for a
distance-like `δ` with `δ(x) ≥ h`. -/
lemma hasDerivAt_mollifyLine_far_gen {δ f : ℝ → ℝ} (hδ : ∀ y z, δ y ≤ δ z + |y - z|)
    (hγ0 : 0 ≤ γ) (hρ : IsMollifier ρ) (hh : 0 < h) (hf : LocallyIntegrable f volume)
    (hdiff : ∀ y, δ y ≠ 0 → DifferentiableAt ℝ f y)
    (hfd : ∀ y, δ y ≠ 0 → |deriv f y| ≤ δ y ^ (-1 - γ)) {x : ℝ} (hx : h ≤ δ x) :
    HasDerivAt (mollifyLine ρ h f) (∫ u, deriv f (x - u) * scaledMollifier ρ h u) x := by
  have hfun : mollifyLine ρ h f = fun x' => ∫ u, f (x' - u) * scaledMollifier ρ h u :=
    funext (mollifyLine_eq f)
  rw [hfun]
  have hε0 : 0 < δ x / 4 := by linarith
  have hρc : Continuous (scaledMollifier ρ h) := (contDiff_scaledMollifier hρ).continuous
  have hρi : Integrable (scaledMollifier ρ h) :=
    hρc.integrable_of_hasCompactSupport (hasCompactSupport_scaledMollifier hρ hh)
  have hint : Integrable (fun u => f (x - u) * scaledMollifier ρ h u) := by
    have := (integrable_mul_scaled_sub hρ hh hf x).comp_sub_left x
    simpa only [sub_sub_cancel] using this
  have hmeas : ∀ x' : ℝ, AEStronglyMeasurable (fun u => f (x' - u) * scaledMollifier ρ h u)
      volume := by
    intro x'
    have hfm : AEStronglyMeasurable (fun u => f (x' - u)) volume :=
      hf.aestronglyMeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant volume x')
    exact hfm.mul hρc.aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable (fun u => deriv f (x - u) * scaledMollifier ρ h u)
      volume :=
    (((measurable_deriv f).comp (measurable_const.sub measurable_id)).mul hρc.measurable
      ).aestronglyMeasurable
  have hD := _root_.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x' u => f (x' - u) * scaledMollifier ρ h u)
    (F' := fun x' u => deriv f (x' - u) * scaledMollifier ρ h u)
    (x₀ := x) (s := Metric.ball x (δ x / 4))
    (bound := fun u => (δ x / 4) ^ (-1 - γ) * scaledMollifier ρ h u)
    (Metric.ball_mem_nhds x hε0) (Filter.Eventually.of_forall hmeas) hint hdmeas ?_
    (hρi.const_mul _) ?_
  · exact hD.2
  · refine Filter.Eventually.of_forall fun u x' hx' => ?_
    rw [Metric.mem_ball, Real.dist_eq] at hx'
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (scaledMollifier_nonneg hρ hh u)]
    rcases eq_or_lt_of_le (scaledMollifier_nonneg hρ hh u) with h0 | hpos
    · rw [← h0]
      simp
    · have hu : |u| < h / 2 := by
        by_contra hc
        exact hpos.ne' (scaledMollifier_eq_zero hρ hh (not_lt.1 hc))
      have hd := le_of_lipschitz_sub hδ hx hu hx'
      have hne : δ (x' - u) ≠ 0 := (lt_of_lt_of_le hε0 hd).ne'
      exact mul_le_mul_of_nonneg_right
        ((hfd _ hne).trans (Real.rpow_le_rpow_of_nonpos hε0 hd (by linarith)))
        (scaledMollifier_nonneg hρ hh u)
  · refine Filter.Eventually.of_forall fun u x' hx' => ?_
    rw [Metric.mem_ball, Real.dist_eq] at hx'
    by_cases hz : scaledMollifier ρ h u = 0
    · simp only [hz, mul_zero]
      exact hasDerivAt_const _ _
    · have hu : |u| < h / 2 := by
        by_contra hc
        exact hz (scaledMollifier_eq_zero hρ hh (not_lt.1 hc))
      have hd := le_of_lipschitz_sub hδ hx hu hx'
      have hne : δ (x' - u) ≠ 0 := (lt_of_lt_of_le hε0 hd).ne'
      exact (((hdiff _ hne).hasDerivAt).comp_sub_const x' u).mul_const _

/-- The far derivative is bounded by `(δ x / 2)^(-1-γ)`. -/
lemma abs_integral_deriv_far_le_gen {δ f : ℝ → ℝ} (hδ : ∀ y z, δ y ≤ δ z + |y - z|)
    (hγ0 : 0 ≤ γ) (hρ : IsMollifier ρ) (hh : 0 < h)
    (hfd : ∀ y, δ y ≠ 0 → |deriv f y| ≤ δ y ^ (-1 - γ)) {x : ℝ} (hx : h ≤ δ x) :
    |∫ u, deriv f (x - u) * scaledMollifier ρ h u| ≤ (δ x / 2) ^ (-1 - γ) := by
  have hbound : ∀ u, ‖deriv f (x - u) * scaledMollifier ρ h u‖ ≤
      (δ x / 2) ^ (-1 - γ) * scaledMollifier ρ h u := by
    intro u
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (scaledMollifier_nonneg hρ hh u)]
    rcases eq_or_lt_of_le (scaledMollifier_nonneg hρ hh u) with h0 | hpos
    · rw [← h0]
      simp
    · have hu : |u| < h / 2 := by
        by_contra hc
        exact hpos.ne' (scaledMollifier_eq_zero hρ hh (not_lt.1 hc))
      have hd : δ x / 2 ≤ δ (x - u) := by
        have h1 := hδ x (x - u)
        rw [sub_sub_cancel] at h1
        linarith
      have hne : δ (x - u) ≠ 0 := (lt_of_lt_of_le (by linarith) hd).ne'
      exact mul_le_mul_of_nonneg_right
        ((hfd _ hne).trans (Real.rpow_le_rpow_of_nonpos (by linarith) hd (by linarith)))
        (scaledMollifier_nonneg hρ hh u)
  have hρi : Integrable (scaledMollifier ρ h) :=
    (contDiff_scaledMollifier hρ).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_scaledMollifier hρ hh)
  have hgi : Integrable (fun u => (δ x / 2) ^ (-1 - γ) * scaledMollifier ρ h u) :=
    hρi.const_mul _
  calc |∫ u, deriv f (x - u) * scaledMollifier ρ h u|
      = ‖∫ u, deriv f (x - u) * scaledMollifier ρ h u‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ u, (δ x / 2) ^ (-1 - γ) * scaledMollifier ρ h u :=
        MeasureTheory.norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall hbound)
    _ = (δ x / 2) ^ (-1 - γ) := by
        rw [MeasureTheory.integral_const_mul, integral_scaledMollifier hρ hh, mul_one]

/-- The derivative estimate on the line: for `0 < γ < 1`, the convolution `f ⋆ ρ_h` is
differentiable and its derivative is bounded by `C max(|x|, h) ^ (-1 - γ)`, uniformly in `f`,
`h` and `x`. -/
theorem mollifyLine_deriv_bound (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ, LocallyIntegrable f volume →
      (∀ᵐ y ∂(volume : Measure ℝ), y ≠ 0 → |f y| ≤ |y| ^ (-γ)) →
      ContDiffOn ℝ 1 f {0}ᶜ → (∀ y : ℝ, y ≠ 0 → |deriv f y| ≤ |y| ^ (-1 - γ)) →
      ∀ h : ℝ, 0 < h → ∀ x : ℝ, ∃ D : ℝ, HasDerivAt (mollifyLine ρ h f) D x ∧
        |D| ≤ C * (max |x| h) ^ (-1 - γ) := by
  obtain ⟨M, hM0, hM⟩ := hρ.exists_bound_deriv
  set M' := M + 1 with hM'
  have hM'pos : 0 < M' := by linarith
  have hM1 : 1 ≤ M' := by linarith
  have hM'' : ∀ x, |deriv ρ x| ≤ M' := fun x => (hM x).trans (by linarith)
  have hA0 : 0 ≤ 2 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ) := by
    have : 0 < 1 - γ := by linarith
    positivity
  have h21 : 0 < (2 : ℝ) ^ (1 + γ) := by positivity
  refine ⟨M' * (2 ^ (1 + γ) + 2 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)), ?_, ?_⟩
  · exact mul_pos hM'pos (by linarith)
  intro f hf hfb hC1 hfd h hh x
  rcases le_total h |x| with hx | hx
  · -- Far from the singularity.
    have hdiff : ∀ y : ℝ, |y| ≠ 0 → DifferentiableAt ℝ f y := fun y hy =>
      (hC1.differentiableOn (by norm_num)).differentiableAt
        (isOpen_compl_singleton.mem_nhds (abs_ne_zero.1 hy))
    have hfd' : ∀ y : ℝ, |y| ≠ 0 → |deriv f y| ≤ |y| ^ (-1 - γ) :=
      fun y hy => hfd y (abs_ne_zero.1 hy)
    refine ⟨∫ u, deriv f (x - u) * scaledMollifier ρ h u,
      hasDerivAt_mollifyLine_far_gen abs_lipschitz hγ0.le hρ hh hf hdiff hfd' hx, ?_⟩
    have hb := abs_integral_deriv_far_le_gen abs_lipschitz hγ0.le hρ hh hfd' hx
    have hmax : max |x| h = |x| := max_eq_left hx
    rw [hmax]
    have hx0 : 0 ≤ |x| ^ (-1 - γ) := Real.rpow_nonneg (abs_nonneg x) _
    have e : (|x| / 2) ^ (-1 - γ) = |x| ^ (-1 - γ) * 2 ^ (1 + γ) := by
      rw [show (-1 - γ : ℝ) = -(1 + γ) by ring, div_two_rpow_neg (abs_nonneg x)]
    have hA0' : 0 ≤ 2 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ) := hA0
    nlinarith [mul_nonneg (sub_nonneg.2 hM1) (mul_nonneg h21.le hx0),
      mul_nonneg (mul_nonneg hM'pos.le hA0') hx0]
  · -- Near the singularity: differentiate the kernel.
    refine ⟨_, hasDerivAt_mollifyLine hρ hh hf x, ?_⟩
    have hmax : max |x| h = h := max_eq_right hx
    rw [hmax]
    have hw := norm_integral_mul_le_window (g := f) (φ := deriv (scaledMollifier ρ h)) (x := x)
      (r := h / 2) (K := M' * (h⁻¹ * h⁻¹)) hf
      ((contDiff_scaledMollifier hρ).continuous_deriv (by simp))
      (fun u => abs_deriv_scaledMollifier_le hρ hh hM'' u)
      (fun u hu => deriv_scaledMollifier_eq_zero hρ hh hu)
    have hnear_hyp : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Icc (-(3 / 2 * h)) (3 / 2 * h) →
        |f y| ≤ |y| ^ (-γ) :=
      (ae_abs_le_of_ae_ne_zero γ hfb).mono fun y hy _ => hy
    have hnear := window_abs_le_near hf hγ1 hh hnear_hyp hx
    have hkey : M' * (h⁻¹ * h⁻¹) * (2 * (3 / 2 * h) ^ (1 - γ) / (1 - γ)) =
        M' * (2 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)) * h ^ (-1 - γ) := by
      rw [Real.mul_rpow (by norm_num) hh.le, ← inv_mul_inv_mul_rpow_one_sub hh]
      ring
    have hhp : 0 ≤ h ^ (-1 - γ) := Real.rpow_nonneg hh.le _
    have hMpos : 0 ≤ M' * (h⁻¹ * h⁻¹) := by positivity
    calc |∫ y, f y * deriv (scaledMollifier ρ h) (x - y)|
        ≤ M' * (h⁻¹ * h⁻¹) * ∫ y in Ioo (x - h / 2) (x + h / 2), |f y| := hw
      _ ≤ M' * (h⁻¹ * h⁻¹) * (2 * (3 / 2 * h) ^ (1 - γ) / (1 - γ)) :=
          mul_le_mul_of_nonneg_left hnear hMpos
      _ = M' * (2 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)) * h ^ (-1 - γ) := hkey
      _ ≤ M' * (2 ^ (1 + γ) + 2 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)) * h ^ (-1 - γ) := by
          nlinarith [mul_nonneg (mul_nonneg hM'pos.le h21.le) hhp]

end Riesz1
