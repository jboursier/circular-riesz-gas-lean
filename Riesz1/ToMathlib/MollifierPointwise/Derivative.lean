/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.Circle

/-!
# Smoothness and derivatives of the circle regularization

The regularization `f_h` of a locally integrable `L`-periodic function `f` is smooth. Each
derivative is the convolution with the derivative of the periodized kernel. For `f` of class `C^m`,
the `m`-th derivative of `f_h` is also the convolution of `f^{(m)}` with the kernel.

This file proves these statements for every length `L > 0`, every `0 < h` and every mollifier `ρ`:
* `Riesz1.contDiff_circleMollify`: `f_h` is smooth.
* `Riesz1.iteratedDeriv_circleMollify`: the `m`-th derivative is the convolution of `f` with the
  periodized `m`-th derivative of the kernel.
* `Riesz1.iteratedDeriv_circleMollify_eq_deriv`: for `f` of class `C^m`, the `m`-th derivative of
  `f_h` is the convolution of `f^{(m)}` with the periodized kernel.

The convolutions are first treated on `ℝ` for a continuous kernel of compact support. The periodization
is then unfolded over one period.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology
open scoped ContDiff

namespace Riesz1

/-- A function vanishes outside its topological support. -/
lemma zero_of_notMem_tsupport {κ : ℝ → ℝ} {u : ℝ} (hu : u ∉ tsupport κ) : κ u = 0 := by
  by_contra hne
  exact hu (subset_tsupport κ (Function.mem_support.mpr hne))

/-- A function with compact support vanishes for `|u| ≥ R` when `R` is large enough. -/
lemma exists_radius_of_hasCompactSupport {κ : ℝ → ℝ} (hκc : HasCompactSupport κ) :
    ∃ R : ℝ, ∀ u : ℝ, R ≤ |u| → κ u = 0 := by
  obtain ⟨R, hR⟩ := hκc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R + 1, fun u hu => zero_of_notMem_tsupport (fun hmem => ?_)⟩
  have h1 := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
  linarith

/-- The `m`-th derivative of a function with compact support has compact support. -/
lemma hasCompactSupport_iteratedDeriv {κ : ℝ → ℝ} (hκc : HasCompactSupport κ) (m : ℕ) :
    HasCompactSupport (iteratedDeriv m κ) := by
  induction m with
  | zero => simpa using hκc
  | succ m ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- The `m`-th derivative of a smooth function is smooth. -/
lemma contDiff_iteratedDeriv_inf {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) (m : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv m κ) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv m hκ

/-- A periodic function has a periodic derivative. -/
lemma periodic_deriv {f : ℝ → ℝ} {L : ℝ} (hf : Function.Periodic f L) :
    Function.Periodic (deriv f) L := by
  intro x
  have hfun : (fun y => f (y + L)) = f := funext hf
  calc deriv f (x + L) = deriv (fun y => f (y + L)) x := (deriv_comp_add_const f L x).symm
    _ = deriv f x := by rw [hfun]

/-- The `m`-th derivative of a periodic function is periodic. -/
lemma periodic_iteratedDeriv {f : ℝ → ℝ} {L : ℝ} (hf : Function.Periodic f L) (m : ℕ) :
    Function.Periodic (iteratedDeriv m f) L := by
  induction m with
  | zero => simpa using hf
  | succ m ih => rw [iteratedDeriv_succ]; exact periodic_deriv ih

/-- **Derivative falling on the first factor.** For a `C¹` function `g` and a continuous kernel `κ`
of compact support, the convolution `x ↦ ∫ g(y) κ(x - y) dy` has derivative `∫ g'(y) κ(x - y) dy`.
The proof changes variables to `∫ g(x - u) κ(u) du` and differentiates under the integral. -/
lemma hasDerivAt_integral_mul_sub_of_contDiff {g κ : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hκ : Continuous κ) (hκc : HasCompactSupport κ) (x₀ : ℝ) :
    HasDerivAt (fun x => ∫ y, g y * κ (x - y)) (∫ y, deriv g y * κ (x₀ - y)) x₀ := by
  -- Change of variables `y ↦ x - y` in the integral.
  have hcv : ∀ (φ : ℝ → ℝ) (x : ℝ), ∫ y, φ y * κ (x - y) = ∫ u, φ (x - u) * κ u := by
    intro φ x
    rw [← integral_sub_left_eq_self (fun y => φ y * κ (x - y)) volume x]
    simp
  have hfun : (fun x => ∫ y, g y * κ (x - y)) = fun x => ∫ u, g (x - u) * κ u :=
    funext fun x => hcv g x
  rw [hfun, hcv (deriv g) x₀]
  obtain ⟨R, hR⟩ := hκc.isCompact.isBounded.subset_closedBall 0
  have hdcont : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hgc : Continuous g := hg.continuous
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ Metric.closedBall (0 : ℝ) (|x₀| + 1 + R), ‖deriv g z‖ ≤ M :=
    (isCompact_closedBall _ _).exists_bound_of_continuousOn hdcont.continuousOn
  -- The integrand of the derivative is bounded by `M |κ(u)|`, uniformly for `x` near `x₀`.
  have hkey : ∀ u : ℝ, ∀ x ∈ Metric.ball x₀ 1, ‖deriv g (x - u) * κ u‖ ≤ M * ‖κ u‖ := by
    intro u x hx
    rw [norm_mul]
    by_cases hu : u ∈ tsupport κ
    · have hu' := hR hu
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hu'
      rw [Metric.mem_ball, Real.dist_eq] at hx
      have hu2 := abs_le.mp hu'
      have hx2 := abs_lt.mp hx
      have hxu : x - u ∈ Metric.closedBall (0 : ℝ) (|x₀| + 1 + R) := by
        rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
        have h3 := neg_abs_le x₀
        have h4 := le_abs_self x₀
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      exact mul_le_mul_of_nonneg_right (hM _ hxu) (norm_nonneg _)
    · simp [zero_of_notMem_tsupport hu]
  have hint : Integrable (fun u => g (x₀ - u) * κ u) := by
    have hcs : HasCompactSupport (fun u => g (x₀ - u) * κ u) := hκc.mul_left
    exact Continuous.integrable_of_hasCompactSupport
      ((hgc.comp (continuous_const.sub continuous_id)).mul hκ) hcs
  have hbound : Integrable (fun u => M * ‖κ u‖) :=
    (Continuous.integrable_of_hasCompactSupport hκ.norm hκc.norm).const_mul M
  have hshift : ∀ (u x : ℝ), HasDerivAt (fun x => g (x - u)) (deriv g (x - u)) x := by
    intro u x
    have h1 := (hg.differentiable (by norm_num) (x - u)).hasDerivAt
    have h2 : HasDerivAt (fun x : ℝ => x - u) 1 x := (hasDerivAt_id x).sub_const u
    have h3 := h1.comp x h2
    rw [mul_one] at h3
    exact h3
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun x u => g (x - u) * κ u)
    (F' := fun x u => deriv g (x - u) * κ u) (bound := fun u => M * ‖κ u‖)
    (s := Metric.ball x₀ 1) (Metric.ball_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x =>
      ((hgc.comp (continuous_const.sub continuous_id)).mul hκ).aestronglyMeasurable)
    hint
    ((hdcont.comp (continuous_const.sub continuous_id)).mul hκ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u x hx => hkey u x hx)
    hbound
    (Filter.Eventually.of_forall fun u x _ => (hshift u x).mul_const (κ u))).2

/-- **Derivative falling on the kernel.** For a function `f` that is locally integrable and a kernel `κ` of
class `C¹` with compact support, the convolution `x ↦ ∫ f(y) κ(x - y) dy` has derivative `∫ f(y) κ'(x - y) dy`. -/
lemma hasDerivAt_integral_mul_sub_kernel {f κ : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (hκc : HasCompactSupport κ) (hκ : ContDiff ℝ 1 κ) (x₀ : ℝ) :
    HasDerivAt (fun x => ∫ y, f y * κ (x - y)) (∫ y, f y * deriv κ (x₀ - y)) x₀ := by
  have hfun : (fun x => ∫ y, f y * κ (x - y)) =
      convolution f κ (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext x
    simp [convolution_def]
  have hval : convolution f (deriv κ) (ContinuousLinearMap.mul ℝ ℝ) volume x₀ =
      ∫ y, f y * deriv κ (x₀ - y) := by
    simp [convolution_def]
  rw [hfun, ← hval]
  exact HasCompactSupport.hasDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hκc hκ x₀

/-- The `m`-th derivative of `x ↦ ∫ f(y) κ(x - y) dy` is the convolution with the `m`-th derivative
of the kernel. -/
lemma iteratedDeriv_integral_mul_sub_kernel {f κ : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (hκc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ) (m : ℕ) :
    iteratedDeriv m (fun x => ∫ y, f y * κ (x - y)) =
      fun x => ∫ y, f y * iteratedDeriv m κ (x - y) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext x₀
    have hκm : ContDiff ℝ 1 (iteratedDeriv m κ) :=
      (contDiff_iteratedDeriv_inf hκ m).of_le (by simp)
    rw [(hasDerivAt_integral_mul_sub_kernel hf (hasCompactSupport_iteratedDeriv hκc m) hκm x₀).deriv,
      iteratedDeriv_succ]

/-- The `m`-th derivative of `x ↦ ∫ g(y) κ(x - y) dy`, for `g` of class `C^m`, is the convolution of
`g^{(m)}` with `κ`. -/
lemma iteratedDeriv_integral_mul_sub_of_contDiff {κ : ℝ → ℝ} (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) (m : ℕ) :
    ∀ {g : ℝ → ℝ}, ContDiff ℝ m g →
      iteratedDeriv m (fun x => ∫ y, g y * κ (x - y)) =
        fun x => ∫ y, iteratedDeriv m g y * κ (x - y) := by
  induction m with
  | zero => intro g _; simp
  | succ m ih =>
    intro g hg
    have hg' : ContDiff ℝ m g := hg.of_le (by exact_mod_cast Nat.le_succ m)
    have hgm : ContDiff ℝ 1 (iteratedDeriv m g) := by
      rw [iteratedDeriv_eq_iterate]
      exact ContDiff.iterate_deriv' 1 m (by rw [Nat.add_comm]; exact hg)
    rw [iteratedDeriv_succ, ih hg']
    funext x₀
    rw [(hasDerivAt_integral_mul_sub_of_contDiff hgm hκ hκc x₀).deriv, iteratedDeriv_succ]

/-- **Unfolding the periodization.** Let `f` be locally integrable and `L`-periodic, with `L > 0`, and
let `κ` be a continuous kernel of compact support. Then the integral over one period against the
periodized kernel `∑_n κ(· + nL)` equals the integral over `ℝ` against `κ`. -/
lemma intervalIntegral_mul_tsum_eq_integral {f κ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hf : LocallyIntegrable f volume) (hper : Function.Periodic f L) (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) (x : ℝ) :
    ∫ y in (-(L / 2))..(L / 2), f y * ∑' n : ℤ, κ (x - y + n * L) = ∫ y, f y * κ (x - y) := by
  obtain ⟨r, hr⟩ := exists_radius_of_hasCompactSupport hκc
  set G : ℝ → ℝ := fun y => f y * κ (x - y) with hG
  have hGi : Integrable G := integrable_mul_sub_of_support hf hκ hr
  have hpt : ∀ y : ℝ, f y * ∑' n : ℤ, κ (x - y + n * L) = ∑' n : ℤ, G (y - n * L) := by
    intro y
    rw [← tsum_mul_left]
    congr 1
    funext n
    simp only [hG]
    rw [hper.sub_int_mul_eq n]
    congr 2
    ring
  have hnorm : Summable fun n : ℤ => ∫ t in Ioc (-(L / 2) - n * L) (L / 2 - n * L), ‖G t‖ := by
    have := hasSum_integral_iUnion (μ := volume) (f := fun t => ‖G t‖)
      (s := fun n : ℤ => Ioc (-(L / 2) - n * L) (L / 2 - n * L))
      (fun n => measurableSet_Ioc) (pairwise_disjoint_tiles hL)
      (by rw [iUnion_tiles_eq_univ hL]; exact hGi.norm.integrableOn)
    exact this.summable
  have hsumG : HasSum (fun n : ℤ => ∫ t in Ioc (-(L / 2) - n * L) (L / 2 - n * L), G t)
      (∫ t, G t) := by
    have := hasSum_integral_iUnion (μ := volume) (f := G)
      (s := fun n : ℤ => Ioc (-(L / 2) - n * L) (L / 2 - n * L))
      (fun n => measurableSet_Ioc) (pairwise_disjoint_tiles hL)
      (by rw [iUnion_tiles_eq_univ hL]; exact hGi.integrableOn)
    rwa [iUnion_tiles_eq_univ hL, setIntegral_univ] at this
  have hFi : ∀ n : ℤ, Integrable (fun y => G (y - n * L))
      (volume.restrict (Ioc (-(L / 2)) (L / 2))) :=
    fun n => (hGi.comp_sub_right (n * L)).integrableOn
  have hFs : Summable fun n : ℤ => ∫ y in Ioc (-(L / 2)) (L / 2), ‖G (y - n * L)‖ :=
    hnorm.congr fun n => (integral_Ioc_sub_tiles (fun t => ‖G t‖) hL n).symm
  calc ∫ y in (-(L / 2))..(L / 2), f y * ∑' n : ℤ, κ (x - y + n * L)
      = ∫ y in (-(L / 2))..(L / 2), ∑' n : ℤ, G (y - n * L) :=
        intervalIntegral.integral_congr fun y _ => hpt y
    _ = ∫ y in Ioc (-(L / 2)) (L / 2), ∑' n : ℤ, G (y - n * L) :=
        intervalIntegral.integral_of_le (by linarith)
    _ = ∑' n : ℤ, ∫ y in Ioc (-(L / 2)) (L / 2), G (y - n * L) :=
        (integral_tsum_of_summable_integral_norm hFi hFs).symm
    _ = ∑' n : ℤ, ∫ t in Ioc (-(L / 2) - n * L) (L / 2 - n * L), G t :=
        tsum_congr fun n => integral_Ioc_sub_tiles G hL n
    _ = ∫ t, G t := hsumG.tsum_eq
    _ = ∫ y, f y * κ (x - y) := rfl

/-- The circle regularization is the line convolution with the scaled mollifier. -/
lemma circleMollify_fun_eq {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {L h : ℝ} (hL : 0 < L) (hh : 0 < h)
    {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (hper : Function.Periodic f L) :
    circleMollify ρ L h f = fun x => ∫ y, f y * scaledMollifier ρ h (x - y) :=
  funext fun x => circleMollify_eq_mollifyLine hρ hL hh hf hper x

/-- **Smoothness.** For a mollifier `ρ`, a length `L > 0`, a scale `h > 0` and a locally integrable
`L`-periodic `f`, the regularization `f_h` is smooth. -/
theorem contDiff_circleMollify {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {L h : ℝ} (hL : 0 < L) (hh : 0 < h)
    {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (hper : Function.Periodic f L) :
    ContDiff ℝ ∞ (circleMollify ρ L h f) := by
  rw [circleMollify_fun_eq hρ hL hh hf hper]
  exact HasCompactSupport.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (hasCompactSupport_scaledMollifier hρ hh) hf (contDiff_scaledMollifier hρ (h := h))

/-- **Periodized derivatives of the kernel.** For a mollifier `ρ`, a length `L > 0`, a scale `h > 0`, a
locally integrable `L`-periodic `f` and `m : ℕ`, the `m`-th derivative of `f_h` is the integral over one
period of `f(y)` against the periodized `m`-th derivative `∑_n ρ_h^{(m)}(x - y + nL)` of the kernel. -/
theorem iteratedDeriv_circleMollify {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {L h : ℝ} (hL : 0 < L)
    (hh : 0 < h) {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (hper : Function.Periodic f L)
    (m : ℕ) (x : ℝ) :
    iteratedDeriv m (circleMollify ρ L h f) x =
      ∫ y in (-(L / 2))..(L / 2), f y *
        ∑' n : ℤ, iteratedDeriv m (scaledMollifier ρ h) (x - y + n * L) := by
  have hκc := hasCompactSupport_scaledMollifier hρ hh
  have hκ : ContDiff ℝ ∞ (scaledMollifier ρ h) := contDiff_scaledMollifier hρ
  rw [circleMollify_fun_eq hρ hL hh hf hper,
    iteratedDeriv_integral_mul_sub_kernel hf hκc hκ m]
  exact (intervalIntegral_mul_tsum_eq_integral hL hf hper
    (contDiff_iteratedDeriv_inf hκ m).continuous (hasCompactSupport_iteratedDeriv hκc m) x).symm

/-- **Derivative on the function.** For a mollifier `ρ`, a length `L > 0`, a scale `h > 0`, and an
`L`-periodic `f` of class `C^m`, the `m`-th derivative of `f_h` is the convolution of `f^{(m)}` with the
periodized kernel `ρ_{h,L}`. -/
theorem iteratedDeriv_circleMollify_eq_deriv {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {L h : ℝ}
    (hL : 0 < L) (hh : 0 < h) {f : ℝ → ℝ} (m : ℕ) (hf : ContDiff ℝ m f)
    (hper : Function.Periodic f L) (x : ℝ) :
    iteratedDeriv m (circleMollify ρ L h f) x =
      ∫ y in (-(L / 2))..(L / 2), iteratedDeriv m f y * periodMollifier ρ L h (x - y) := by
  have hκc := hasCompactSupport_scaledMollifier hρ hh
  have hκ : ContDiff ℝ ∞ (scaledMollifier ρ h) := contDiff_scaledMollifier hρ
  have hcont : Continuous (iteratedDeriv m f) := hf.continuous_iteratedDeriv m le_rfl
  have hlocint : LocallyIntegrable (iteratedDeriv m f) volume := hcont.locallyIntegrable
  rw [circleMollify_fun_eq hρ hL hh (hf.continuous.locallyIntegrable) hper,
    iteratedDeriv_integral_mul_sub_of_contDiff hκ.continuous hκc m hf]
  unfold periodMollifier
  exact (intervalIntegral_mul_tsum_eq_integral hL hlocint (periodic_iteratedDeriv hper m)
    hκ.continuous hκc x).symm

end Riesz1

end
