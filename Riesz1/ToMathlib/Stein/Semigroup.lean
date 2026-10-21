/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Riesz1.ToMathlib.Stein.Gaussian

/-!
# The Gaussian averaging semigroup: spatial regularity and bounds

For `σ > 0` and `t ≥ 0`, the Gaussian averaging
`P_t f (x) = E f (e^{-t} x + σ √(1 - e^{-2t}) Z)` with `Z ∼ N(0, 1)` is `gaussianAveraging σ t f x`.
For `f` continuously differentiable with `|f| ≤ 1` and `|f'| ≤ 1`, this file proves:

* for `t > 0`, the map `x ↦ P_t f (x)` is `C²`, with explicit first and second derivatives.
* for `t ≥ 0`, the bound `|P_t f (x) - E f (σ Z)| ≤ e^{-t} (|x| + σ √(2/π))`.
* the limit `P_t f (x) → f (x)` as `t ↓ 0` and the limit `P_t f (x) → E f (σ Z)` as `t → ∞`.

The time derivative and the generator identity are in `Riesz1.ToMathlib.Stein.SemigroupGenerator`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace Riesz1

/-- The Gaussian averaging `P_t f (x) = E f (e^{-t} x + σ √(1 - e^{-2t}) Z)` for `Z ∼ N(0, 1)`. -/
@[expose] noncomputable def gaussianAveraging (σ t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, f (rexp (-t) * x + σ * √(1 - rexp (-2 * t)) * z) ∂(gaussianReal 0 1)

/-- A bounded continuous function is integrable along an affine change of variables. -/
lemma semigroup_integrable_comp {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ} (hC : ∀ y, |g y| ≤ C)
    (y c : ℝ) : Integrable (fun z : ℝ => g (y + c * z)) (gaussianReal 0 1) :=
  (integrable_const C).mono'
    (hg.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hC _)

/-- Differentiation in the mean for a function with bounded derivative: the map `y ↦ E f (y + c Z)`
has derivative `E f' (y₀ + c Z)` at `y₀`. -/
lemma semigroup_hasDerivAt_mean {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hfb : ∀ y, |f y| ≤ 1)
    (hf' : ∀ y, |deriv f y| ≤ 1) (c y₀ : ℝ) :
    HasDerivAt (fun y => ∫ z, f (y + c * z) ∂(gaussianReal 0 1))
      (∫ z, deriv f (y₀ + c * z) ∂(gaussianReal 0 1)) y₀ := by
  have hfc : Continuous f := hf.continuous
  have hdfc : Continuous (deriv f) := hf.continuous_deriv_one
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hd : ∀ z y : ℝ, HasDerivAt (fun y => f (y + c * z)) (deriv f (y + c * z)) y := by
    intro z y
    have h1 : HasDerivAt (fun y : ℝ => y + c * z) 1 y := (hasDerivAt_id' y).add_const (c * z)
    exact ((hfd (y + c * z)).hasDerivAt.comp y h1).congr_deriv (mul_one _)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 1)
    (F := fun y z => f (y + c * z)) (F' := fun y z => deriv f (y + c * z))
    (bound := fun _ => 1) (s := univ) (x₀ := y₀) univ_mem
    (Eventually.of_forall fun y => (hfc.comp (continuous_const.add
      (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (semigroup_integrable_comp hfc hfb y₀ c)
    (hdfc.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
    (Eventually.of_forall fun z y _ => by rw [Real.norm_eq_abs]; exact hf' _)
    (integrable_const 1)
    (Eventually.of_forall fun z y _ => hd z y)).2

/-- The first spatial derivative of the Gaussian average of an affine map, for every `a` and `c`. -/
lemma semigroup_hasDerivAt_affine {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hfb : ∀ y, |f y| ≤ 1)
    (hf' : ∀ y, |deriv f y| ≤ 1) (a c x : ℝ) :
    HasDerivAt (fun x => ∫ z, f (a * x + c * z) ∂(gaussianReal 0 1))
      (a * ∫ z, deriv f (a * x + c * z) ∂(gaussianReal 0 1)) x := by
  have h := (semigroup_hasDerivAt_mean hf hfb hf' c (a * x)).comp x
    ((hasDerivAt_id' x).const_mul a)
  exact h.congr_deriv (by ring)

/-- The derivative of `x ↦ a E f' (a x + c Z)` for `c > 0`, obtained from the Gaussian derivative
in the mean. -/
lemma semigroup_hasDerivAt_affine_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hf' : ∀ y, |deriv f y| ≤ 1) {c : ℝ} (hc : 0 < c) (a x : ℝ) :
    HasDerivAt (fun x => a * ∫ z, deriv f (a * x + c * z) ∂(gaussianReal 0 1))
      (a * (a * ((1 / c) * ∫ z, z * deriv f (a * x + c * z) ∂(gaussianReal 0 1)))) x := by
  have hdfc : Continuous (deriv f) := hf.continuous_deriv_one
  have h := (stein_hasDerivAt_gaussian_mean hdfc hf' hc (a * x)).comp x
    ((hasDerivAt_id' x).const_mul a)
  exact (h.const_mul a).congr_deriv (by ring)

/-- The moment `x ↦ E [Z f' (a x + c Z)]` is continuous. -/
lemma semigroup_continuous_moment {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hf' : ∀ y, |deriv f y| ≤ 1)
    (a c : ℝ) :
    Continuous (fun x => ∫ z, z * deriv f (a * x + c * z) ∂(gaussianReal 0 1)) := by
  have hdfc : Continuous (deriv f) := hf.continuous_deriv_one
  refine continuous_of_dominated (F := fun x z => z * deriv f (a * x + c * z))
    (bound := fun z => |z|) (fun x => ?_) (fun x => Eventually.of_forall fun z => ?_)
    stein_integrable_abs_std (Eventually.of_forall fun z => ?_)
  · exact (continuous_id.mul (hdfc.comp
      (continuous_const.add (continuous_const.mul continuous_id)))).aestronglyMeasurable
  · simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg z) (hf' _)
  · exact continuous_const.mul (hdfc.comp ((continuous_const.mul continuous_id).add continuous_const))

/-- The first spatial derivative of the Gaussian averaging, for every `t`. -/
lemma gaussianAveraging_hasDerivAt_x {σ t : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfb : ∀ y, |f y| ≤ 1) (hf' : ∀ y, |deriv f y| ≤ 1) (x : ℝ) :
    HasDerivAt (gaussianAveraging σ t f)
      (rexp (-t) * ∫ z, deriv f (rexp (-t) * x + σ * √(1 - rexp (-2 * t)) * z)
        ∂(gaussianReal 0 1)) x :=
  semigroup_hasDerivAt_affine hf hfb hf' (rexp (-t)) (σ * √(1 - rexp (-2 * t))) x

/-- Spatial regularity of the Gaussian averaging for `t > 0`: the map `x ↦ P_t f (x)` is `C²`,
with first derivative `e^{-t} E f' (a + b Z)` and second derivative
`e^{-2t} / (σ √(1 - e^{-2t})) E [Z f' (a + b Z)]`, where `a = e^{-t} x` and
`b = σ √(1 - e^{-2t})`. -/
theorem gaussianAveraging_spatial {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hfb : ∀ y, |f y| ≤ 1) (hf' : ∀ y, |deriv f y| ≤ 1) :
    ContDiff ℝ 2 (gaussianAveraging σ t f) ∧
      (∀ x, deriv (gaussianAveraging σ t f) x = rexp (-t) * ∫ z,
        deriv f (rexp (-t) * x + σ * √(1 - rexp (-2 * t)) * z) ∂(gaussianReal 0 1)) ∧
      (∀ x, deriv (deriv (gaussianAveraging σ t f)) x = rexp (-2 * t) / (σ * √(1 - rexp (-2 * t)))
        * ∫ z, z * deriv f (rexp (-t) * x + σ * √(1 - rexp (-2 * t)) * z)
          ∂(gaussianReal 0 1)) := by
  have hexp2 : rexp (-2 * t) = rexp (-t) * rexp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hlt : rexp (-2 * t) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hc : 0 < σ * √(1 - rexp (-2 * t)) :=
    mul_pos hσ (Real.sqrt_pos.2 (by linarith))
  have hP1 : deriv (gaussianAveraging σ t f) = fun x => rexp (-t) * ∫ z,
      deriv f (rexp (-t) * x + σ * √(1 - rexp (-2 * t)) * z) ∂(gaussianReal 0 1) :=
    funext fun x => (gaussianAveraging_hasDerivAt_x hf hfb hf' x).deriv
  have hP2 : deriv (deriv (gaussianAveraging σ t f)) = fun x => rexp (-2 * t)
      / (σ * √(1 - rexp (-2 * t))) * ∫ z, z * deriv f (rexp (-t) * x + σ * √(1 - rexp (-2 * t)) * z)
        ∂(gaussianReal 0 1) := by
    rw [hP1]
    funext x
    rw [(semigroup_hasDerivAt_affine_deriv hf hf' hc (rexp (-t)) x).deriv, hexp2]
    ring
  have hdiff : Differentiable ℝ (gaussianAveraging σ t f) := fun x =>
    (gaussianAveraging_hasDerivAt_x hf hfb hf' x).differentiableAt
  have hdiffD : Differentiable ℝ (deriv (gaussianAveraging σ t f)) := by
    rw [hP1]
    intro x
    exact (semigroup_hasDerivAt_affine_deriv hf hf' hc (rexp (-t)) x).differentiableAt
  have hcontDD : Continuous (deriv (deriv (gaussianAveraging σ t f))) := by
    rw [hP2]
    exact (semigroup_continuous_moment hf hf' _ _).const_mul _
  refine ⟨?_, fun x => ?_, fun x => ?_⟩
  · show ContDiff ℝ (1 + 1) (gaussianAveraging σ t f)
    refine contDiff_succ_iff_deriv.2 ⟨hdiff, fun h => absurd h (by simp), ?_⟩
    exact contDiff_one_iff_deriv.2 ⟨hdiffD, hcontDD⟩
  · exact (gaussianAveraging_hasDerivAt_x hf hfb hf' x).deriv
  · exact congrFun hP2 x

/-- The Gaussian averaging with `t = 0` is the identity: `P_0 f = f`. -/
lemma gaussianAveraging_zero (σ : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    gaussianAveraging σ 0 f x = f x := by
  simp [gaussianAveraging]

/-- The inequality `1 - √(1 - e^{-2t}) ≤ e^{-t}` for `t ≥ 0`. -/
lemma semigroup_one_sub_sqrt_le {t : ℝ} (ht : 0 ≤ t) :
    1 - √(1 - rexp (-2 * t)) ≤ rexp (-t) := by
  have hq : rexp (-2 * t) = rexp (-t) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hq0 : 0 ≤ rexp (-t) := (Real.exp_pos _).le
  have hq1 : rexp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hle : (1 - rexp (-t)) ^ 2 ≤ 1 - rexp (-2 * t) := by
    rw [hq]
    nlinarith [mul_nonneg hq0 (sub_nonneg.2 hq1)]
  have hsq : 1 - rexp (-t) ≤ √(1 - rexp (-2 * t)) := by
    calc 1 - rexp (-t) = √((1 - rexp (-t)) ^ 2) := (Real.sqrt_sq (by linarith)).symm
      _ ≤ √(1 - rexp (-2 * t)) := Real.sqrt_le_sqrt hle
  linarith

/-- The map `f` is `1`-Lipschitz when `|f'| ≤ 1`. -/
lemma semigroup_lipschitz {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hf' : ∀ y, |deriv f y| ≤ 1)
    (u v : ℝ) : |f u - f v| ≤ |u - v| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (f := f) (C := 1)
    (fun y _ => hf.differentiable one_ne_zero y)
    (fun y _ => by rw [Real.norm_eq_abs]; exact hf' y) convex_univ (mem_univ v) (mem_univ u)
  simpa [Real.norm_eq_abs] using h

/-- The bound `|P_t f (x) - E f (σ Z)| ≤ e^{-t} (|x| + σ √(2/π))` for `t ≥ 0`. -/
theorem gaussianAveraging_sub_le {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hfb : ∀ y, |f y| ≤ 1) (hf' : ∀ y, |deriv f y| ≤ 1) (x : ℝ) :
    |gaussianAveraging σ t f x - ∫ y, f y ∂(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩)|
      ≤ rexp (-t) * (|x| + σ * √(2 / π)) := by
  have hfc : Continuous f := hf.continuous
  rw [stein_integral_gaussian_scale σ hfc]
  unfold gaussianAveraging
  set A := rexp (-t) * x with hA
  set B := σ * √(1 - rexp (-2 * t)) with hB
  have hint1 : Integrable (fun z : ℝ => f (A + B * z)) (gaussianReal 0 1) :=
    semigroup_integrable_comp hfc hfb A B
  have hint2 : Integrable (fun z : ℝ => f (σ * z)) (gaussianReal 0 1) := by
    simpa using semigroup_integrable_comp hfc hfb 0 σ
  rw [← integral_sub hint1 hint2]
  have hbound : ∀ z : ℝ, ‖f (A + B * z) - f (σ * z)‖ ≤ |A| + |B - σ| * |z| := by
    intro z
    rw [Real.norm_eq_abs]
    calc |f (A + B * z) - f (σ * z)| ≤ |A + B * z - σ * z| :=
          semigroup_lipschitz hf hf' _ _
      _ = |A + (B - σ) * z| := by congr 1; ring
      _ ≤ |A| + |(B - σ) * z| := abs_add_le _ _
      _ = |A| + |B - σ| * |z| := by rw [abs_mul (B - σ) z]
  have hint3 : Integrable (fun z : ℝ => |A| + |B - σ| * |z|) (gaussianReal 0 1) :=
    (integrable_const _).add (stein_integrable_abs_std.const_mul _)
  have key := norm_integral_le_of_norm_le hint3 (Eventually.of_forall hbound)
  rw [integral_add (integrable_const _) (stein_integrable_abs_std.const_mul _),
    integral_const, integral_const_mul, stein_integral_abs_std] at key
  simp only [probReal_univ, one_smul] at key
  have hA_abs : |A| = rexp (-t) * |x| := by
    rw [hA, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hB_le : B ≤ σ := by
    have h1 : √(1 - rexp (-2 * t)) ≤ 1 := Real.sqrt_le_one.2 (by linarith [Real.exp_pos (-2 * t)])
    calc B = σ * √(1 - rexp (-2 * t)) := hB
      _ ≤ σ * 1 := mul_le_mul_of_nonneg_left h1 hσ.le
      _ = σ := mul_one σ
  have hBσ : |B - σ| = σ - B := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  have hσB : σ - B ≤ σ * rexp (-t) := by
    calc σ - B = σ * (1 - √(1 - rexp (-2 * t))) := by rw [hB]; ring
      _ ≤ σ * rexp (-t) := mul_le_mul_of_nonneg_left (semigroup_one_sub_sqrt_le ht) hσ.le
  have hsqrt : 0 ≤ √(2 / π) := Real.sqrt_nonneg _
  have hmul : |B - σ| * √(2 / π) ≤ σ * rexp (-t) * √(2 / π) := by
    rw [hBσ]
    exact mul_le_mul_of_nonneg_right hσB hsqrt
  calc |∫ z, (f (A + B * z) - f (σ * z)) ∂(gaussianReal 0 1)|
      = ‖∫ z, (f (A + B * z) - f (σ * z)) ∂(gaussianReal 0 1)‖ := (Real.norm_eq_abs _).symm
    _ ≤ |A| + |B - σ| * √(2 / π) := key
    _ = rexp (-t) * |x| + |B - σ| * √(2 / π) := by rw [hA_abs]
    _ ≤ rexp (-t) * |x| + σ * rexp (-t) * √(2 / π) := by linarith
    _ = rexp (-t) * (|x| + σ * √(2 / π)) := by ring

/-- As `t ↓ 0`, the Gaussian averaging converges to `f x`, for continuous `f` with `|f| ≤ 1`. -/
theorem gaussianAveraging_tendsto_zero {σ : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hfb : ∀ y, |f y| ≤ 1) (x : ℝ) :
    Tendsto (fun t => gaussianAveraging σ t f x) (𝓝[>] 0) (𝓝 (f x)) := by
  have hcont : Continuous (fun t => gaussianAveraging σ t f x) := by
    unfold gaussianAveraging
    refine continuous_of_dominated (F := fun t z =>
      f (rexp (-t) * x + σ * √(1 - rexp (-2 * t)) * z)) (bound := fun _ => 1)
      (fun t => ?_) (fun t => Eventually.of_forall fun z => ?_) (integrable_const 1)
      (Eventually.of_forall fun z => ?_)
    · exact (hf.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact hfb _
    · fun_prop
  have h : Tendsto (fun t => gaussianAveraging σ t f x) (𝓝[>] (0 : ℝ))
      (𝓝 (gaussianAveraging σ 0 f x)) := (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  rwa [gaussianAveraging_zero σ f x] at h

/-- As `t → ∞`, the Gaussian averaging converges to `E f (σ Z)`, the value at the Gaussian law of
variance `σ²`. -/
theorem gaussianAveraging_tendsto_atTop {σ : ℝ} (hσ : 0 < σ) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfb : ∀ y, |f y| ≤ 1) (hf' : ∀ y, |deriv f y| ≤ 1) (x : ℝ) :
    Tendsto (fun t => gaussianAveraging σ t f x) atTop
      (𝓝 (∫ y, f y ∂(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun t => rexp (-t) * (|x| + σ * √(2 / π))) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.mul_const (|x| + σ * √(2 / π))
    rwa [zero_mul] at h
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [Real.norm_eq_abs]
  exact gaussianAveraging_sub_le hσ ht hf hfb hf' x

end Riesz1
