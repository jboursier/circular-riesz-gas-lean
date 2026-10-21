/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Mollifiers and pointwise window estimates

The mollifier `ρ` is smooth, even, nonnegative, supported in
`(-1/2, 1/2)` and has total mass one. Its scaled version is `ρ_h(y) = h⁻¹ ρ(y / h)`.

This file collects the facts about the scaled mollifier that the pointwise estimates of
Lemma 5.1 use:
* support, bounds, integral one, and integral zero of the derivative.
* the convolution `mollifyLine ρ h f = f ⋆ ρ_h` on `ℝ`, and its derivative.
* the local bound `|∫ f(y) φ(x - y) dy| ≤ K ∫_{x - r}^{x + r} |f|` for a kernel `φ` supported in
  `[-r, r]` and bounded by `K`.
* the integrals of `|y| ^ (-γ)` over symmetric intervals.

Main results:
* `Riesz1.hasDerivAt_mollifyLine`: the derivative of `f ⋆ ρ_h` is `f ⋆ ρ_h'`.
* `Riesz1.norm_integral_mul_le_window`: the window estimate.
* `Riesz1.integral_abs_rpow_symm`: `∫_{-a}^{a} |y| ^ (-γ) dy = 2 a ^ (1 - γ) / (1 - γ)`.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The standing hypotheses on the mollifier `ρ`: `ρ` is smooth, even
and nonnegative, its support lies in the open interval `(-1/2, 1/2)`, and its total mass is one. -/
@[expose]
def IsMollifier (ρ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ ρ ∧ (∀ x, 0 ≤ ρ x) ∧ (∀ x, ρ (-x) = ρ x) ∧
    tsupport ρ ⊆ Ioo (-(1 / 2)) (1 / 2) ∧ ∫ x, ρ x = 1

/-- The scaled mollifier `ρ_h(y) = h⁻¹ ρ(y / h)`. -/
@[expose]
noncomputable def scaledMollifier (ρ : ℝ → ℝ) (h y : ℝ) : ℝ :=
  h⁻¹ * ρ (y / h)

/-- The convolution `(f ⋆ ρ_h)(x) = ∫ f(y) ρ_h(x - y) dy` on the line. -/
@[expose]
noncomputable def mollifyLine (ρ : ℝ → ℝ) (h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, f y * scaledMollifier ρ h (x - y)

namespace IsMollifier

variable {ρ : ℝ → ℝ}

lemma contDiff (hρ : IsMollifier ρ) : ContDiff ℝ ∞ ρ := hρ.1

lemma nonneg (hρ : IsMollifier ρ) (x : ℝ) : 0 ≤ ρ x := hρ.2.1 x

lemma tsupport_subset (hρ : IsMollifier ρ) : tsupport ρ ⊆ Ioo (-(1 / 2)) (1 / 2) := hρ.2.2.2.1

lemma integral_eq_one (hρ : IsMollifier ρ) : ∫ x, ρ x = 1 := hρ.2.2.2.2

lemma hasCompactSupport (hρ : IsMollifier ρ) : HasCompactSupport ρ :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport ρ)
    (hρ.tsupport_subset.trans Ioo_subset_Icc_self)

lemma abs_lt_of_mem_tsupport (hρ : IsMollifier ρ) {x : ℝ} (hx : x ∈ tsupport ρ) :
    |x| < 1 / 2 := by
  have hI := hρ.tsupport_subset hx
  rw [mem_Ioo] at hI
  rw [abs_lt]
  constructor <;> linarith [hI.1, hI.2]

lemma eq_zero_of_half_le (hρ : IsMollifier ρ) {x : ℝ} (hx : 1 / 2 ≤ |x|) : ρ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun hmem => by
    have := hρ.abs_lt_of_mem_tsupport hmem
    linarith

lemma deriv_eq_zero_of_half_le (hρ : IsMollifier ρ) {x : ℝ} (hx : 1 / 2 ≤ |x|) :
    deriv ρ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun hmem => by
    have := hρ.abs_lt_of_mem_tsupport (tsupport_deriv_subset hmem)
    linarith

lemma exists_bound (hρ : IsMollifier ρ) : ∃ M, 0 ≤ M ∧ ∀ x, |ρ x| ≤ M := by
  obtain ⟨M, hM⟩ :=
    Continuous.bounded_above_of_compact_support hρ.contDiff.continuous hρ.hasCompactSupport
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  rw [← Real.norm_eq_abs]
  exact (hM x).trans (le_max_left _ _)

lemma exists_bound_deriv (hρ : IsMollifier ρ) : ∃ M, 0 ≤ M ∧ ∀ x, |deriv ρ x| ≤ M := by
  obtain ⟨M, hM⟩ := Continuous.bounded_above_of_compact_support
    (hρ.contDiff.continuous_deriv (by simp)) hρ.hasCompactSupport.deriv
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  rw [← Real.norm_eq_abs]
  exact (hM x).trans (le_max_left _ _)

end IsMollifier

section Scaled

variable {ρ : ℝ → ℝ} {h : ℝ}

lemma scaledMollifier_nonneg (hρ : IsMollifier ρ) (hh : 0 < h) (y : ℝ) :
    0 ≤ scaledMollifier ρ h y :=
  mul_nonneg (inv_nonneg.2 hh.le) (hρ.nonneg _)

lemma scaledMollifier_eq_zero (hρ : IsMollifier ρ) (hh : 0 < h) {y : ℝ} (hy : h / 2 ≤ |y|) :
    scaledMollifier ρ h y = 0 := by
  have h0 : ρ (y / h) = 0 := by
    apply hρ.eq_zero_of_half_le
    rw [abs_div, abs_of_pos hh, le_div_iff₀ hh]
    linarith
  simp [scaledMollifier, h0]

lemma abs_scaledMollifier_le (hh : 0 < h) {M : ℝ}
    (hM : ∀ x, |ρ x| ≤ M) (y : ℝ) : |scaledMollifier ρ h y| ≤ M * h⁻¹ := by
  unfold scaledMollifier
  rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hh.le), mul_comm M]
  exact mul_le_mul_of_nonneg_left (hM _) (inv_nonneg.2 hh.le)

lemma contDiff_scaledMollifier (hρ : IsMollifier ρ) :
    ContDiff ℝ ∞ (scaledMollifier ρ h) := by
  unfold scaledMollifier
  exact contDiff_const.mul (hρ.contDiff.comp (contDiff_id.div_const h))

lemma hasDerivAt_scaledMollifier (hρ : IsMollifier ρ) (y : ℝ) :
    HasDerivAt (scaledMollifier ρ h) (h⁻¹ * (h⁻¹ * deriv ρ (y / h))) y := by
  have hρd : HasDerivAt ρ (deriv ρ (y / h)) (y / h) :=
    ((hρ.contDiff.differentiable (by simp)) _).hasDerivAt
  have hlin : HasDerivAt (fun z : ℝ => z / h) h⁻¹ y := by
    simpa [div_eq_inv_mul] using (hasDerivAt_id y).const_mul h⁻¹
  have hcomp := (hρd.comp y hlin).const_mul h⁻¹
  have hval : h⁻¹ * (h⁻¹ * deriv ρ (y / h)) = h⁻¹ * (deriv ρ (y / h) * h⁻¹) := by ring
  rw [hval]
  exact hcomp

lemma deriv_scaledMollifier (hρ : IsMollifier ρ) (y : ℝ) :
    deriv (scaledMollifier ρ h) y = h⁻¹ * (h⁻¹ * deriv ρ (y / h)) :=
  (hasDerivAt_scaledMollifier hρ y).deriv

lemma abs_deriv_scaledMollifier_le (hρ : IsMollifier ρ) (hh : 0 < h) {M : ℝ}
    (hM : ∀ x, |deriv ρ x| ≤ M) (y : ℝ) :
    |deriv (scaledMollifier ρ h) y| ≤ M * (h⁻¹ * h⁻¹) := by
  rw [deriv_scaledMollifier hρ]
  have hi : 0 ≤ h⁻¹ * h⁻¹ := by positivity
  calc |h⁻¹ * (h⁻¹ * deriv ρ (y / h))| = (h⁻¹ * h⁻¹) * |deriv ρ (y / h)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.2 hh.le)]
        ring
    _ ≤ (h⁻¹ * h⁻¹) * M := mul_le_mul_of_nonneg_left (hM _) hi
    _ = M * (h⁻¹ * h⁻¹) := mul_comm _ _

lemma deriv_scaledMollifier_eq_zero (hρ : IsMollifier ρ) (hh : 0 < h) {y : ℝ}
    (hy : h / 2 ≤ |y|) : deriv (scaledMollifier ρ h) y = 0 := by
  rw [deriv_scaledMollifier hρ]
  have : deriv ρ (y / h) = 0 := by
    apply hρ.deriv_eq_zero_of_half_le
    rw [abs_div, abs_of_pos hh, le_div_iff₀ hh]
    linarith
  simp [this]

lemma hasCompactSupport_scaledMollifier (hρ : IsMollifier ρ) (hh : 0 < h) :
    HasCompactSupport (scaledMollifier ρ h) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(h / 2)) (b := h / 2)) fun y hy => ?_
  apply scaledMollifier_eq_zero hρ hh
  rw [mem_Icc, not_and_or, not_le, not_le] at hy
  rcases hy with hy | hy <;> rw [le_abs]
  · exact Or.inr (by linarith)
  · exact Or.inl (by linarith)

lemma integral_scaledMollifier (hρ : IsMollifier ρ) (hh : 0 < h) :
    ∫ y, scaledMollifier ρ h y = 1 := by
  unfold scaledMollifier
  rw [MeasureTheory.integral_const_mul, Measure.integral_comp_div ρ h, hρ.integral_eq_one,
    abs_of_pos hh, smul_eq_mul, mul_one]
  field_simp

lemma integral_deriv_scaledMollifier (hρ : IsMollifier ρ) (hh : 0 < h) :
    ∫ y, deriv (scaledMollifier ρ h) y = 0 := by
  have hC := contDiff_scaledMollifier (h := h) hρ
  have hcs := hasCompactSupport_scaledMollifier hρ hh
  refine integral_eq_zero_of_hasDerivAt_of_integrable (f := scaledMollifier ρ h)
    (f' := deriv (scaledMollifier ρ h)) (fun y => ?_) ?_ ?_
  · exact (hC.differentiable (by simp) y).hasDerivAt
  · exact (hC.continuous_deriv (by simp)).integrable_of_hasCompactSupport hcs.deriv
  · exact (hC.continuous).integrable_of_hasCompactSupport hcs

end Scaled

/-- For a locally integrable `g` and a continuous kernel `φ` vanishing for `|u| ≥ r`, the
integrand `g(y) φ(x - y)` is integrable. -/
lemma integrable_mul_sub_of_support {g φ : ℝ → ℝ} {x r : ℝ} (hg : LocallyIntegrable g volume)
    (hφc : Continuous φ) (hφ0 : ∀ u, r ≤ |u| → φ u = 0) :
    Integrable fun y => g y * φ (x - y) := by
  have hcont : Continuous fun y => φ (x - y) := hφc.comp (continuous_const.sub continuous_id)
  have hsupp : Function.support (fun y => g y * φ (x - y)) ⊆ Icc (x - r) (x + r) := by
    intro y hy
    have hφne : φ (x - y) ≠ 0 := fun h0 => hy (by simp [h0])
    have hlt : |x - y| < r := by
      by_contra hc
      exact hφne (hφ0 _ (not_lt.1 hc))
    rw [abs_lt] at hlt
    exact ⟨by linarith [hlt.2], by linarith [hlt.1]⟩
  have hloc : LocallyIntegrable fun y => φ (x - y) * g y := hg.continuous_mul hcont
  have hI' : IntegrableOn (fun y => g y * φ (x - y)) (Icc (x - r) (x + r)) :=
    (hloc.integrableOn_isCompact isCompact_Icc).congr_fun (fun y _ => mul_comm _ _)
      measurableSet_Icc
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hI'

section Convolution

variable {ρ : ℝ → ℝ} {h : ℝ}

lemma mollifyLine_eq (f : ℝ → ℝ) (x : ℝ) :
    mollifyLine ρ h f x = ∫ u, f (x - u) * scaledMollifier ρ h u := by
  unfold mollifyLine
  refine (integral_sub_left_eq_self (fun y => f y * scaledMollifier ρ h (x - y)) volume x
    ).symm.trans ?_
  simp only [sub_sub_cancel]

lemma integrable_mul_scaled_sub (hρ : IsMollifier ρ) (hh : 0 < h) {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (x : ℝ) :
    Integrable fun y => f y * scaledMollifier ρ h (x - y) :=
  integrable_mul_sub_of_support hf (contDiff_scaledMollifier hρ).continuous
    (fun _ hu => scaledMollifier_eq_zero hρ hh hu)

/-- The derivative of `f ⋆ ρ_h` is `f ⋆ ρ_h'`, for every locally integrable `f`. -/
lemma hasDerivAt_mollifyLine (hρ : IsMollifier ρ) (hh : 0 < h) {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (x : ℝ) :
    HasDerivAt (mollifyLine ρ h f) (∫ y, f y * deriv (scaledMollifier ρ h) (x - y)) x := by
  have hC1 : ContDiff ℝ 1 (scaledMollifier ρ h) :=
    (contDiff_scaledMollifier hρ).of_le (by simp)
  have hconv := HasCompactSupport.hasDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf
    (hasCompactSupport_scaledMollifier hρ hh) hC1 x
  have hfun : mollifyLine ρ h f = convolution f (scaledMollifier ρ h)
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext y
    simp [mollifyLine, convolution_def]
  rw [hfun]
  convert hconv using 1
  simp [convolution_def]

/-- Window estimate: if `φ` is bounded by `K` and vanishes for `|u| ≥ r`, then
`|∫ g(y) φ(x - y) dy| ≤ K ∫_{x - r}^{x + r} |g|`. -/
lemma norm_integral_mul_le_window {g φ : ℝ → ℝ} {x r K : ℝ}
    (hg : LocallyIntegrable g volume) (hφc : Continuous φ) (hφK : ∀ u, |φ u| ≤ K)
    (hφ0 : ∀ u, r ≤ |u| → φ u = 0) :
    |∫ y, g y * φ (x - y)| ≤ K * ∫ y in Ioo (x - r) (x + r), |g y| := by
  have hcont : Continuous fun y => φ (x - y) := hφc.comp (continuous_const.sub continuous_id)
  have hsupp : Function.support (fun y => g y * φ (x - y)) ⊆ Icc (x - r) (x + r) := by
    intro y hy
    have hφne : φ (x - y) ≠ 0 := fun h0 => hy (by simp [h0])
    have hlt : |x - y| < r := by
      by_contra hc
      exact hφne (hφ0 _ (not_lt.1 hc))
    rw [abs_lt] at hlt
    exact ⟨by linarith [hlt.2], by linarith [hlt.1]⟩
  have hloc : LocallyIntegrable fun y => φ (x - y) * g y := hg.continuous_mul hcont
  have hI : Integrable fun y => g y * φ (x - y) := by
    have hI' : IntegrableOn (fun y => g y * φ (x - y)) (Icc (x - r) (x + r)) :=
      ((hloc.integrableOn_isCompact isCompact_Icc).congr_fun
        (fun y _ => mul_comm _ _) measurableSet_Icc)
    exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hI'
  have hgW : IntegrableOn (fun y => |g y|) (Ioo (x - r) (x + r)) :=
    ((hg.integrableOn_isCompact isCompact_Icc).mono_set Ioo_subset_Icc_self).abs
  calc |∫ y, g y * φ (x - y)|
      ≤ ∫ y, |g y * φ (x - y)| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => g y * φ (x - y))
    _ = ∫ y in Ioo (x - r) (x + r), |g y * φ (x - y)| := by
        symm
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
        have hlt : r ≤ |x - y| := by
          by_contra hc
          apply hy
          rw [mem_Ioo]
          rw [not_le] at hc
          rw [abs_lt] at hc
          constructor <;> linarith [hc.1, hc.2]
        simp [hφ0 _ hlt]
    _ ≤ ∫ y in Ioo (x - r) (x + r), K * |g y| := by
        refine setIntegral_mono_on (hI.abs.integrableOn) (hgW.const_mul K) measurableSet_Ioo
          fun y _ => ?_
        rw [abs_mul, mul_comm K]
        exact mul_le_mul_of_nonneg_left (hφK _) (abs_nonneg _)
    _ = K * ∫ y in Ioo (x - r) (x + r), |g y| := MeasureTheory.integral_const_mul K _

end Convolution


section AbsRpow

/-- The function `|y| ^ r` is integrable on every symmetric compact interval when `-1 < r`. -/
lemma integrableOn_abs_rpow {r : ℝ} (hr : -1 < r) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun y : ℝ => |y| ^ r) (Icc (-a) a) := by
  have hpos : IntegrableOn (fun y : ℝ => y ^ r) (Icc 0 a) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ha).1
      (intervalIntegral.intervalIntegrable_rpow' hr)
  have h1 : IntegrableOn (fun y : ℝ => |y| ^ r) (Icc 0 a) :=
    hpos.congr_fun (fun y hy => by rw [abs_of_nonneg hy.1]) measurableSet_Icc
  have h3 : IntegrableOn (fun x : ℝ => |-x| ^ r) (-Icc 0 a) := h1.comp_neg
  rw [neg_Icc, neg_zero] at h3
  have h2 : IntegrableOn (fun y : ℝ => |y| ^ r) (Icc (-a) 0) := by
    simpa only [abs_neg] using h3
  rw [← Icc_union_Icc_eq_Icc (by linarith : -a ≤ 0) ha]
  exact h2.union h1

/-- The symmetric integral `∫_{-a}^{a} |y| ^ (-γ) dy = 2 a ^ (1 - γ) / (1 - γ)`. -/
lemma integral_abs_rpow_symm {γ : ℝ} (hγ1 : γ < 1) {a : ℝ} (ha : 0 ≤ a) :
    ∫ y in Icc (-a) a, |y| ^ (-γ) = 2 * a ^ (1 - γ) / (1 - γ) := by
  have hr : -1 < -γ := by linarith
  have hII : IntervalIntegrable (fun y : ℝ => |y| ^ (-γ)) volume (-a) a :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 (integrableOn_abs_rpow hr ha)
  have hsub : uIcc (-a) 0 ⊆ uIcc (-a) a := by
    rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
    exact Icc_subset_Icc le_rfl (by linarith)
  have hsub' : uIcc 0 a ⊆ uIcc (-a) a := by
    rw [uIcc_of_le ha, uIcc_of_le (by linarith)]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hL : ∫ y in (-a)..0, |y| ^ (-γ) = ∫ x in (0:ℝ)..a, |x| ^ (-γ) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := a) (fun y : ℝ => |y| ^ (-γ))
    simpa [abs_neg] using this.symm
  have hcongr : ∫ x in (0:ℝ)..a, |x| ^ (-γ) = ∫ x in (0:ℝ)..a, x ^ (-γ) :=
    intervalIntegral.integral_congr fun x hx => by
      rw [uIcc_of_le ha] at hx
      rw [abs_of_nonneg hx.1]
  have hR : ∫ x in (0:ℝ)..a, x ^ (-γ) = a ^ (1 - γ) / (1 - γ) := by
    rw [integral_rpow (Or.inl hr)]
    have e : -γ + 1 = 1 - γ := by ring
    rw [e, Real.zero_rpow (by linarith : (0:ℝ) < 1 - γ).ne', sub_zero]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -a ≤ a),
    ← intervalIntegral.integral_add_adjacent_intervals (hII.mono_set hsub)
      (hII.mono_set hsub')]
  rw [hL, hcongr, hR]
  ring

/-- `h⁻¹ h^(1 - γ) = h^(-γ)` for `h > 0`. -/
lemma inv_mul_rpow_one_sub {h γ : ℝ} (hh : 0 < h) : h⁻¹ * h ^ (1 - γ) = h ^ (-γ) := by
  have e : 1 - γ = -γ + 1 := by ring
  rw [e, Real.rpow_add_one hh.ne', mul_comm (h ^ (-γ)) h, ← mul_assoc, inv_mul_cancel₀ hh.ne',
    one_mul]

/-- `h⁻¹ h⁻¹ h^(1 - γ) = h^(-1 - γ)` for `h > 0`. -/
lemma inv_mul_inv_mul_rpow_one_sub {h γ : ℝ} (hh : 0 < h) :
    h⁻¹ * h⁻¹ * h ^ (1 - γ) = h ^ (-1 - γ) := by
  have e : -1 - γ = -1 + -γ := by ring
  rw [e, Real.rpow_add hh, Real.rpow_neg_one, ← inv_mul_rpow_one_sub hh, mul_assoc]

/-- `(t / 2) ^ (-p) = t ^ (-p) * 2 ^ p` for `t ≥ 0`. -/
lemma div_two_rpow_neg {t p : ℝ} (ht : 0 ≤ t) : (t / 2) ^ (-p) = t ^ (-p) * 2 ^ p := by
  rw [Real.div_rpow ht zero_le_two, Real.rpow_neg zero_le_two, div_inv_eq_mul]

end AbsRpow

end Riesz1
