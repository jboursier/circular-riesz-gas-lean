/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.Line
public import Riesz1.ToMathlib.CircDist
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Pointwise regularization on the circle

Circle version of Lemma 5.1. The circle of length `L ≥ 1`
is represented by `L`-periodic functions on `ℝ`: a function on `ℝ / L ℤ` is a periodic function
`f : ℝ → ℝ` with period `L`, and integrals over the circle are integrals over `(-L/2, L/2]`.
The distance to `0` on the circle is `circDist L y = |y - L · round(y/L)|`, the absolute value of
the representative of `y` in `[-L/2, L/2]`.

The periodized mollifier is `ρ_{h,L}(z) = ∑_{n ∈ ℤ} ρ_h(z + nL)` and the circle convolution is
`f ⋆ ρ_{h,L}(x) = ∫_{-L/2}^{L/2} f(y) ρ_{h,L}(x - y) dy`.

Main results:
* `Riesz1.circleMollify_eq_mollifyLine`: the circle convolution is the line convolution with the
  periodic function `f`, so the line estimates apply to the unfolded integrand.
* `Riesz1.circDist_le_add_abs`, `Riesz1.circDist_eq_abs`: the basic geometry of the distance.
* `Riesz1.circleMollify_sup_bound`: the sup estimate for `0 ≤ γ < 1`.
* `Riesz1.circleMollify_deriv_bound_pos`: the derivative estimate for `0 < γ < 1`.
* `Riesz1.circleMollify_deriv_bound_log`: the derivative estimate at `γ = 0`, with `1 + log(L/h)`.
* `Riesz1.circleMollify_deriv_bound_log_tail`: the same with `1 + |log h|` under the tail bound.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The periodized mollifier `ρ_{h,L}(z) = ∑_{n ∈ ℤ} ρ_h(z + nL)`. -/
@[expose] noncomputable def periodMollifier (ρ : ℝ → ℝ) (L h z : ℝ) : ℝ :=
  ∑' n : ℤ, scaledMollifier ρ h (z + n * L)

/-- The convolution on the circle `ℝ / Lℤ`: `f ⋆ ρ_{h,L}(x) = ∫_{-L/2}^{L/2} f(y) ρ_{h,L}(x - y)`.
The integral is over a fundamental domain, so it does not depend on the choice of the interval
for a periodic integrand. -/
@[expose] noncomputable def circleMollify (ρ : ℝ → ℝ) (L h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in (-(L / 2))..(L / 2), f y * periodMollifier ρ L h (x - y)


/-- Translating a tile: the integral over the fundamental domain of `g(y - nL)` is the integral
over the `n`-th tile. -/
lemma integral_Ioc_sub_tiles {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : ℝ}
    (g : ℝ → E) (hL : 0 < L) (n : ℤ) :
    ∫ y in Ioc (-(L / 2)) (L / 2), g (y - n * L) =
      ∫ t in Ioc (-(L / 2) - n * L) (L / 2 - n * L), g t := by
  have hle0 : -(L / 2) ≤ L / 2 := by linarith
  have hle : -(L / 2) - n * L ≤ L / 2 - n * L := by linarith
  rw [← intervalIntegral.integral_of_le hle0, ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_comp_sub_right g (n * L)]

section Unfolding

variable {ρ : ℝ → ℝ}

/-- The tiles `Ioc (-L/2 - nL) (L/2 - nL)`, `n ∈ ℤ`, cover the line. -/
lemma iUnion_tiles_eq_univ {L : ℝ} (hL : 0 < L) :
    ⋃ n : ℤ, Ioc (-(L / 2) - n * L) (L / 2 - n * L) = univ := by
  refine eq_univ_of_forall fun t => ?_
  have hmem := toIocMod_mem_Ioc hL (-(L / 2)) t
  rw [mem_iUnion]
  refine ⟨-toIocDiv hL (-(L / 2)) t, ?_⟩
  have e : toIocMod hL (-(L / 2)) t = t - toIocDiv hL (-(L / 2)) t • L := rfl
  rw [e, zsmul_eq_mul] at hmem
  have h2 : -(L / 2) + L = L / 2 := by ring
  rw [h2, mem_Ioc] at hmem
  rw [mem_Ioc]
  push_cast
  constructor <;> linarith [hmem.1, hmem.2]

/-- Distinct tiles `Ioc (-L/2 - nL) (L/2 - nL)` are disjoint. -/
lemma pairwise_disjoint_tiles {L : ℝ} (hL : 0 < L) :
    Pairwise fun n m : ℤ => Disjoint (Ioc (-(L / 2) - n * L) (L / 2 - n * L))
      (Ioc (-(L / 2) - m * L) (L / 2 - m * L)) := by
  intro n m hnm
  refine Set.disjoint_left.2 fun t htn htm => hnm ?_
  rw [mem_Ioc] at htn htm
  have h1 : ((n : ℝ) - m) * L < L := by nlinarith [htn.1, htn.2, htm.1, htm.2]
  have h2 : -L < ((n : ℝ) - m) * L := by nlinarith [htn.1, htn.2, htm.1, htm.2]
  have h3 : (n : ℝ) - m < 1 := by
    by_contra hc
    have hc' := not_lt.1 hc
    nlinarith
  have h4 : -1 < (n : ℝ) - m := by
    by_contra hc
    have hc' := not_lt.1 hc
    nlinarith
  have h5 : n - m < 1 := by exact_mod_cast h3
  have h6 : -1 < n - m := by exact_mod_cast h4
  omega

/-- The unfolding identity: for a periodic locally integrable `f`, the circle convolution equals
the line convolution `f ⋆ ρ_h` with the periodic extension of `f`. -/
lemma circleMollify_eq_mollifyLine (hρ : IsMollifier ρ) {L h : ℝ} (hL : 0 < L) (hh : 0 < h)
    {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (hper : Function.Periodic f L) (x : ℝ) :
    circleMollify ρ L h f x = mollifyLine ρ h f x := by
  set G : ℝ → ℝ := fun y => f y * scaledMollifier ρ h (x - y) with hG
  have hGi : Integrable G := integrable_mul_scaled_sub hρ hh hf x
  have hpt : ∀ y : ℝ, f y * periodMollifier ρ L h (x - y) = ∑' n : ℤ, G (y - n * L) := by
    intro y
    unfold periodMollifier
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
  calc circleMollify ρ L h f x
      = ∫ y in (-(L / 2))..(L / 2), ∑' n : ℤ, G (y - n * L) :=
        intervalIntegral.integral_congr fun y _ => hpt y
    _ = ∫ y in Ioc (-(L / 2)) (L / 2), ∑' n : ℤ, G (y - n * L) :=
        intervalIntegral.integral_of_le (by linarith)
    _ = ∑' n : ℤ, ∫ y in Ioc (-(L / 2)) (L / 2), G (y - n * L) :=
        (integral_tsum_of_summable_integral_norm hFi hFs).symm
    _ = ∑' n : ℤ, ∫ t in Ioc (-(L / 2) - n * L) (L / 2 - n * L), G t :=
        tsum_congr fun n => integral_Ioc_sub_tiles G hL n
    _ = ∫ t, G t := hsumG.tsum_eq
    _ = mollifyLine ρ h f x := rfl

end Unfolding

section Analysis

/-- The integrand of a periodic function is invariant under integer shifts. -/
lemma periodic_add_int_mul {f : ℝ → ℝ} {L : ℝ} (hper : Function.Periodic f L) (k : ℤ) (v : ℝ) :
    f (v + k * L) = f v := by
  have := hper.sub_int_mul_eq (x := v) (-k)
  push_cast at this
  rwa [neg_mul, sub_neg_eq_add] at this

/-- Shifting the kernel by a period of the integrand does not change the integral. -/
lemma integral_periodic_shift {f : ℝ → ℝ} {c : ℝ} (hc : ∀ v, f (v + c) = f v) (φ : ℝ → ℝ)
    (x : ℝ) : ∫ v, f v * φ (x - c - v) = ∫ v, f v * φ (x - v) := by
  have h1 : ∫ v, f v * φ (x - c - v) = ∫ v, f (v + c) * φ (x - (v + c)) := by
    congr 1
    funext v
    rw [hc, show x - (v + c) = x - c - v by ring]
  rw [h1]
  exact integral_add_right_eq_self (fun v => f v * φ (x - v)) c

/-- The integral against a kernel shifted by `kL` equals the integral against the unshifted
kernel, for a periodic integrand. -/
lemma integral_mul_shift_int {f : ℝ → ℝ} {L : ℝ} (hper : Function.Periodic f L) (φ : ℝ → ℝ)
    (t : ℝ) (k : ℤ) : ∫ v, f v * φ (t + k * L - v) = ∫ v, f v * φ (t - v) := by
  have hc : ∀ v, f (v + -(k * L)) = f v := fun v => by
    have := periodic_add_int_mul hper (-k) v
    rw [← this]
    congr 1
    push_cast
    ring
  have := integral_periodic_shift hc φ t
  rw [sub_neg_eq_add] at this
  exact this

/-- One-sided estimate: if `F` is differentiable on `(0, L/2]` with `|F'(r)| ≤ r^(-1-γ)`, then
`|F(L/2) - F(s)| ≤ ∫_s^{L/2} r^(-1-γ) dr` for `0 < s ≤ L/2`. -/
lemma abs_sub_le_integral_of_deriv_le {F : ℝ → ℝ} {γ L s : ℝ} (hs : 0 < s) (hsL : s ≤ L / 2)
    (hd : ∀ r, 0 < r → r ≤ L / 2 → DifferentiableAt ℝ F r)
    (hF' : ∀ r, 0 < r → r ≤ L / 2 → |deriv F r| ≤ r ^ (-1 - γ)) :
    |F (L / 2) - F s| ≤ ∫ r in s..(L / 2), r ^ (-1 - γ) := by
  have hcont : ContinuousOn F (Icc s (L / 2)) := fun r hr =>
    (hd r (lt_of_lt_of_le hs hr.1) hr.2).continuousAt.continuousWithinAt
  have hderiv : ∀ r ∈ Ioo s (L / 2), HasDerivAt F (deriv F r) r := fun r hr =>
    (hd r (hs.trans hr.1) hr.2.le).hasDerivAt
  have hφ : IntervalIntegrable (fun r : ℝ => r ^ (-1 - γ)) volume s (L / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hsL]
    refine ContinuousOn.rpow_const continuousOn_id fun r hr => Or.inl ?_
    exact (lt_of_lt_of_le hs hr.1).ne'
  have hle : ∀ᵐ r ∂(volume.restrict (uIoc s (L / 2))), ‖deriv F r‖ ≤ ‖r ^ (-1 - γ)‖ := by
    rw [uIoc_of_le hsL]
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_
    have hr0 : 0 < r := hs.trans hr.1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hr0.le _)]
    exact hF' r hr0 hr.2
  have hint : IntervalIntegrable (deriv F) volume s (L / 2) :=
    hφ.mono_fun (measurable_deriv F).aestronglyMeasurable.restrict hle
  have hFTC := integral_eq_sub_of_hasDerivAt_of_le hsL hcont hderiv hint
  rw [← hFTC]
  have hb : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioc s (L / 2) → ‖deriv F r‖ ≤ r ^ (-1 - γ) :=
    Filter.Eventually.of_forall fun r hr => by
      rw [Real.norm_eq_abs]
      exact hF' r (hs.trans hr.1) hr.2
  have := intervalIntegral.norm_integral_le_of_norm_le hsL hb hφ
  simpa [Real.norm_eq_abs] using this

end Analysis

section Windows

/-- The function `log |y|` is integrable on every symmetric compact interval. -/
lemma integrableOn_abs_log {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun y : ℝ => Real.log |y|) (Icc (-a) a) := by
  have hpos : IntegrableOn Real.log (Icc 0 a) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ha).1 intervalIntegrable_log'
  have h1 : IntegrableOn (fun y : ℝ => Real.log |y|) (Icc 0 a) :=
    hpos.congr_fun (fun y hy => by rw [abs_of_nonneg hy.1]) measurableSet_Icc
  have h3 : IntegrableOn (fun x : ℝ => Real.log |-x|) (-Icc 0 a) := h1.comp_neg
  rw [neg_Icc, neg_zero] at h3
  have h2 : IntegrableOn (fun y : ℝ => Real.log |y|) (Icc (-a) 0) := by
    simpa only [abs_neg] using h3
  rw [← Icc_union_Icc_eq_Icc (by linarith : -a ≤ 0) ha]
  exact h2.union h1

/-- For a function `B` with `B(|·|)` integrable on `[-a, a]`, the symmetric integral is twice the
integral over `[0, a]`. -/
lemma integral_symm_comp_abs {B : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hB : IntegrableOn (fun y => B |y|) (Icc (-a) a)) :
    ∫ y in Icc (-a) a, B |y| = 2 * ∫ r in (0 : ℝ)..a, B r := by
  have hII : IntervalIntegrable (fun y => B |y|) volume (-a) a :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 hB
  have hsub1 : uIcc (-a) 0 ⊆ uIcc (-a) a := by
    rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
    exact Icc_subset_Icc le_rfl (by linarith)
  have hsub2 : uIcc 0 a ⊆ uIcc (-a) a := by
    rw [uIcc_of_le ha, uIcc_of_le (by linarith)]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hL : ∫ y in (-a)..0, B |y| = ∫ x in (0 : ℝ)..a, B |x| := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := a) (fun y => B |y|)
    simpa [abs_neg] using this.symm
  have hR : ∫ x in (0 : ℝ)..a, B |x| = ∫ x in (0 : ℝ)..a, B x :=
    intervalIntegral.integral_congr fun x hx => by
      rw [uIcc_of_le ha] at hx
      rw [abs_of_nonneg hx.1]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -a ≤ a),
    ← intervalIntegral.integral_add_adjacent_intervals (hII.mono_set hsub1) (hII.mono_set hsub2),
    hL, hR]
  ring

/-- Four periods: the integral of a periodic function over `[-2L, 2L]` is four times its integral
over a fundamental domain. -/
lemma intervalIntegral_four_periods {g : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hg : Function.Periodic g L) (hgi : IntervalIntegrable g volume (-(L / 2)) (L / 2)) :
    ∫ y in (-(2 * L))..(2 * L), g y = 4 * ∫ y in (-(L / 2))..(L / 2), g y := by
  have hgi' : IntervalIntegrable g volume (-(L / 2)) (-(L / 2) + L) := by
    rw [show -(L / 2) + L = L / 2 by ring]
    exact hgi
  have hI : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    Function.Periodic.intervalIntegrable hg hL.ne' hgi' a b
  have e1 := Function.Periodic.intervalIntegral_add_eq hg (-(2 * L)) (-(L / 2))
  have e2 := Function.Periodic.intervalIntegral_add_eq hg (-L) (-(L / 2))
  have e3 := Function.Periodic.intervalIntegral_add_eq hg 0 (-(L / 2))
  have e4 := Function.Periodic.intervalIntegral_add_eq hg L (-(L / 2))
  rw [show -(2 * L) + L = -L by ring, show -(L / 2) + L = L / 2 by ring] at e1
  rw [show -L + L = 0 by ring, show -(L / 2) + L = L / 2 by ring] at e2
  rw [show (0 : ℝ) + L = L by ring, show -(L / 2) + L = L / 2 by ring] at e3
  rw [show L + L = 2 * L by ring, show -(L / 2) + L = L / 2 by ring] at e4
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI _ (-L)) (hI _ (2 * L)),
    ← intervalIntegral.integral_add_adjacent_intervals (hI (-L) 0) (hI 0 (2 * L)),
    ← intervalIntegral.integral_add_adjacent_intervals (hI 0 L) (hI L (2 * L)), e1, e2, e3, e4]
  ring

/-- Window bound for the `L`-periodic integrand `|f - c|`, when the window fits in the fundamental
domain: `∫_{t-h/2}^{t+h/2} |f - c| ≤ 2 ∫_0^{3h/2} B`, provided `|f(y) - c| ≤ B(|y|)` on the
fundamental domain. -/
lemma integral_window_sub_le_of_le {f : ℝ → ℝ} {L h t c : ℝ} {B : ℝ → ℝ}
    (hh : 0 < h) (h3 : 3 * h ≤ L) (ht : |t| ≤ h) (hf : LocallyIntegrable f volume)
    (hfb : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Icc (-(L / 2)) (L / 2) → |f y - c| ≤ B |y|)
    (hBnn : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Icc (-(L / 2)) (L / 2) → 0 ≤ B |y|)
    (hBint : IntegrableOn (fun y => B |y|) (Icc (-(L / 2)) (L / 2))) :
    ∫ y in Ioo (t - h / 2) (t + h / 2), |f y - c| ≤ 2 * ∫ r in (0 : ℝ)..(3 / 2 * h), B r := by
  have ha : 0 ≤ 3 / 2 * h := by linarith
  have hsub : Ioo (t - h / 2) (t + h / 2) ⊆ Icc (-(3 / 2 * h)) (3 / 2 * h) := by
    intro y hy
    rw [abs_le] at ht
    rw [mem_Ioo] at hy
    exact ⟨by linarith [hy.1, ht.1], by linarith [hy.2, ht.2]⟩
  have hsubL : Icc (-(3 / 2 * h)) (3 / 2 * h) ⊆ Icc (-(L / 2)) (L / 2) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hWL : Ioo (t - h / 2) (t + h / 2) ⊆ Icc (-(L / 2)) (L / 2) := hsub.trans hsubL
  have hfi : IntegrableOn (fun y => |f y - c|) (Icc (-(L / 2)) (L / 2)) :=
    ((hf.integrableOn_isCompact isCompact_Icc).sub (integrableOn_const (by simp))).abs
  calc ∫ y in Ioo (t - h / 2) (t + h / 2), |f y - c|
      ≤ ∫ y in Ioo (t - h / 2) (t + h / 2), B |y| :=
        setIntegral_mono_ae_restrict (hfi.mono_set hWL) (hBint.mono_set hWL)
          ((ae_restrict_iff' measurableSet_Ioo).2 (hfb.mono fun y hy hyW => hy (hWL hyW)))
    _ ≤ ∫ y in Icc (-(3 / 2 * h)) (3 / 2 * h), B |y| :=
        setIntegral_mono_set (hBint.mono_set hsubL)
          ((ae_restrict_iff' measurableSet_Icc).2 (hBnn.mono fun y hy hyI => hy (hsubL hyI)))
          hsub.eventuallyLE
    _ = 2 * ∫ r in (0 : ℝ)..(3 / 2 * h), B r :=
        integral_symm_comp_abs ha (hBint.mono_set hsubL)

/-- Window bound for the periodic integrand `|f - c|`, when the window is longer than the
fundamental domain: `∫_{t-h/2}^{t+h/2} |f - c| ≤ 8 ∫_0^{L/2} B`. -/
lemma integral_window_sub_le_of_lt {f : ℝ → ℝ} {L h t c : ℝ} {B : ℝ → ℝ}
    (hper : Function.Periodic f L) (hL : 0 < L) (hhL : h ≤ L) (ht : |t| ≤ h)
    (hf : LocallyIntegrable f volume)
    (hfb : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Icc (-(L / 2)) (L / 2) → |f y - c| ≤ B |y|)
    (hBint : IntegrableOn (fun y => B |y|) (Icc (-(L / 2)) (L / 2))) :
    ∫ y in Ioo (t - h / 2) (t + h / 2), |f y - c| ≤ 8 * ∫ r in (0 : ℝ)..(L / 2), B r := by
  have hsub : Ioo (t - h / 2) (t + h / 2) ⊆ Icc (-(2 * L)) (2 * L) := by
    intro y hy
    rw [abs_le] at ht
    rw [mem_Ioo] at hy
    exact ⟨by linarith [hy.1, ht.1], by linarith [hy.2, ht.2]⟩
  have hper' : Function.Periodic (fun y => |f y - c|) L := fun y => by
    simp only [hper y]
  have hfi : IntegrableOn (fun y => |f y - c|) (Icc (-(2 * L)) (2 * L)) :=
    ((hf.integrableOn_isCompact isCompact_Icc).sub (integrableOn_const (by simp))).abs
  have hgi : IntervalIntegrable (fun y => |f y - c|) volume (-(L / 2)) (L / 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2
      ((hf.integrableOn_isCompact isCompact_Icc).sub (integrableOn_const (by simp))).abs
  have hmono : ∫ y in (-(L / 2))..(L / 2), |f y - c| ≤ ∫ y in (-(L / 2))..(L / 2), B |y| := by
    rw [intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_mono_ae_restrict
      (((hf.integrableOn_isCompact isCompact_Icc).sub (integrableOn_const (by simp))).abs)
      hBint ((ae_restrict_iff' measurableSet_Icc).2 (hfb.mono fun y hy hyI => hy hyI))
  calc ∫ y in Ioo (t - h / 2) (t + h / 2), |f y - c|
      ≤ ∫ y in Icc (-(2 * L)) (2 * L), |f y - c| :=
        setIntegral_mono_set hfi
          (Filter.Eventually.of_forall fun y => abs_nonneg _) hsub.eventuallyLE
    _ = ∫ y in (-(2 * L))..(2 * L), |f y - c| := by
        rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
    _ = 4 * ∫ y in (-(L / 2))..(L / 2), |f y - c| :=
        intervalIntegral_four_periods hL hper' hgi
    _ ≤ 4 * ∫ y in (-(L / 2))..(L / 2), B |y| :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ = 8 * ∫ r in (0 : ℝ)..(L / 2), B r := by
        rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
          integral_symm_comp_abs (by linarith) (hBint)]
        ring

/-- The integral of `r ^ (-γ) / γ` over `[0, a]`. -/
lemma integral_rpow_div_zero_to {γ a : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) :
    ∫ r in (0 : ℝ)..a, r ^ (-γ) / γ = a ^ (1 - γ) / (γ * (1 - γ)) := by
  rw [intervalIntegral.integral_div, integral_rpow (Or.inl (by linarith))]
  have e : -γ + 1 = 1 - γ := by ring
  rw [e, Real.zero_rpow (by linarith : (0 : ℝ) < 1 - γ).ne', sub_zero]
  field_simp

/-- The integral of `log (L/2) - log r` over `[0, a]`. -/
lemma integral_log_sub_zero_to (L : ℝ) (a : ℝ) :
    ∫ r in (0 : ℝ)..a, (Real.log (L / 2) - Real.log r) =
      a * (1 + (Real.log (L / 2) - Real.log a)) := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_log',
    intervalIntegral.integral_const, integral_log]
  simp only [smul_eq_mul, Real.log_zero, mul_zero, sub_zero]
  ring


end Windows

section Estimates

/-- Almost every point is nonzero. -/
lemma ae_ne_zero_volume : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 0 := by
  rw [ae_iff]
  simp

/-- The integral of `r ^ (-γ)` over `[0, a]` for `γ < 1`. -/
lemma integral_rpow_neg_zero_to {γ a : ℝ} (hγ1 : γ < 1) :
    ∫ r in (0 : ℝ)..a, r ^ (-γ) = a ^ (1 - γ) / (1 - γ) := by
  rw [integral_rpow (Or.inl (by linarith))]
  have e : -γ + 1 = 1 - γ := by ring
  rw [e, Real.zero_rpow (by linarith : (0 : ℝ) < 1 - γ).ne', sub_zero]

/-- The circle sup estimate for `0 ≤ γ < 1`: the convolution is bounded by
`C max(|x|, h)^(-γ)`, where `|x|` is the distance to `0` on the circle. -/
theorem circleMollify_sup_bound (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ f : ℝ → ℝ, Function.Periodic f L →
      LocallyIntegrable f volume →
      (∀ᵐ y ∂(volume : Measure ℝ), circDist L y ≠ 0 → |f y| ≤ circDist L y ^ (-γ)) →
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
        |circleMollify ρ L h f x| ≤ C * (max (circDist L x) h) ^ (-γ) := by
  obtain ⟨M, hM0, hM⟩ := hρ.exists_bound
  set M' := M + 1 with hM'
  have hM'pos : 0 < M' := by linarith
  have hM'' : ∀ x, |ρ x| ≤ M' := fun x => (hM x).trans (by linarith)
  have h1γ : 0 < 1 - γ := by linarith
  have hA0 : 0 ≤ 8 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ) :=
    div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)) h1γ.le
  have h2 : 0 < (2 : ℝ) ^ γ := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨M' * (2 ^ γ + 8 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)),
    mul_pos hM'pos (by linarith), ?_⟩
  intro L hL1 f hper hf hfb h hh hh1 x
  have hL : 0 < L := by linarith
  have hMh : 0 ≤ M' * h⁻¹ := mul_nonneg hM'pos.le (inv_nonneg.2 hh.le)
  rw [circleMollify_eq_mollifyLine hρ hL hh hf hper x]
  have hmol_x := abs_mollifyLine_le_window hρ hh hM'' hf x
  rcases le_total h (circDist L x) with hx | hx
  · -- Far from the singularity: the window integral is controlled by `circDist x / 2`.
    have hfar := window_abs_le_far_gen (δ := circDist L) (circDist_le_add_abs hL) hf hγ0 hh
      hfb hx
    have hmax : max (circDist L x) h = circDist L x := max_eq_left hx
    rw [hmax]
    have hd0 : 0 ≤ circDist L x := circDist_nonneg L x
    have hx0 : 0 ≤ circDist L x ^ (-γ) := Real.rpow_nonneg hd0 _
    calc |mollifyLine ρ h f x|
        ≤ M' * h⁻¹ * (h * (circDist L x / 2) ^ (-γ)) :=
          hmol_x.trans (mul_le_mul_of_nonneg_left hfar hMh)
      _ = M' * (circDist L x ^ (-γ) * 2 ^ γ) := by
          rw [div_two_rpow_neg hd0]
          field_simp
      _ ≤ M' * (2 ^ γ + 8 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)) * circDist L x ^ (-γ) := by
          have e : M' * (2 ^ γ + 8 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)) * circDist L x ^ (-γ) =
              M' * (circDist L x ^ (-γ) * 2 ^ γ) +
                M' * (8 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)) * circDist L x ^ (-γ) := by ring
          rw [e]
          have : 0 ≤ M' * (8 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)) * circDist L x ^ (-γ) :=
            mul_nonneg (mul_nonneg hM'pos.le hA0) hx0
          linarith
  · -- Near the singularity: move the window to `t = x - L round(x/L)`, with `|t| = circDist x`.
    set t := x - L * (round (x / L) : ℝ) with ht_def
    have hxt : mollifyLine ρ h f x = mollifyLine ρ h f t := by
      have := integral_mul_shift_int hper (scaledMollifier ρ h) t (round (x / L))
      have e : t + (round (x / L) : ℝ) * L = x := by rw [ht_def]; ring
      rw [e] at this
      exact this
    have htd : |t| ≤ h := by
      have : |t| = circDist L x := rfl
      rw [this]
      exact hx
    have hfb2 : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Icc (-(L / 2)) (L / 2) →
        |f y - 0| ≤ (fun r : ℝ => r ^ (-γ)) |y| := by
      filter_upwards [hfb, ae_ne_zero_volume] with y hy hy0 hI
      have hyL : |y| ≤ L / 2 := abs_le.2 hI
      have hd : circDist L y = |y| := circDist_eq_abs hL hyL
      have hne : circDist L y ≠ 0 := by
        rw [hd]
        exact abs_ne_zero.2 hy0
      rw [sub_zero]
      have := hy hne
      rw [hd] at this
      exact this
    have hBint : IntegrableOn (fun y : ℝ => |y| ^ (-γ)) (Icc (-(L / 2)) (L / 2)) :=
      integrableOn_abs_rpow (by linarith) (by linarith)
    have hBnn : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Icc (-(L / 2)) (L / 2) →
        0 ≤ (fun r : ℝ => r ^ (-γ)) |y| :=
      Filter.Eventually.of_forall fun y _ => Real.rpow_nonneg (abs_nonneg y) _
    have hwin : ∫ y in Ioo (t - h / 2) (t + h / 2), |f y| ≤
        8 * ((3 / 2 * h) ^ (1 - γ) / (1 - γ)) := by
      by_cases h3 : 3 * h ≤ L
      · have := integral_window_sub_le_of_le (B := fun r : ℝ => r ^ (-γ)) hh h3 htd hf
          hfb2 hBnn hBint
        simp only [sub_zero] at this
        rw [integral_rpow_neg_zero_to hγ1] at this
        have hnn : 0 ≤ (3 / 2 * h) ^ (1 - γ) / (1 - γ) :=
          div_nonneg (Real.rpow_nonneg (by linarith) _) h1γ.le
        linarith
      · have hhL : h ≤ L := by linarith
        have := integral_window_sub_le_of_lt (B := fun r : ℝ => r ^ (-γ)) hper hL hhL htd hf
          hfb2 hBint
        simp only [sub_zero] at this
        rw [integral_rpow_neg_zero_to hγ1] at this
        have hmono : (L / 2) ^ (1 - γ) ≤ (3 / 2 * h) ^ (1 - γ) :=
          Real.rpow_le_rpow (by linarith) (by linarith) h1γ.le
        have hdiv : (L / 2) ^ (1 - γ) / (1 - γ) ≤ (3 / 2 * h) ^ (1 - γ) / (1 - γ) :=
          div_le_div_of_nonneg_right hmono h1γ.le
        linarith
    have hmax : max (circDist L x) h = h := max_eq_right hx
    rw [hmax]
    have hkey : M' * h⁻¹ * (8 * ((3 / 2 * h) ^ (1 - γ) / (1 - γ))) =
        M' * (8 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)) * h ^ (-γ) := by
      rw [Real.mul_rpow (by norm_num) hh.le, ← inv_mul_rpow_one_sub hh]
      ring
    have hhp : 0 ≤ h ^ (-γ) := Real.rpow_nonneg hh.le _
    calc |mollifyLine ρ h f x|
        = |mollifyLine ρ h f t| := by rw [hxt]
      _ ≤ M' * h⁻¹ * ∫ y in Ioo (t - h / 2) (t + h / 2), |f y| :=
          abs_mollifyLine_le_window hρ hh hM'' hf t
      _ ≤ M' * h⁻¹ * (8 * ((3 / 2 * h) ^ (1 - γ) / (1 - γ))) :=
          mul_le_mul_of_nonneg_left hwin hMh
      _ = M' * (8 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)) * h ^ (-γ) := hkey
      _ ≤ M' * (2 ^ γ + 8 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)) * h ^ (-γ) := by
          have e : M' * (2 ^ γ + 8 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)) * h ^ (-γ) =
              M' * (8 * (3 / 2 : ℝ) ^ (1 - γ) / (1 - γ)) * h ^ (-γ) +
                M' * 2 ^ γ * h ^ (-γ) := by ring
          rw [e]
          have : 0 ≤ M' * 2 ^ γ * h ^ (-γ) := mul_nonneg (mul_nonneg hM'pos.le h2.le) hhp
          linarith

end Estimates

section Reference

/-- The bound `|f(y) - f(L/2)| ≤ B(|y|)` for `0 < |y| ≤ L/2`, given that `B` dominates the one-sided
integrals `∫_s^{L/2} r^(-1-γ)`. The negative side is reduced to the positive side by reflection
and periodicity. -/
lemma abs_sub_ref_le {f : ℝ → ℝ} {γ L : ℝ} {B : ℝ → ℝ} (hper : Function.Periodic f L)
    (hL : 0 < L) (hdf : ∀ y, circDist L y ≠ 0 → DifferentiableAt ℝ f y)
    (hfd : ∀ y, circDist L y ≠ 0 → |deriv f y| ≤ circDist L y ^ (-1 - γ))
    (hB : ∀ s, 0 < s → s ≤ L / 2 → ∫ r in s..(L / 2), r ^ (-1 - γ) ≤ B s)
    {y : ℝ} (hy0 : y ≠ 0) (hyL : |y| ≤ L / 2) : |f y - f (L / 2)| ≤ B |y| := by
  have hcirc : ∀ r, 0 < r → r ≤ L / 2 → circDist L r = r := fun r hr0 hrL => by
    rw [circDist_eq_abs hL (by rw [abs_of_pos hr0]; exact hrL), abs_of_pos hr0]
  have hcirc' : ∀ r, 0 < r → r ≤ L / 2 → circDist L (-r) = r := fun r hr0 hrL => by
    rw [circDist_eq_abs hL (by rw [abs_neg, abs_of_pos hr0]; exact hrL), abs_neg,
      abs_of_pos hr0]
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · -- Negative side: reflect `f` and use the periodicity `f(-L/2) = f(L/2)`.
    have hyabs : |y| = -y := abs_of_neg hneg
    have hsL : -y ≤ L / 2 := by
      rw [hyabs] at hyL
      linarith
    have hpL : f (-(L / 2)) = f (L / 2) := by
      have := hper (-(L / 2))
      rw [show -(L / 2) + L = L / 2 by ring] at this
      exact this.symm
    have hd : ∀ r, 0 < r → r ≤ L / 2 → DifferentiableAt ℝ (fun r => f (-r)) r := by
      intro r hr0 hrL
      exact ((hdf (-r) (by rw [hcirc' r hr0 hrL]; exact hr0.ne')).comp r
        differentiableAt_id.neg)
    have hF' : ∀ r, 0 < r → r ≤ L / 2 → |deriv (fun r => f (-r)) r| ≤ r ^ (-1 - γ) := by
      intro r hr0 hrL
      rw [deriv_comp_neg, abs_neg]
      have := hfd (-r) (by rw [hcirc' r hr0 hrL]; exact hr0.ne')
      rw [hcirc' r hr0 hrL] at this
      exact this
    have key := abs_sub_le_integral_of_deriv_le (F := fun r => f (-r)) (γ := γ) (L := L)
      (s := -y) (by linarith) hsL hd hF'
    simp only [neg_neg] at key
    rw [hpL, abs_sub_comm] at key
    rw [hyabs]
    have hB' := hB (-y) (by linarith) hsL
    exact key.trans hB'
  · -- Positive side: the integral from `y` to `L/2`.
    have hsL : y ≤ L / 2 := by
      rw [abs_of_pos hpos] at hyL
      exact hyL
    have hd : ∀ r, 0 < r → r ≤ L / 2 → DifferentiableAt ℝ f r := fun r hr0 hrL =>
      hdf r (by rw [hcirc r hr0 hrL]; exact hr0.ne')
    have hF' : ∀ r, 0 < r → r ≤ L / 2 → |deriv f r| ≤ r ^ (-1 - γ) := fun r hr0 hrL => by
      have := hfd r (by rw [hcirc r hr0 hrL]; exact hr0.ne')
      rw [hcirc r hr0 hrL] at this
      exact this
    have key := abs_sub_le_integral_of_deriv_le (F := f) (γ := γ) (L := L) (s := y) hpos hsL
      hd hF'
    rw [abs_sub_comm, abs_of_pos hpos]
    exact key.trans (hB y hpos hsL)

/-- Subtracting a constant does not change the convolution of an integrand against the derivative
of a mollifier, since the mollifier has integral zero. -/
lemma integral_mul_sub_const_deriv {f : ℝ → ℝ} {h t : ℝ} (ρ : ℝ → ℝ) (hρ : IsMollifier ρ)
    (hh : 0 < h) (c : ℝ) (hf : LocallyIntegrable f volume) :
    ∫ y, f y * deriv (scaledMollifier ρ h) (t - y) =
      ∫ y, (f y - c) * deriv (scaledMollifier ρ h) (t - y) := by
  have hC1 : Continuous (deriv (scaledMollifier ρ h)) :=
    (contDiff_scaledMollifier hρ).continuous_deriv (by simp)
  have hcs : HasCompactSupport (deriv (scaledMollifier ρ h)) :=
    (hasCompactSupport_scaledMollifier hρ hh).deriv
  have hint1 : Integrable fun y => f y * deriv (scaledMollifier ρ h) (t - y) :=
    integrable_mul_sub_of_support hf hC1 (fun u hu => deriv_scaledMollifier_eq_zero hρ hh hu)
  have hint2 : Integrable fun y => c * deriv (scaledMollifier ρ h) (t - y) :=
    ((hC1.integrable_of_hasCompactSupport hcs).comp_sub_left t).const_mul c
  have hzero : ∫ y, c * deriv (scaledMollifier ρ h) (t - y) = 0 := by
    rw [MeasureTheory.integral_const_mul,
      integral_sub_left_eq_self (deriv (scaledMollifier ρ h)) volume t,
      integral_deriv_scaledMollifier hρ hh, mul_zero]
  simp_rw [sub_mul]
  rw [integral_sub hint1 hint2, hzero, sub_zero]

end Reference

section DerivativeEstimates

/-- The one-sided integral `∫_s^{L/2} r^(-1-γ) dr ≤ s^(-γ)/γ` for `γ > 0`. -/
lemma integral_rpow_neg_one_sub_le {γ L s : ℝ} (hγ : 0 < γ) (hs : 0 < s)
    (hsL : s ≤ L / 2) : ∫ r in s..(L / 2), r ^ (-1 - γ) ≤ s ^ (-γ) / γ := by
  have hne : (-1 - γ) ≠ -1 := fun h => by linarith
  have h0 : (0 : ℝ) ∉ uIcc s (L / 2) := fun h0 => by
    rw [uIcc_of_le hsL] at h0
    linarith [h0.1]
  rw [integral_rpow (Or.inr ⟨hne, h0⟩)]
  have e : -1 - γ + 1 = -γ := by ring
  rw [e]
  have hA : 0 ≤ (L / 2) ^ (-γ) := Real.rpow_nonneg (by linarith) _
  have hid : ((L / 2) ^ (-γ) - s ^ (-γ)) / (-γ) = s ^ (-γ) / γ - (L / 2) ^ (-γ) / γ := by
    field_simp
    ring
  rw [hid]
  linarith [div_nonneg hA hγ.le]

/-- The one-sided integral `∫_s^{L/2} r^(-1-0) dr = log(L/2) - log s`. -/
lemma integral_inv_sub_eq {L s : ℝ} (hs : 0 < s) (hsL : s ≤ L / 2) :
    ∫ r in s..(L / 2), r ^ (-1 - (0 : ℝ)) = Real.log (L / 2) - Real.log s := by
  have e : (fun r : ℝ => r ^ (-1 - (0 : ℝ))) = fun r => r⁻¹ :=
    funext fun r => by rw [sub_zero, Real.rpow_neg_one]
  rw [e, integral_inv_of_pos hs (by linarith), Real.log_div (by linarith) hs.ne']

/-- The log-type window bound: `log(L/2) - log(3h/2) ≤ log(L/h)` for `3h ≤ L`. -/
lemma log_sub_log_le {L h : ℝ} (hL : 0 < L) (hh : 0 < h) (h3 : 3 * h ≤ L) :
    Real.log (L / 2) - Real.log (3 / 2 * h) ≤ Real.log (L / h) := by
  rw [← Real.log_div (by linarith) (by positivity)]
  apply Real.log_le_log (by positivity)
  rw [div_le_div_iff₀ (by positivity) hh]
  nlinarith [mul_pos hL hh]

/-- The circle derivative estimate for `0 < γ < 1`: the convolution is differentiable and its
derivative is bounded by `C max(|x|, h)^(-1-γ)`. -/
theorem circleMollify_deriv_bound_pos (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ f : ℝ → ℝ, Function.Periodic f L →
      LocallyIntegrable f volume →
      (∀ y : ℝ, circDist L y ≠ 0 → DifferentiableAt ℝ f y) →
      (∀ y : ℝ, circDist L y ≠ 0 → |deriv f y| ≤ circDist L y ^ (-1 - γ)) →
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ, ∃ D : ℝ,
        HasDerivAt (circleMollify ρ L h f) D x ∧
          |D| ≤ C * (max (circDist L x) h) ^ (-1 - γ) := by
  obtain ⟨M1, hM1_0, hM1⟩ := hρ.exists_bound_deriv
  set M1' := M1 + 1 with hM1'
  have hM1'pos : 0 < M1' := by linarith
  have hM1ge : 1 ≤ M1' := by linarith
  have hM1'' : ∀ z, |deriv ρ z| ≤ M1' := fun z => (hM1 z).trans (by linarith)
  have h1γ : 0 < 1 - γ := by linarith
  have hγ1' : 0 < γ * (1 - γ) := mul_pos hγ0 h1γ
  have hA0 : 0 ≤ 8 * (3 / 2 : ℝ) ^ (1 - γ) / (γ * (1 - γ)) :=
    div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)) hγ1'.le
  have h21 : 0 < (2 : ℝ) ^ (1 + γ) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨M1' * (2 ^ (1 + γ) + 8 * (3 / 2 : ℝ) ^ (1 - γ) / (γ * (1 - γ))),
    mul_pos hM1'pos (by linarith), ?_⟩
  intro L hL1 f hper hf hdf hfd h hh hh1 x
  have hL : 0 < L := by linarith
  have hfun : circleMollify ρ L h f = mollifyLine ρ h f :=
    funext (circleMollify_eq_mollifyLine hρ hL hh hf hper)
  rw [hfun]
  rcases le_total h (circDist L x) with hx | hx
  · -- Far from the singularity.
    have hdiff := hasDerivAt_mollifyLine_far_gen (δ := circDist L) (f := f)
      (circDist_le_add_abs hL) hγ0.le hρ hh hf hdf hfd hx
    refine ⟨_, hdiff, ?_⟩
    have hb := abs_integral_deriv_far_le_gen (δ := circDist L) (f := f)
      (circDist_le_add_abs hL) hγ0.le hρ hh hfd hx
    have hmax : max (circDist L x) h = circDist L x := max_eq_left hx
    rw [hmax]
    have hd0 : 0 ≤ circDist L x := circDist_nonneg L x
    have hx0 : 0 ≤ circDist L x ^ (-1 - γ) := Real.rpow_nonneg hd0 _
    calc |∫ u, deriv f (x - u) * scaledMollifier ρ h u|
        ≤ (circDist L x / 2) ^ (-1 - γ) := hb
      _ = circDist L x ^ (-1 - γ) * 2 ^ (1 + γ) := by
          rw [show (-1 - γ : ℝ) = -(1 + γ) by ring, div_two_rpow_neg hd0]
      _ ≤ M1' * (2 ^ (1 + γ) + 8 * (3 / 2 : ℝ) ^ (1 - γ) / (γ * (1 - γ))) *
            circDist L x ^ (-1 - γ) := by
          have e : M1' * (2 ^ (1 + γ) + 8 * (3 / 2 : ℝ) ^ (1 - γ) / (γ * (1 - γ))) *
              circDist L x ^ (-1 - γ) =
              circDist L x ^ (-1 - γ) * 2 ^ (1 + γ) +
                ((M1' - 1) * 2 ^ (1 + γ) * circDist L x ^ (-1 - γ) +
                  M1' * (8 * (3 / 2 : ℝ) ^ (1 - γ) / (γ * (1 - γ))) *
                    circDist L x ^ (-1 - γ)) := by ring
          rw [e]
          have h1 : 0 ≤ (M1' - 1) * 2 ^ (1 + γ) * circDist L x ^ (-1 - γ) :=
            mul_nonneg (mul_nonneg (sub_nonneg.2 hM1ge) h21.le) hx0
          have h2 : 0 ≤ M1' * (8 * (3 / 2 : ℝ) ^ (1 - γ) / (γ * (1 - γ))) *
              circDist L x ^ (-1 - γ) := mul_nonneg (mul_nonneg hM1'pos.le hA0) hx0
          linarith
  · -- Near the singularity: move to `t = x - L round(x/L)` and subtract `f(L/2)`.
    set t := x - L * (round (x / L) : ℝ) with ht_def
    have hxt : ∫ y, f y * deriv (scaledMollifier ρ h) (x - y) =
        ∫ y, f y * deriv (scaledMollifier ρ h) (t - y) := by
      have := integral_mul_shift_int hper (deriv (scaledMollifier ρ h)) t (round (x / L))
      have e : t + (round (x / L) : ℝ) * L = x := by rw [ht_def]; ring
      rw [e] at this
      exact this
    have htd : |t| ≤ h := by
      have : |t| = circDist L x := rfl
      rw [this]
      exact hx
    have hfb_ref : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Icc (-(L / 2)) (L / 2) →
        |f y - f (L / 2)| ≤ (fun r : ℝ => r ^ (-γ) / γ) |y| := by
      filter_upwards [ae_ne_zero_volume] with y hy0 hI
      exact abs_sub_ref_le (γ := γ) hper hL hdf hfd
        (fun s hs hsL => integral_rpow_neg_one_sub_le hγ0 hs hsL) hy0 (abs_le.2 hI)
    have hBnn : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Icc (-(L / 2)) (L / 2) →
        0 ≤ (fun r : ℝ => r ^ (-γ) / γ) |y| :=
      Filter.Eventually.of_forall fun y _ => div_nonneg (Real.rpow_nonneg (abs_nonneg y) _) hγ0.le
    have hBint : IntegrableOn (fun y : ℝ => (fun r : ℝ => r ^ (-γ) / γ) |y|)
        (Icc (-(L / 2)) (L / 2)) :=
      (integrableOn_abs_rpow (by linarith) (by linarith)).div_const γ
    have hW : ∫ y in Ioo (t - h / 2) (t + h / 2), |f y - f (L / 2)| ≤
        8 * ((3 / 2 * h) ^ (1 - γ) / (γ * (1 - γ))) := by
      by_cases h3 : 3 * h ≤ L
      · have := integral_window_sub_le_of_le (B := fun r : ℝ => r ^ (-γ) / γ) hh h3 htd hf
          hfb_ref hBnn hBint
        rw [integral_rpow_div_zero_to hγ0 hγ1] at this
        have hnn : 0 ≤ (3 / 2 * h) ^ (1 - γ) / (γ * (1 - γ)) :=
          div_nonneg (Real.rpow_nonneg (by linarith) _) hγ1'.le
        linarith
      · have hhL : h ≤ L := by linarith
        have := integral_window_sub_le_of_lt (B := fun r : ℝ => r ^ (-γ) / γ) hper hL hhL htd hf
          hfb_ref hBint
        rw [integral_rpow_div_zero_to hγ0 hγ1] at this
        have hmono : (L / 2) ^ (1 - γ) ≤ (3 / 2 * h) ^ (1 - γ) :=
          Real.rpow_le_rpow (by linarith) (by linarith) h1γ.le
        have hdiv : (L / 2) ^ (1 - γ) / (γ * (1 - γ)) ≤
            (3 / 2 * h) ^ (1 - γ) / (γ * (1 - γ)) :=
          div_le_div_of_nonneg_right hmono hγ1'.le
        linarith
    refine ⟨(∫ y, f y * deriv (scaledMollifier ρ h) (x - y)),
      hasDerivAt_mollifyLine hρ hh hf x, ?_⟩
    rw [hxt]
    have hmax : max (circDist L x) h = h := max_eq_right hx
    rw [hmax]
    have hφc : Continuous (deriv (scaledMollifier ρ h)) :=
      (contDiff_scaledMollifier hρ).continuous_deriv (by simp)
    have hD := norm_integral_mul_le_window (g := fun y => f y - f (L / 2))
      (φ := deriv (scaledMollifier ρ h)) (x := t) (r := h / 2) (K := M1' * (h⁻¹ * h⁻¹))
      (hf.sub (locallyIntegrable_const (f (L / 2)))) hφc (abs_deriv_scaledMollifier_le hρ hh hM1'')
      (fun u hu => deriv_scaledMollifier_eq_zero hρ hh hu)
    rw [integral_mul_sub_const_deriv ρ hρ hh (f (L / 2)) hf]
    have hinv : 0 ≤ h⁻¹ * h⁻¹ := mul_nonneg (inv_nonneg.2 hh.le) (inv_nonneg.2 hh.le)
    refine le_trans hD ?_
    refine le_trans (mul_le_mul_of_nonneg_left hW (mul_nonneg hM1'pos.le hinv)) ?_
    have hid : M1' * (h⁻¹ * h⁻¹) * (8 * ((3 / 2 * h) ^ (1 - γ) / (γ * (1 - γ)))) =
        M1' * (8 * (3 / 2 : ℝ) ^ (1 - γ) / (γ * (1 - γ))) * h ^ (-1 - γ) := by
      rw [Real.mul_rpow (by norm_num) hh.le, ← inv_mul_inv_mul_rpow_one_sub hh]
      ring
    rw [hid]
    have hhp : 0 ≤ h ^ (-1 - γ) := Real.rpow_nonneg hh.le _
    have e : M1' * (2 ^ (1 + γ) + 8 * (3 / 2 : ℝ) ^ (1 - γ) / (γ * (1 - γ))) * h ^ (-1 - γ) =
        M1' * (8 * (3 / 2 : ℝ) ^ (1 - γ) / (γ * (1 - γ))) * h ^ (-1 - γ) +
          M1' * 2 ^ (1 + γ) * h ^ (-1 - γ) := by ring
    rw [e]
    have : 0 ≤ M1' * 2 ^ (1 + γ) * h ^ (-1 - γ) :=
      mul_nonneg (mul_nonneg hM1'pos.le h21.le) hhp
    linarith
end DerivativeEstimates

section LogDerivative

/-- The circle derivative estimate at the endpoint `γ = 0`: the derivative of the convolution is
bounded by `C (1 + log(L/h)) max(|x|, h)^(-1)`, with `C` depending only on `ρ`. -/
theorem circleMollify_deriv_bound_log (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ f : ℝ → ℝ, Function.Periodic f L →
      LocallyIntegrable f volume →
      (∀ y : ℝ, circDist L y ≠ 0 → DifferentiableAt ℝ f y) →
      (∀ y : ℝ, circDist L y ≠ 0 → |deriv f y| ≤ circDist L y ^ (-1 : ℝ)) →
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ, ∃ D : ℝ,
        HasDerivAt (circleMollify ρ L h f) D x ∧
          |D| ≤ C * (1 + Real.log (L / h)) * (max (circDist L x) h) ^ (-1 : ℝ) := by
  obtain ⟨M1, hM1_0, hM1⟩ := hρ.exists_bound_deriv
  set M1' := M1 + 1 with hM1'
  have hM1'pos : 0 < M1' := by linarith
  have hM1'' : ∀ z, |deriv ρ z| ≤ M1' := fun z => (hM1 z).trans (by linarith)
  refine ⟨12 * M1' + 2, by linarith, ?_⟩
  intro L hL1 f hper hf hdf hfd h hh hh1 x
  have hL : 0 < L := by linarith
  have hfun : circleMollify ρ L h f = mollifyLine ρ h f :=
    funext (circleMollify_eq_mollifyLine hρ hL hh hf hper)
  rw [hfun]
  have hlog0 : 0 ≤ Real.log (L / h) := Real.log_nonneg (by rw [le_div_iff₀ hh]; linarith)
  have hfd' : ∀ y : ℝ, circDist L y ≠ 0 → |deriv f y| ≤ circDist L y ^ (-1 - (0 : ℝ)) := by
    intro y hy
    rw [sub_zero]
    exact hfd y hy
  rcases le_total h (circDist L x) with hx | hx
  · -- Far from the singularity.
    have hdiff := hasDerivAt_mollifyLine_far_gen (δ := circDist L) (f := f)
      (circDist_le_add_abs hL) (le_refl (0 : ℝ)) hρ hh hf hdf hfd' hx
    refine ⟨_, hdiff, ?_⟩
    have hb := abs_integral_deriv_far_le_gen (δ := circDist L) (f := f)
      (circDist_le_add_abs hL) (le_refl (0 : ℝ)) hρ hh hfd' hx
    have hmax : max (circDist L x) h = circDist L x := max_eq_left hx
    rw [hmax]
    have hd0 : 0 ≤ circDist L x := circDist_nonneg L x
    have hinv : 0 ≤ circDist L x ^ (-1 : ℝ) := Real.rpow_nonneg hd0 _
    have hval : (circDist L x / 2) ^ (-1 - (0 : ℝ)) = circDist L x ^ (-1 : ℝ) * 2 := by
      rw [show (-1 - (0 : ℝ)) = -(1 : ℝ) by norm_num, div_two_rpow_neg hd0, Real.rpow_one]
    rw [hval] at hb
    have hC : 2 ≤ 12 * M1' + 2 := by linarith
    have hlog1 : 1 ≤ 1 + Real.log (L / h) := by linarith
    calc |∫ u, deriv f (x - u) * scaledMollifier ρ h u|
        ≤ circDist L x ^ (-1 : ℝ) * 2 := hb
      _ ≤ (12 * M1' + 2) * (1 + Real.log (L / h)) * circDist L x ^ (-1 : ℝ) := by
          have h1 : 2 ≤ (12 * M1' + 2) * (1 + Real.log (L / h)) := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_right h1 hinv]
  · -- Near the singularity: move to `t`, subtract `f(L/2)`, and use the logarithmic kernel.
    set t := x - L * (round (x / L) : ℝ) with ht_def
    have hxt : ∫ y, f y * deriv (scaledMollifier ρ h) (x - y) =
        ∫ y, f y * deriv (scaledMollifier ρ h) (t - y) := by
      have := integral_mul_shift_int hper (deriv (scaledMollifier ρ h)) t (round (x / L))
      have e : t + (round (x / L) : ℝ) * L = x := by rw [ht_def]; ring
      rw [e] at this
      exact this
    have htd : |t| ≤ h := by
      have : |t| = circDist L x := rfl
      rw [this]
      exact hx
    have hfb_ref : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Icc (-(L / 2)) (L / 2) →
        |f y - f (L / 2)| ≤ (fun r : ℝ => Real.log (L / 2) - Real.log r) |y| := by
      filter_upwards [ae_ne_zero_volume] with y hy0 hI
      exact abs_sub_ref_le (γ := 0) hper hL hdf hfd'
        (fun s hs hsL => (integral_inv_sub_eq hs hsL).le) hy0 (abs_le.2 hI)
    have hBnn : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Icc (-(L / 2)) (L / 2) →
        0 ≤ (fun r : ℝ => Real.log (L / 2) - Real.log r) |y| := by
      filter_upwards [ae_ne_zero_volume] with y hy0 hI
      have hpos : 0 < |y| := abs_pos.2 hy0
      have := Real.log_le_log hpos (abs_le.2 hI)
      show 0 ≤ Real.log (L / 2) - Real.log |y|
      linarith
    have hBint : IntegrableOn (fun y : ℝ => (fun r : ℝ => Real.log (L / 2) - Real.log r) |y|)
        (Icc (-(L / 2)) (L / 2)) :=
      (integrableOn_const (by simp)).sub (integrableOn_abs_log (by linarith))
    have hW : ∫ y in Ioo (t - h / 2) (t + h / 2), |f y - f (L / 2)| ≤
        12 * h * (1 + Real.log (L / h)) := by
      have hlogh : 0 ≤ 1 + Real.log (L / h) := by linarith
      by_cases h3 : 3 * h ≤ L
      · have := integral_window_sub_le_of_le (B := fun r : ℝ => Real.log (L / 2) - Real.log r)
          hh h3 htd hf hfb_ref hBnn hBint
        rw [integral_log_sub_zero_to L (3 / 2 * h)] at this
        have hlog := log_sub_log_le hL hh h3
        nlinarith [mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ 3 * h)]
      · have hhL : h ≤ L := by linarith
        have := integral_window_sub_le_of_lt (B := fun r : ℝ => Real.log (L / 2) - Real.log r)
          hper hL hhL htd hf hfb_ref hBint
        rw [integral_log_sub_zero_to L (L / 2), sub_self, add_zero, mul_one] at this
        have hLh : L ≤ 3 * h := by linarith
        nlinarith
    refine ⟨(∫ y, f y * deriv (scaledMollifier ρ h) (x - y)),
      hasDerivAt_mollifyLine hρ hh hf x, ?_⟩
    rw [hxt]
    have hmax : max (circDist L x) h = h := max_eq_right hx
    rw [hmax]
    have hφc : Continuous (deriv (scaledMollifier ρ h)) :=
      (contDiff_scaledMollifier hρ).continuous_deriv (by simp)
    have hD := norm_integral_mul_le_window (g := fun y => f y - f (L / 2))
      (φ := deriv (scaledMollifier ρ h)) (x := t) (r := h / 2) (K := M1' * (h⁻¹ * h⁻¹))
      (hf.sub (locallyIntegrable_const (f (L / 2)))) hφc (abs_deriv_scaledMollifier_le hρ hh hM1'')
      (fun u hu => deriv_scaledMollifier_eq_zero hρ hh hu)
    rw [integral_mul_sub_const_deriv ρ hρ hh (f (L / 2)) hf]
    have hinv : 0 ≤ h⁻¹ * h⁻¹ := mul_nonneg (inv_nonneg.2 hh.le) (inv_nonneg.2 hh.le)
    refine le_trans hD ?_
    refine le_trans (mul_le_mul_of_nonneg_left hW (mul_nonneg hM1'pos.le hinv)) ?_
    rw [Real.rpow_neg_one]
    have hid : M1' * (h⁻¹ * h⁻¹) * (12 * h * (1 + Real.log (L / h))) =
        12 * M1' * (1 + Real.log (L / h)) * h⁻¹ := by
      field_simp
    rw [hid]
    have hpos : 0 ≤ (1 + Real.log (L / h)) * h⁻¹ := mul_nonneg (by linarith) (inv_nonneg.2 hh.le)
    nlinarith

end LogDerivative

section Tail

/-- One-sided estimate on `[a, b]` with a general integrable majorant `φ` of `|F'|`. -/
lemma abs_sub_le_integral_of_bound {F φ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hd : ∀ r, 0 < r → r ≤ b → DifferentiableAt ℝ F r)
    (hF' : ∀ r, a < r → r ≤ b → |deriv F r| ≤ φ r) (hφ : ContinuousOn φ (Icc a b)) :
    |F b - F a| ≤ ∫ r in a..b, φ r := by
  have hcont : ContinuousOn F (Icc a b) := fun r hr =>
    (hd r (lt_of_lt_of_le ha hr.1) hr.2).continuousAt.continuousWithinAt
  have hderiv : ∀ r ∈ Ioo a b, HasDerivAt F (deriv F r) r := fun r hr =>
    (hd r (ha.trans hr.1) hr.2.le).hasDerivAt
  have hφi : IntervalIntegrable φ volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hφ
  have hle : ∀ᵐ r ∂(volume.restrict (uIoc a b)), ‖deriv F r‖ ≤ ‖φ r‖ := by
    rw [uIoc_of_le hab]
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hF' r hr.1 hr.2).trans (le_abs_self _)
  have hint : IntervalIntegrable (deriv F) volume a b :=
    hφi.mono_fun (measurable_deriv F).aestronglyMeasurable.restrict hle
  have hFTC := integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint
  rw [← hFTC]
  have hb : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioc a b → ‖deriv F r‖ ≤ φ r :=
    Filter.Eventually.of_forall fun r hr => by
      rw [Real.norm_eq_abs]
      exact hF' r hr.1 hr.2
  have := intervalIntegral.norm_integral_le_of_norm_le hab hb hφi
  simpa [Real.norm_eq_abs] using this

/-- The tail integral `∫_a^b r^(s-3) dr ≤ 1/(2-s)` for `1 ≤ a ≤ b` and `s < 1`. -/
lemma integral_rpow_tail_le {s a b : ℝ} (hs : s < 1) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ r in a..b, r ^ (s - 3) ≤ 1 / (2 - s) := by
  have hb0 : 0 < b := by linarith
  have hne : (s - 3) ≠ -1 := fun h => by linarith
  have h0 : (0 : ℝ) ∉ uIcc a b := fun h0 => by
    rw [uIcc_of_le hab] at h0
    linarith [h0.1]
  rw [integral_rpow (Or.inr ⟨hne, h0⟩)]
  have e : s - 3 + 1 = s - 2 := by ring
  rw [e]
  have hA : a ^ (s - 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha (by linarith)
  have hB : 0 ≤ b ^ (s - 2) := Real.rpow_nonneg hb0.le _
  have hid : (b ^ (s - 2) - a ^ (s - 2)) / (s - 2) = (a ^ (s - 2) - b ^ (s - 2)) / (2 - s) := by
    rw [show s - 2 = -(2 - s) by ring, div_neg, ← neg_div, neg_sub]
  rw [hid]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- The pointwise bound `|log r| ≤ -log r + 1` for `0 ≤ r ≤ 3/2`. -/
lemma abs_log_le_neg_log_add_one {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 3 / 2) :
    |Real.log r| ≤ -Real.log r + 1 := by
  rcases hr0.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp
  · rcases le_total r 1 with h1 | h1
    · rw [abs_of_nonpos (Real.log_nonpos hpos.le h1)]
      linarith
    · rw [abs_of_nonneg (Real.log_nonneg h1)]
      have := Real.log_le_sub_one_of_pos hpos
      linarith

/-- `∫_0^a |log r| dr ≤ 2 a (1 + |log a|)` for `0 < a ≤ 3/2`. -/
lemma integral_abs_log_le {a : ℝ} (ha : 0 < a) (ha' : a ≤ 3 / 2) :
    ∫ r in (0 : ℝ)..a, |Real.log r| ≤ 2 * a * (1 + |Real.log a|) := by
  have hmono : ∫ r in (0 : ℝ)..a, |Real.log r| ≤ ∫ r in (0 : ℝ)..a, (-Real.log r + 1) := by
    refine intervalIntegral.integral_mono_on ha.le intervalIntegrable_log'.abs
      ((intervalIntegrable_log'.neg).add intervalIntegrable_const) fun r hr => ?_
    exact abs_log_le_neg_log_add_one hr.1 (hr.2.trans ha')
  have hn : IntervalIntegrable (fun r : ℝ => -Real.log r) volume 0 a :=
    intervalIntegrable_log'.neg
  have hval : ∫ r in (0 : ℝ)..a, (-Real.log r + 1) = 2 * a - a * Real.log a := by
    rw [intervalIntegral.integral_add hn intervalIntegrable_const,
      intervalIntegral.integral_neg, integral_log, intervalIntegral.integral_const]
    simp only [Real.log_zero, mul_zero, sub_zero, smul_eq_mul, mul_one]
    ring
  rw [hval] at hmono
  have hl : -(a * Real.log a) ≤ a * |Real.log a| := by
    have : -Real.log a ≤ |Real.log a| := neg_le_abs _
    nlinarith
  have hpos : 0 ≤ a * |Real.log a| := mul_nonneg ha.le (abs_nonneg _)
  have e : 2 * a * (1 + |Real.log a|) = 2 * a + 2 * (a * |Real.log a|) := by ring
  rw [e]
  linarith

end Tail

section TailEstimates

/-- One-sided tail estimate: for `0 < x ≤ b`, `|F(b) - F(x)| ≤ 1/(2-s) + |log x|`, under the
derivative bounds `|F'(r)| ≤ r^(-1)` for `r ≤ 1` and `|F'(r)| ≤ r^(s-3)` for `r ≥ 1`. -/
lemma abs_sub_le_tail {F : ℝ → ℝ} {s b x : ℝ} (hs : s < 1) (hx : 0 < x) (hxb : x ≤ b)
    (hd : ∀ r, 0 < r → r ≤ b → DifferentiableAt ℝ F r)
    (h1 : ∀ r, 0 < r → r ≤ 1 → r ≤ b → |deriv F r| ≤ r ^ (-1 : ℝ))
    (h2 : ∀ r, 1 ≤ r → r ≤ b → |deriv F r| ≤ r ^ (s - 3)) :
    |F b - F x| ≤ 1 / (2 - s) + |Real.log x| := by
  have hb0 : 0 < b := hx.trans_le hxb
  have hinv : (fun r : ℝ => r ^ (-1 : ℝ)) = fun r => r⁻¹ :=
    funext fun r => Real.rpow_neg_one r
  have hc : 0 < 1 / (2 - s) := by
    have : 0 < 2 - s := by linarith
    positivity
  rcases lt_or_ge b 1 with hb1 | hb1
  · -- Everything lies below `1`: the integrand is `r⁻¹`.
    have key := abs_sub_le_integral_of_bound (φ := fun r : ℝ => r ^ (-1 : ℝ)) hx hxb hd
      (fun r hr1 hr2 => h1 r (hx.trans hr1) (by linarith) hr2)
      (ContinuousOn.rpow_const continuousOn_id fun r hr => Or.inl (by
        exact (hx.trans_le hr.1).ne'))
    rw [hinv, integral_inv_of_pos hx hb0, Real.log_div hb0.ne' hx.ne'] at key
    have hlb : Real.log b ≤ 0 := Real.log_nonpos hb0.le (by linarith)
    have := neg_le_abs (Real.log x)
    linarith
  · rcases le_total x 1 with hx1 | hx1
    · -- Split at `1`.
      have hA := abs_sub_le_integral_of_bound (φ := fun r : ℝ => r ^ (-1 : ℝ))
        (a := x) (b := 1) hx hx1 (fun r hr0 hr1 => hd r hr0 (hr1.trans hb1))
        (fun r hr1 hr2 => h1 r (hx.trans hr1) hr2 (hr2.trans hb1))
        (ContinuousOn.rpow_const continuousOn_id fun r hr => Or.inl (by
          exact (hx.trans_le hr.1).ne'))
      rw [hinv, integral_inv_of_pos hx one_pos, Real.log_div one_ne_zero hx.ne',
        Real.log_one, zero_sub] at hA
      have hB := abs_sub_le_integral_of_bound (φ := fun r : ℝ => r ^ (s - 3))
        (a := 1) (b := b) one_pos hb1 (fun r hr0 hr1 => hd r hr0 hr1)
        (fun r hr1 hr2 => h2 r hr1.le hr2)
        (ContinuousOn.rpow_const continuousOn_id fun r hr => Or.inl (by
          exact (lt_of_lt_of_le one_pos hr.1).ne'))
      have hT := integral_rpow_tail_le hs le_rfl hb1
      have htri := abs_sub_le (F b) (F 1) (F x)
      have hB' : |F b - F 1| ≤ 1 / (2 - s) := hB.trans hT
      linarith [neg_le_abs (Real.log x)]
    · -- Everything lies above `1`: the integrand is `r^(s-3)`.
      have key := abs_sub_le_integral_of_bound (φ := fun r : ℝ => r ^ (s - 3)) (a := x) (b := b)
        hx hxb hd (fun r hr1 hr2 => h2 r (hx1.trans hr1.le) hr2)
        (ContinuousOn.rpow_const continuousOn_id fun r hr => Or.inl (by
          exact (hx.trans_le hr.1).ne'))
      have hT := integral_rpow_tail_le hs hx1 hxb
      have := abs_nonneg (Real.log x)
      linarith

/-- The pointwise tail bound on the circle, for the positive side and the reflected negative side:
`|f(y) - f(L/2)| ≤ 1/(2-s) + |log|y||` for `0 < |y| ≤ L/2`. -/
lemma abs_sub_ref_tail_le {f : ℝ → ℝ} {s L : ℝ} (hs : s < 1) (hper : Function.Periodic f L)
    (hL : 0 < L) (hdf : ∀ y, circDist L y ≠ 0 → DifferentiableAt ℝ f y)
    (hfd : ∀ y, circDist L y ≠ 0 → |deriv f y| ≤ circDist L y ^ (-1 : ℝ))
    (htail : ∀ y, 1 ≤ circDist L y → |deriv f y| ≤ circDist L y ^ (s - 3))
    {y : ℝ} (hy0 : y ≠ 0) (hyL : |y| ≤ L / 2) :
    |f y - f (L / 2)| ≤ 1 / (2 - s) + |Real.log (|y|)| := by
  have hcirc : ∀ r, 0 < r → r ≤ L / 2 → circDist L r = r := fun r hr0 hrL => by
    rw [circDist_eq_abs hL (by rw [abs_of_pos hr0]; exact hrL), abs_of_pos hr0]
  have hcirc' : ∀ r, 0 < r → r ≤ L / 2 → circDist L (-r) = r := fun r hr0 hrL => by
    rw [circDist_eq_abs hL (by rw [abs_neg, abs_of_pos hr0]; exact hrL), abs_neg,
      abs_of_pos hr0]
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · -- Negative side: reflect `f`.
    have hyabs : |y| = -y := abs_of_neg hneg
    have hsL : -y ≤ L / 2 := by
      rw [hyabs] at hyL
      linarith
    have hpL : f (-(L / 2)) = f (L / 2) := by
      have := hper (-(L / 2))
      rw [show -(L / 2) + L = L / 2 by ring] at this
      exact this.symm
    have hd : ∀ r, 0 < r → r ≤ L / 2 → DifferentiableAt ℝ (fun r => f (-r)) r := by
      intro r hr0 hrL
      exact ((hdf (-r) (by rw [hcirc' r hr0 hrL]; exact hr0.ne')).comp r
        differentiableAt_id.neg)
    have key := abs_sub_le_tail (F := fun r => f (-r)) (s := s) (b := L / 2) (x := -y) hs
      (by linarith) hsL hd
      (fun r hr0 hr1 hrL => by
        rw [deriv_comp_neg, abs_neg]
        have := hfd (-r) (by rw [hcirc' r hr0 hrL]; exact hr0.ne')
        rw [hcirc' r hr0 hrL] at this
        exact this)
      (fun r hr1 hrL => by
        rw [deriv_comp_neg, abs_neg]
        have := htail (-r) (by rw [hcirc' r (by linarith) hrL]; exact hr1)
        rw [hcirc' r (by linarith) hrL] at this
        exact this)
    simp only [neg_neg] at key
    rw [hpL] at key
    rw [hyabs, abs_sub_comm]
    exact key
  · -- Positive side.
    have hsL : y ≤ L / 2 := by
      rw [abs_of_pos hpos] at hyL
      exact hyL
    have hd : ∀ r, 0 < r → r ≤ L / 2 → DifferentiableAt ℝ f r := fun r hr0 hrL =>
      hdf r (by rw [hcirc r hr0 hrL]; exact hr0.ne')
    have key := abs_sub_le_tail (F := f) (s := s) (b := L / 2) (x := y) hs hpos hsL hd
      (fun r hr0 hr1 hrL => by
        have := hfd r (by rw [hcirc r hr0 hrL]; exact hr0.ne')
        rw [hcirc r hr0 hrL] at this
        exact this)
      (fun r hr1 hrL => by
        have := htail r (by rw [hcirc r (by linarith) hrL]; exact hr1)
        rw [hcirc r (by linarith) hrL] at this
        exact this)
    rw [abs_sub_comm, abs_of_pos hpos]
    exact key

end TailEstimates

section TailDerivative

/-- `|log a| ≤ 1` for `1/2 ≤ a ≤ 3/2`. -/
lemma abs_log_le_one_of_mem {a : ℝ} (h1 : 1 / 2 ≤ a) (h2 : a ≤ 3 / 2) : |Real.log a| ≤ 1 := by
  have ha : 0 < a := by linarith
  have hup := Real.log_le_sub_one_of_pos ha
  have hlow := Real.one_sub_inv_le_log_of_pos ha
  have hinv : a⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ ha]
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- The window integral of `c + |log r|` over `[0, a]`. -/
lemma integral_const_add_abs_log_le {c a : ℝ} :
    ∫ r in (0 : ℝ)..a, (c + |Real.log r|) = c * a + ∫ r in (0 : ℝ)..a, |Real.log r| := by
  rw [intervalIntegral.integral_add intervalIntegrable_const intervalIntegrable_log'.abs,
    intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]

/-- The circle derivative estimate with the tail hypothesis: the logarithm can be replaced by
`|log h|`. -/
theorem circleMollify_deriv_bound_log_tail (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (s : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ f : ℝ → ℝ, Function.Periodic f L →
      LocallyIntegrable f volume →
      (∀ y : ℝ, circDist L y ≠ 0 → DifferentiableAt ℝ f y) →
      (∀ y : ℝ, circDist L y ≠ 0 → |deriv f y| ≤ circDist L y ^ (-1 : ℝ)) →
      (∀ y : ℝ, 1 ≤ circDist L y → |deriv f y| ≤ circDist L y ^ (s - 3)) →
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ, ∃ D : ℝ,
        HasDerivAt (circleMollify ρ L h f) D x ∧
          |D| ≤ C * (1 + |Real.log h|) * (max (circDist L x) h) ^ (-1 : ℝ) := by
  obtain ⟨M1, hM1_0, hM1⟩ := hρ.exists_bound_deriv
  set M1' := M1 + 1 with hM1'
  have hM1'pos : 0 < M1' := by linarith
  have hM1'' : ∀ z, |deriv ρ z| ≤ M1' := fun z => (hM1 z).trans (by linarith)
  have hc0 : 0 ≤ 1 / (2 - s) := by
    have : 0 < 2 - s := by linarith
    positivity
  have hK0 : 0 ≤ 12 * (1 / (2 - s) + 4) := by linarith
  refine ⟨M1' * (12 * (1 / (2 - s) + 4)) + 2, by nlinarith [mul_nonneg hM1'pos.le hK0], ?_⟩
  intro L hL1 f hper hf hdf hfd htail h hh hh1 x
  have hL : 0 < L := by linarith
  have hfun : circleMollify ρ L h f = mollifyLine ρ h f :=
    funext (circleMollify_eq_mollifyLine hρ hL hh hf hper)
  rw [hfun]
  have hlog0 : 0 ≤ |Real.log h| := abs_nonneg _
  have hfd' : ∀ y : ℝ, circDist L y ≠ 0 → |deriv f y| ≤ circDist L y ^ (-1 - (0 : ℝ)) := by
    intro y hy
    rw [sub_zero]
    exact hfd y hy
  rcases le_total h (circDist L x) with hx | hx
  · -- Far from the singularity.
    have hdiff := hasDerivAt_mollifyLine_far_gen (δ := circDist L) (f := f)
      (circDist_le_add_abs hL) (le_refl (0 : ℝ)) hρ hh hf hdf hfd' hx
    refine ⟨_, hdiff, ?_⟩
    have hb := abs_integral_deriv_far_le_gen (δ := circDist L) (f := f)
      (circDist_le_add_abs hL) (le_refl (0 : ℝ)) hρ hh hfd' hx
    have hmax : max (circDist L x) h = circDist L x := max_eq_left hx
    rw [hmax]
    have hd0 : 0 ≤ circDist L x := circDist_nonneg L x
    have hinv : 0 ≤ circDist L x ^ (-1 : ℝ) := Real.rpow_nonneg hd0 _
    have hval : (circDist L x / 2) ^ (-1 - (0 : ℝ)) = circDist L x ^ (-1 : ℝ) * 2 := by
      rw [show (-1 - (0 : ℝ)) = -(1 : ℝ) by norm_num, div_two_rpow_neg hd0, Real.rpow_one]
    rw [hval] at hb
    have h1 : 2 ≤ (M1' * (12 * (1 / (2 - s) + 4)) + 2) * (1 + |Real.log h|) := by
      nlinarith [mul_nonneg hM1'pos.le hK0]
    calc |∫ u, deriv f (x - u) * scaledMollifier ρ h u|
        ≤ circDist L x ^ (-1 : ℝ) * 2 := hb
      _ ≤ (M1' * (12 * (1 / (2 - s) + 4)) + 2) * (1 + |Real.log h|) * circDist L x ^ (-1 : ℝ) := by
          nlinarith [mul_le_mul_of_nonneg_right h1 hinv]
  · -- Near the singularity.
    set t := x - L * (round (x / L) : ℝ) with ht_def
    have hxt : ∫ y, f y * deriv (scaledMollifier ρ h) (x - y) =
        ∫ y, f y * deriv (scaledMollifier ρ h) (t - y) := by
      have := integral_mul_shift_int hper (deriv (scaledMollifier ρ h)) t (round (x / L))
      have e : t + (round (x / L) : ℝ) * L = x := by rw [ht_def]; ring
      rw [e] at this
      exact this
    have htd : |t| ≤ h := by
      have : |t| = circDist L x := rfl
      rw [this]
      exact hx
    have hfb_ref : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Icc (-(L / 2)) (L / 2) →
        |f y - f (L / 2)| ≤ (fun r : ℝ => 1 / (2 - s) + |Real.log r|) |y| := by
      filter_upwards [ae_ne_zero_volume] with y hy0 hI
      exact abs_sub_ref_tail_le hs1 hper hL hdf hfd htail hy0 (abs_le.2 hI)
    have hBnn : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Icc (-(L / 2)) (L / 2) →
        0 ≤ (fun r : ℝ => 1 / (2 - s) + |Real.log r|) |y| :=
      Filter.Eventually.of_forall fun y _ => add_nonneg hc0 (abs_nonneg _)
    have hBint : IntegrableOn (fun y : ℝ => (fun r : ℝ => 1 / (2 - s) + |Real.log r|) |y|)
        (Icc (-(L / 2)) (L / 2)) :=
      (integrableOn_const (by simp)).add ((integrableOn_abs_log (by linarith)).abs)
    have hW : ∫ y in Ioo (t - h / 2) (t + h / 2), |f y - f (L / 2)| ≤
        12 * (1 / (2 - s) + 4) * h * (1 + |Real.log h|) := by
      by_cases h3 : 3 * h ≤ L
      · have := integral_window_sub_le_of_le
          (B := fun r : ℝ => 1 / (2 - s) + |Real.log r|) hh h3 htd hf hfb_ref hBnn hBint
        have hI := integral_const_add_abs_log_le (c := 1 / (2 - s)) (a := 3 / 2 * h)
        have hlogb : |Real.log (3 / 2 * h)| ≤ |Real.log h| + 1 := by
          rw [Real.log_mul (by norm_num) hh.ne']
          have h32 : |Real.log (3 / 2)| ≤ 1 := abs_log_le_one_of_mem (by norm_num) le_rfl
          linarith [abs_add_le (Real.log (3 / 2)) (Real.log h)]
        have hA := integral_abs_log_le (a := 3 / 2 * h) (by positivity) (by linarith)
        nlinarith [mul_nonneg hh.le (abs_nonneg (Real.log h)), mul_nonneg hh.le hc0,
          mul_nonneg (mul_nonneg hh.le hc0) (abs_nonneg (Real.log h)),
          mul_le_mul_of_nonneg_left hlogb hh.le]
      · have hhL : h ≤ L := by linarith
        have hLh : L < 3 * h := lt_of_not_ge h3
        have := integral_window_sub_le_of_lt
          (B := fun r : ℝ => 1 / (2 - s) + |Real.log r|) hper hL hhL htd hf hfb_ref hBint
        have hI := integral_const_add_abs_log_le (c := 1 / (2 - s)) (a := L / 2)
        have hlogL := abs_log_le_one_of_mem (a := L / 2) (by linarith) (by linarith)
        have hA := integral_abs_log_le (a := L / 2) (by linarith) (by linarith)
        nlinarith [mul_nonneg hh.le hc0, mul_le_mul_of_nonneg_left hLh.le hc0,
          mul_nonneg (mul_nonneg hh.le (by linarith : (0 : ℝ) ≤ 4)) (abs_nonneg (Real.log h)),
          mul_nonneg (mul_nonneg hh.le hc0) (abs_nonneg (Real.log h)),
          mul_le_mul_of_nonneg_left hlogL (by linarith : (0 : ℝ) ≤ L / 2)]
    refine ⟨(∫ y, f y * deriv (scaledMollifier ρ h) (x - y)),
      hasDerivAt_mollifyLine hρ hh hf x, ?_⟩
    rw [hxt]
    have hmax : max (circDist L x) h = h := max_eq_right hx
    rw [hmax]
    have hφc : Continuous (deriv (scaledMollifier ρ h)) :=
      (contDiff_scaledMollifier hρ).continuous_deriv (by simp)
    have hD := norm_integral_mul_le_window (g := fun y => f y - f (L / 2))
      (φ := deriv (scaledMollifier ρ h)) (x := t) (r := h / 2) (K := M1' * (h⁻¹ * h⁻¹))
      (hf.sub (locallyIntegrable_const (f (L / 2)))) hφc
      (abs_deriv_scaledMollifier_le hρ hh hM1'')
      (fun u hu => deriv_scaledMollifier_eq_zero hρ hh hu)
    rw [integral_mul_sub_const_deriv ρ hρ hh (f (L / 2)) hf]
    have hinv : 0 ≤ h⁻¹ * h⁻¹ := mul_nonneg (inv_nonneg.2 hh.le) (inv_nonneg.2 hh.le)
    refine le_trans hD ?_
    refine le_trans (mul_le_mul_of_nonneg_left hW (mul_nonneg hM1'pos.le hinv)) ?_
    rw [Real.rpow_neg_one]
    have hh' : h⁻¹ * h⁻¹ * h = h⁻¹ := by field_simp
    have hid : M1' * (h⁻¹ * h⁻¹) * (12 * (1 / (2 - s) + 4) * h * (1 + |Real.log h|)) =
        M1' * (12 * (1 / (2 - s) + 4)) * (1 + |Real.log h|) * h⁻¹ := by
      linear_combination (M1' * (12 * (1 / (2 - s) + 4)) * (1 + |Real.log h|)) * hh'
    rw [hid]
    have hq : 0 ≤ 2 * ((1 + |Real.log h|) * h⁻¹) :=
      mul_nonneg (by norm_num) (mul_nonneg (by linarith) (inv_nonneg.2 hh.le))
    have e : (M1' * (12 * (1 / (2 - s) + 4)) + 2) * (1 + |Real.log h|) * h⁻¹ =
        M1' * (12 * (1 / (2 - s) + 4)) * (1 + |Real.log h|) * h⁻¹ +
          2 * ((1 + |Real.log h|) * h⁻¹) := by ring
    rw [e]
    linarith

end TailDerivative

end Riesz1
