/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.MeanFieldEnergyKernel
public import Mathlib.Tactic

/-!
# Principal-value convolution with the derivative of the Riesz kernel

Proposition 5.5, analytic part. For a smooth
one-periodic `ψ` and `0 < s < 1` the convolution `(g_s' * ψ)(x)` is the symmetric principal value
of `∫ g_s'(x - y) ψ(y) dy`. This file proves that the principal value
exists, gives its absolutely convergent form, and proves the integral identities used by the
force expansion:

* the inner integral `∫ (ψ(x) - ψ(y)) g_s'(x - y) dy = -(g_s' * ψ)(x)` (and the same in the
  other variable),
* the mean `∫ (g_s' * ψ)(x) dx = 0` for mean-zero `ψ`,
* the vanishing of the background-background integral `C_ψ`.

Here `g_s` is the project kernel `hurwitzKernel s`, which is `rieszRepresentative s` on the
circle. Circle integrals are written as integrals over `[0, 1]`
of one-periodic real functions.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-! ### Elementary facts about the kernel and the circle -/

/-- The derivative of the kernel is odd. -/
lemma deriv_hurwitzKernel_neg' (s : ℝ) (x : ℝ) :
    deriv (hurwitzKernel s) (-x) = -deriv (hurwitzKernel s) x :=
  deriv_neg_of_even (hurwitzKernel_neg s) x

/-- The derivative of the kernel is one-periodic. -/
lemma deriv_hurwitzKernel_add_one' (s : ℝ) (x : ℝ) :
    deriv (hurwitzKernel s) (x + 1) = deriv (hurwitzKernel s) x :=
  deriv_add_one_of_periodic (hurwitzKernel_add_one s) x

/-- The kernel has a continuous derivative at every point off the integers. -/
lemma continuousAt_deriv_hurwitzKernel {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {u : ℝ}
    (hu : (u : UnitAddCircle) ≠ 0) : ContinuousAt (deriv (hurwitzKernel s)) u :=
  (hasDerivAt_deriv_hurwitzKernel_of_ne s hs0 hs1 u hu).continuousAt

/-- For `0 < u < 1` the distance from `u` to the nearest integer is `min u (1 - u)`. -/
lemma dist_coe_eq_min {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    dist (u : UnitAddCircle) 0 = min u (1 - u) := by
  rw [dist_coe_zero_eq]
  rcases lt_or_ge u (1 / 2) with h | h
  · have hr : round u = 0 := by
      rw [round_eq, Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    rw [hr, Int.cast_zero, sub_zero, abs_of_pos h0, min_eq_left (by linarith)]
  · have hr : round u = 1 := by
      rw [round_eq, Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    rw [hr, Int.cast_one, abs_of_nonpos (by linarith), min_eq_right (by linarith)]
    ring

/-- The majorant `dist(u, ℤ)^(-s) ≤ u^(-s) + (1 - u)^(-s)` on `(0, 1)`. -/
lemma dist_rpow_le_majorant {s : ℝ} {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    dist (u : UnitAddCircle) 0 ^ (-s) ≤ u ^ (-s) + (1 - u) ^ (-s) := by
  rw [dist_coe_eq_min h0 h1]
  rcases le_total u (1 - u) with h | h
  · rw [min_eq_left h]
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ 1 - u by linarith) (-s)
    linarith
  · rw [min_eq_right h]
    have := Real.rpow_nonneg h0.le (-s)
    linarith

/-- A smooth one-periodic function is Lipschitz with respect to the circle distance. -/
lemma exists_abs_sub_le_dist {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a t : ℝ, |ψ (a + t) - ψ a| ≤ M * dist (t : UnitAddCircle) 0 := by
  have hd : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hper : Function.Periodic (deriv ψ) 1 := deriv_add_one_of_periodic hp
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hd.continuousOn
  have hbd : ∀ x, |deriv ψ x| ≤ C := by
    intro x
    have hfr : Int.fract x ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
    have hx : deriv ψ (Int.fract x) = deriv ψ x := by
      have h1 := hper.sub_int_mul_eq (x := x) ⌊x⌋
      rw [mul_one] at h1
      exact h1
    have := hC _ hfr
    rw [hx, Real.norm_eq_abs] at this
    exact this
  refine ⟨|C|, abs_nonneg C, fun a t => ?_⟩
  have hn : ψ (a + t) = ψ (a + (t - round t)) := by
    have h := (hp.int_mul (round t)) (a + (t - round t))
    rw [show a + (t - round t) + (round t : ℝ) * 1 = a + t by ring] at h
    exact h
  rw [hn, dist_coe_zero_eq]
  have hmean := (convex_univ).norm_image_sub_le_of_norm_deriv_le (f := ψ)
    (fun y _ => (hψ.differentiable (by simp)) y) (fun y _ => by
      rw [Real.norm_eq_abs]; exact hbd y) (mem_univ a) (mem_univ (a + (t - round t)))
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmean
  have hsub : a + (t - round t) - a = t - round t := by ring
  rw [hsub] at hmean
  exact hmean.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _))

/-! ### The principal-value integrand -/

/-- The integrand `g_s'(u) (ψ(x - u) - ψ(x))` of the absolutely convergent form of the principal
value. -/
noncomputable def pvIntegrand (s : ℝ) (ψ : ℝ → ℝ) (x u : ℝ) : ℝ :=
  deriv (hurwitzKernel s) u * (ψ (x - u) - ψ x)

/-- The integrand is bounded by a constant multiple of the majorant on `(0, 1)`, with a constant
independent of `x`. -/
lemma abs_pvIntegrand_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ 1) :
    ∃ K : ℝ, ∀ x u : ℝ, 0 < u → u < 1 →
      |pvIntegrand s ψ x u| ≤ K * (u ^ (-s) + (1 - u) ^ (-s)) := by
  obtain ⟨C, hC, hgb⟩ := deriv_hurwitzKernel_bound s hs0 hs1
  obtain ⟨M, hM0, hM⟩ := exists_abs_sub_le_dist hψ hp
  refine ⟨C * M, fun x u h0 h1 => ?_⟩
  have hne : (u : UnitAddCircle) ≠ 0 := coe_ne_zero_of_mem_Ioo01 h0 h1
  have hdpos : 0 < dist (u : UnitAddCircle) 0 := dist_pos.mpr hne
  set d := dist (u : UnitAddCircle) 0 with hd
  have hdneg : dist ((-u : ℝ) : UnitAddCircle) 0 = d := by
    rw [AddCircle.coe_neg, dist_zero_right, norm_neg, hd, dist_zero_right]
  have hpsi : |ψ (x - u) - ψ x| ≤ M * d := by
    have h := hM x (-u)
    rw [hdneg, ← sub_eq_add_neg] at h
    exact h
  have hgd : |deriv (hurwitzKernel s) u| ≤ C * d ^ (-s - 1) := hgb u hne
  have hprod : |pvIntegrand s ψ x u| ≤ C * d ^ (-s - 1) * (M * d) := by
    unfold pvIntegrand
    rw [abs_mul]
    exact mul_le_mul hgd hpsi (abs_nonneg _) (by positivity)
  have hpow : d ^ (-s - 1) * d = d ^ (-s) := by
    rw [Real.rpow_sub_one hdpos.ne', div_mul_cancel₀ _ hdpos.ne']
  have hmaj : d ^ (-s) ≤ u ^ (-s) + (1 - u) ^ (-s) := dist_rpow_le_majorant (s := s) h0 h1
  calc |pvIntegrand s ψ x u| ≤ C * d ^ (-s - 1) * (M * d) := hprod
    _ = (C * M) * (d ^ (-s - 1) * d) := by ring
    _ = (C * M) * d ^ (-s) := by rw [hpow]
    _ ≤ (C * M) * (u ^ (-s) + (1 - u) ^ (-s)) :=
      mul_le_mul_of_nonneg_left hmaj (mul_nonneg hC.le hM0)

lemma measurable_pvIntegrand (s : ℝ) {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    Measurable fun p : ℝ × ℝ => pvIntegrand s ψ p.1 p.2 := by
  unfold pvIntegrand
  exact ((measurable_deriv _).comp measurable_snd).mul
    ((hψ.measurable.comp (measurable_fst.sub measurable_snd)).sub
      (hψ.measurable.comp measurable_fst))

/-- For fixed `x`, the integrand is integrable on `(0, 1)`. -/
lemma integrableOn_pvIntegrand {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ 1) (x : ℝ) :
    IntegrableOn (pvIntegrand s ψ x) (Ioo 0 1) := by
  obtain ⟨K, hK⟩ := abs_pvIntegrand_le hs0 hs1 hψ hp
  have hmeas : Measurable fun u : ℝ => pvIntegrand s ψ x u :=
    (measurable_pvIntegrand s hψ.continuous).comp measurable_prodMk_left
  refine Integrable.mono' ((integrableOn_rpow_majorant hs1).const_mul K)
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  rw [Real.norm_eq_abs]
  exact hK x u hu.1 hu.2

/-- The integrand is continuous in `u` on `(0, 1)`. -/
lemma continuousOn_pvIntegrand {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : Continuous ψ) (x : ℝ) : ContinuousOn (pvIntegrand s ψ x) (Ioo 0 1) := by
  intro u hu
  have hne : (u : UnitAddCircle) ≠ 0 := coe_ne_zero_of_mem_Ioo01 hu.1 hu.2
  have h2 : ContinuousAt (fun v => ψ (x - v) - ψ x) u :=
    ((hψ.comp (continuous_const.sub continuous_id)).sub continuous_const).continuousAt
  exact ((continuousAt_deriv_hurwitzKernel hs0 hs1 hne).mul h2).continuousWithinAt

/-! ### The symmetric principal value -/

/-- The symmetric principal value `(g_s' * ψ)(x)`: the limit of the integrals over `[h, 1 - h]`,
which delete the points `u` with `dist (u : UnitAddCircle) 0 ≤ h`. The
limit exists by `tendsto_truncated_pv`, so `pvConv` is its value. -/
noncomputable def pvConv (s : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun h : ℝ => ∫ u in h..(1 - h), deriv (hurwitzKernel s) u * ψ (x - u)

/-- The truncated integrals converge to the absolutely convergent form of the principal value. -/
lemma tendsto_truncated_pv {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ 1) (x : ℝ) :
    Tendsto (fun h : ℝ => ∫ u in h..(1 - h), deriv (hurwitzKernel s) u * ψ (x - u)) (𝓝[>] 0)
      (𝓝 (∫ u in (0 : ℝ)..1, pvIntegrand s ψ x u)) := by
  have hψc : Continuous ψ := hψ.continuous
  have hmem01 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t ∈ uIcc (0 : ℝ) 1 := fun t h0 h1 => by
    rw [uIcc_of_le zero_le_one]
    exact ⟨h0, h1⟩
  have hFi : IntervalIntegrable (pvIntegrand s ψ x) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    exact integrableOn_pvIntegrand hs0 hs1 hψ hp x
  have hIcc : IntegrableOn (pvIntegrand s ψ x) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hFi
  have hΦc : ContinuousOn (fun t => ∫ u in (0 : ℝ)..t, pvIntegrand s ψ x u) (uIcc 0 1) :=
    intervalIntegral.continuousOn_primitive_interval hIcc
  set Φ : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, pvIntegrand s ψ x u with hΦ
  have hsub : ∀ h : ℝ, 0 < h → h < 1 / 2 →
      ∫ u in h..(1 - h), deriv (hurwitzKernel s) u * ψ (x - u) = Φ (1 - h) - Φ h := by
    intro h h0 h1
    have hsplit : ∀ u : ℝ, deriv (hurwitzKernel s) u * ψ (x - u)
        = pvIntegrand s ψ x u + ψ x * deriv (hurwitzKernel s) u := fun u => by
      unfold pvIntegrand; ring
    have hmem : uIcc h (1 - h) ⊆ Ioo 0 1 := by
      intro u hu
      rw [uIcc_of_le (show h ≤ 1 - h by linarith)] at hu
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hFint : IntervalIntegrable (pvIntegrand s ψ x) volume h (1 - h) :=
      hFi.mono_set (uIcc_subset_uIcc (hmem01 h h0.le (by linarith))
        (hmem01 (1 - h) (by linarith) (by linarith)))
    have hgint : IntervalIntegrable (deriv (hurwitzKernel s)) volume h (1 - h) := by
      apply ContinuousOn.intervalIntegrable
      intro u hu
      have hu' := hmem hu
      exact (continuousAt_deriv_hurwitzKernel hs0 hs1
        (coe_ne_zero_of_mem_Ioo01 hu'.1 hu'.2)).continuousWithinAt
    have hzero : ∫ u in h..(1 - h), deriv (hurwitzKernel s) u = 0 := by
      rw [intervalIntegral.integral_deriv_eq_sub]
      · have h1' : hurwitzKernel s (1 - h) = hurwitzKernel s h := by
          rw [show 1 - h = -h + 1 by ring, hurwitzKernel_add_one, hurwitzKernel_neg]
        rw [h1', sub_self]
      · intro u hu
        have hu' := hmem hu
        exact differentiableAt_hurwitzKernel_of_ne s hs0 hs1 u
          (coe_ne_zero_of_mem_Ioo01 hu'.1 hu'.2)
      · exact hgint
    have hcongr : ∫ u in h..(1 - h), deriv (hurwitzKernel s) u * ψ (x - u)
        = ∫ u in h..(1 - h), (pvIntegrand s ψ x u + ψ x * deriv (hurwitzKernel s) u) :=
      intervalIntegral.integral_congr (fun u _ => hsplit u)
    have hA : IntervalIntegrable (pvIntegrand s ψ x) volume 0 (1 - h) :=
      hFi.mono_set (uIcc_subset_uIcc left_mem_uIcc (hmem01 (1 - h) (by linarith) (by linarith)))
    have hB : IntervalIntegrable (pvIntegrand s ψ x) volume 0 h :=
      hFi.mono_set (uIcc_subset_uIcc left_mem_uIcc (hmem01 h h0.le (by linarith)))
    rw [hcongr, intervalIntegral.integral_add hFint (hgint.const_mul _),
      intervalIntegral.integral_const_mul, hzero, mul_zero, add_zero]
    exact (intervalIntegral.integral_interval_sub_left hA hB).symm
  -- The two endpoint limits of `Φ`.
  have hlimΦ1 : Tendsto (fun h : ℝ => Φ (1 - h)) (𝓝[>] 0) (𝓝 (Φ 1)) := by
    have hc : ContinuousWithinAt Φ (uIcc 0 1) 1 := hΦc 1 right_mem_uIcc
    have hmap : Tendsto (fun h : ℝ => 1 - h) (𝓝[>] 0) (𝓝[uIcc 0 1] 1) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h0 : Tendsto (fun h : ℝ => 1 - h) (𝓝 0) (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub tendsto_id
        rw [sub_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hh
        exact hmem01 (1 - h) (by linarith [hh.2]) (by linarith [hh.1])
    exact hc.tendsto.comp hmap
  have hlimΦ0 : Tendsto (fun h : ℝ => Φ h) (𝓝[>] 0) (𝓝 (Φ 0)) := by
    have hc : ContinuousWithinAt Φ (uIcc 0 1) 0 := hΦc 0 left_mem_uIcc
    have hmap : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝[uIcc 0 1] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact tendsto_id.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hh
        exact hmem01 h hh.1.le hh.2.le
    exact hc.tendsto.comp hmap
  have hΦ0 : Φ 0 = 0 := by simp [hΦ]
  have hlim := hlimΦ1.sub hlimΦ0
  rw [hΦ0, sub_zero] at hlim
  refine Tendsto.congr' ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with h hh
  exact (hsub h hh.1 hh.2).symm

/-- The symmetric principal value equals the absolutely convergent integral. -/
lemma pvConv_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ 1) (x : ℝ) :
    pvConv s ψ x = ∫ u in (0 : ℝ)..1, pvIntegrand s ψ x u :=
  (tendsto_truncated_pv hs0 hs1 hψ hp x).limUnder_eq

/-! ### The inner identities -/

/-- The inner integral in the first variable: `∫ (ψ(x) - ψ(y)) g_s'(x - y) dy = -(g_s' * ψ)(x)`.
-/
lemma integral_kernel_mul_sub_right {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ 1) (x : ℝ) :
    ∫ y in (0 : ℝ)..1, (ψ x - ψ y) * deriv (hurwitzKernel s) (x - y)
      = -pvConv s ψ x := by
  rw [pvConv_eq hs0 hs1 hψ hp x]
  set f : ℝ → ℝ := fun u => (ψ x - ψ (x - u)) * deriv (hurwitzKernel s) u with hf
  have hsub : ∀ y : ℝ, (ψ x - ψ y) * deriv (hurwitzKernel s) (x - y) = f (x - y) := by
    intro y
    simp only [hf, sub_sub_cancel]
  simp_rw [hsub]
  rw [intervalIntegral.integral_comp_sub_left f x]
  have hper : Function.Periodic f 1 := by
    intro u
    simp only [hf]
    rw [deriv_hurwitzKernel_add_one', show x - (u + 1) = (x - u) - 1 by ring, hp.sub_eq (x - u)]
  have hshift := hper.intervalIntegral_add_eq (x - 1) 0
  rw [sub_add_cancel, zero_add] at hshift
  rw [sub_zero, hshift, ← intervalIntegral.integral_neg]
  exact intervalIntegral.integral_congr (fun u _ => by simp only [hf, pvIntegrand]; ring)

/-- The inner integral in the second variable: `∫ (ψ(x) - ψ(y)) g_s'(x - y) dx = -(g_s' * ψ)(y)`.
This follows from the first identity since the kernel `(x, y) ↦ (ψ x - ψ y) g_s'(x - y)` is
symmetric. -/
lemma integral_kernel_mul_sub_left {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ 1) (y : ℝ) :
    ∫ x in (0 : ℝ)..1, (ψ x - ψ y) * deriv (hurwitzKernel s) (x - y)
      = -pvConv s ψ y := by
  have hsymm : ∀ x : ℝ, (ψ x - ψ y) * deriv (hurwitzKernel s) (x - y)
      = (ψ y - ψ x) * deriv (hurwitzKernel s) (y - x) := by
    intro x
    have h := deriv_hurwitzKernel_neg' s (x - y)
    rw [show -(x - y) = y - x by ring] at h
    rw [h]
    ring
  simp_rw [hsymm]
  exact integral_kernel_mul_sub_right hs0 hs1 hψ hp y

/-! ### The mean of the principal value -/

/-- The product integrability of the principal-value integrand on `(0, 1)²`. -/
lemma integrable_pvIntegrand_prod {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ 1) :
    Integrable (fun p : ℝ × ℝ => pvIntegrand s ψ p.1 p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  obtain ⟨K, hK⟩ := abs_pvIntegrand_le hs0 hs1 hψ hp
  have hc : Integrable (fun _ : ℝ => K) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    integrableOn_const measure_Ioo_lt_top.ne
  have hbound := hc.mul_prod (integrableOn_rpow_majorant hs1)
  refine Integrable.mono' hbound (measurable_pvIntegrand s hψ.continuous).aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp'
  rw [Real.norm_eq_abs]
  exact hK p.1 p.2 hp'.2.1 hp'.2.2

/-- The periodic translation of the integral of `ψ`: `∫₀¹ ψ(x - u) dx = ∫₀¹ ψ(x) dx`. -/
lemma integral_comp_sub_periodic_one {ψ : ℝ → ℝ} (hp : Function.Periodic ψ 1) (u : ℝ) :
    ∫ x in (0 : ℝ)..1, ψ (x - u) = ∫ x in (0 : ℝ)..1, ψ x := by
  rw [intervalIntegral.integral_comp_sub_right ψ u]
  have h := hp.intervalIntegral_add_eq (-u) 0
  rw [zero_add, show -u + 1 = 1 - u by ring] at h
  rw [zero_sub]
  exact h

/-- The integral of the principal value over a period vanishes: `∫₀¹ (g_s' * ψ)(x) dx = 0`,
for mean-zero `ψ`. -/
lemma integral_pvConv_eq_zero {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ 1) :
    ∫ x in (0 : ℝ)..1, pvConv s ψ x = 0 := by
  have hψc : Continuous ψ := hψ.continuous
  have hinner : ∀ u : ℝ, ∫ x in Ioo (0 : ℝ) 1, pvIntegrand s ψ x u = 0 := by
    intro u
    have h1 : IntervalIntegrable (fun x => ψ (x - u)) volume 0 1 :=
      (hψc.comp (continuous_id.sub continuous_const)).intervalIntegrable 0 1
    have h2 : IntervalIntegrable ψ volume 0 1 := hψc.intervalIntegrable 0 1
    have hper := integral_comp_sub_periodic_one hp u
    have key : ∫ x in (0 : ℝ)..1, pvIntegrand s ψ x u = 0 := by
      have hcongr : ∫ x in (0 : ℝ)..1, pvIntegrand s ψ x u
          = ∫ x in (0 : ℝ)..1, (deriv (hurwitzKernel s) u * ψ (x - u)
              - deriv (hurwitzKernel s) u * ψ x) :=
        intervalIntegral.integral_congr (fun x _ => by unfold pvIntegrand; ring)
      -- The equalities are stated with their own types, so that `rw` matches the instances.
      have e1 : ∫ x in (0 : ℝ)..1, deriv (hurwitzKernel s) u * ψ (x - u)
          = deriv (hurwitzKernel s) u * ∫ x in (0 : ℝ)..1, ψ (x - u) :=
        intervalIntegral.integral_const_mul _ _
      have e2 : ∫ x in (0 : ℝ)..1, deriv (hurwitzKernel s) u * ψ x
          = deriv (hurwitzKernel s) u * ∫ x in (0 : ℝ)..1, ψ x :=
        intervalIntegral.integral_const_mul _ _
      have e3 : ∫ x in (0 : ℝ)..1, (deriv (hurwitzKernel s) u * ψ (x - u)
              - deriv (hurwitzKernel s) u * ψ x)
          = (∫ x in (0 : ℝ)..1, deriv (hurwitzKernel s) u * ψ (x - u))
              - ∫ x in (0 : ℝ)..1, deriv (hurwitzKernel s) u * ψ x :=
        intervalIntegral.integral_sub (h1.const_mul _) (h2.const_mul _)
      rw [hcongr, e3, e1, e2, hper, sub_self]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    exact key
  have hint := integrable_pvIntegrand_prod hs0 hs1 hψ hp
  have hfub := integral_integral_swap (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (ν := volume.restrict (Ioo (0 : ℝ) 1)) (f := fun x u => pvIntegrand s ψ x u) hint
  have hpv : ∀ x : ℝ, pvConv s ψ x = ∫ u in Ioo (0 : ℝ) 1, pvIntegrand s ψ x u := fun x => by
    rw [pvConv_eq hs0 hs1 hψ hp x, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
  have hL : ∫ x in (0 : ℝ)..1, pvConv s ψ x = ∫ x in Ioo (0 : ℝ) 1, ∫ u in Ioo (0 : ℝ) 1,
      pvIntegrand s ψ x u := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    exact integral_congr_ae (Eventually.of_forall hpv)
  rw [hL, hfub]
  simp only [hinner, integral_zero]

/-- The background-background integral vanishes: `∫₀¹ ∫₀¹ (ψ(x) - ψ(y)) g_s'(x - y) dy dx = 0`,
which is `C_ψ = 0` up to the factor `N^(2-s)` (Proposition 5.5). -/
lemma integral_integral_kernel_eq_zero {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ 1) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, (ψ x - ψ y) * deriv (hurwitzKernel s) (x - y) = 0 := by
  simp_rw [integral_kernel_mul_sub_right hs0 hs1 hψ hp]
  rw [intervalIntegral.integral_neg, integral_pvConv_eq_zero hs0 hs1 hψ hp, neg_zero]

/-- The principal value is interval integrable on `[0, 1]`. -/
lemma intervalIntegrable_pvConv {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ 1) :
    IntervalIntegrable (pvConv s ψ) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  have h := (integrable_pvIntegrand_prod hs0 hs1 hψ hp).integral_prod_left
  refine Integrable.congr h (Eventually.of_forall fun x => ?_)
  show ∫ u in Ioo (0 : ℝ) 1, pvIntegrand s ψ x u = pvConv s ψ x
  rw [pvConv_eq hs0 hs1 hψ hp x, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]

end Riesz1

end
