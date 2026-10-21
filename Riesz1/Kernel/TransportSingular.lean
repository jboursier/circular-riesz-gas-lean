/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportPrimitive

/-!
# Integration by parts for the singular kernel of the transport

For `0 < s < 1`, the signed power `u ↦ sgn(u) |u|^{s-1}` has derivative `(s-1)|u|^{s-2}` away
from zero. Pairing it with `Ξ(x) - Ξ(t)` for a periodic `Ξ` with bounded derivative gives an
integration by parts identity on `[0, 1]`, whose only singularity sits at the integer translate
`t = x - n`. The singularity is removable for the product: the factor `Ξ(x) - Ξ(t)` vanishes there
linearly, which makes the boundary term at the singular point vanish.

This file proves the identity `(1 - s) ∫_0^1 (Ξ(x) - Ξ(t)) |x - t - n|^{s-2} dt
= [H]_0^1 + ∫_0^1 Ξ'(t) sgn(x - t - n) |x - t - n|^{s-1} dt` with
`H(t) = (Ξ(x) - Ξ(t)) sgn(x-t-n)|x-t-n|^{s-1}`.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology
open scoped ContDiff Real

namespace Riesz1

/-- The signed power `sgn(u) |u|^{s-1}` vanishes at zero, for `0 < s < 1`. -/
lemma signPow_zero (s : ℝ) : signPow s 0 = 0 := by
  simp [signPow]

/-- The sign function is measurable, as a finite piecewise constant function. -/
lemma measurable_realSign : Measurable Real.sign := by
  unfold Real.sign
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    measurable_const

/-- The modulus of the signed power is the power of the modulus. -/
lemma abs_signPow_le (s u : ℝ) : |signPow s u| ≤ |u| ^ (s - 1) := by
  unfold signPow
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg u) _)]
  have h1 : |Real.sign u| ≤ 1 := by
    rcases lt_trichotomy u 0 with hu | hu | hu
    · rw [Real.sign_of_neg hu]; simp
    · simp [hu]
    · rw [Real.sign_of_pos hu]; simp
  calc |Real.sign u| * |u| ^ (s - 1) ≤ 1 * |u| ^ (s - 1) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (abs_nonneg u) _)
    _ = |u| ^ (s - 1) := one_mul _

/-- Derivative of the signed power away from zero. -/
lemma hasDerivAt_signPow {s u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun v => signPow s v) ((s - 1) * |u| ^ (s - 2)) u := by
  rcases lt_or_gt_of_ne hu with hneg | hpos
  · have hev : (fun v => signPow s v) =ᶠ[𝓝 u] fun v => -((-v) ^ (s - 1)) := by
      filter_upwards [gt_mem_nhds hneg] with v hv using signPow_of_neg hv
    have hneg' : -u ≠ 0 := neg_ne_zero.2 hu
    have h1 : HasDerivAt (fun v : ℝ => (-v) ^ (s - 1)) ((-1) * (s - 1) * (-u) ^ (s - 2)) u := by
      have := HasDerivAt.rpow_const (p := s - 1) (hasDerivAt_neg u) (Or.inl hneg')
      rw [show s - 1 - 1 = s - 2 by ring] at this
      exact this
    have h2 := (h1.neg).congr_of_eventuallyEq hev
    rw [abs_of_neg hneg]
    convert h2 using 1
    ring
  · have hev : (fun v => signPow s v) =ᶠ[𝓝 u] fun v => v ^ (s - 1) := by
      filter_upwards [lt_mem_nhds hpos] with v hv using signPow_of_pos hv
    have h1 : HasDerivAt (fun v : ℝ => v ^ (s - 1)) ((s - 1) * u ^ (s - 2)) u := by
      have := Real.hasDerivAt_rpow_const (x := u) (p := s - 1) (Or.inl hu)
      rw [show s - 1 - 1 = s - 2 by ring] at this
      exact this
    rw [abs_of_pos hpos]
    exact h1.congr_of_eventuallyEq hev

/-- The derivative in `t` of `sgn(x - t - n)|x - t - n|^{s-1}`, away from the singularity. -/
lemma hasDerivAt_signPow_sub {s x c t : ℝ} (hu : x - t - c ≠ 0) :
    HasDerivAt (fun τ => signPow s (x - τ - c)) ((1 - s) * |x - t - c| ^ (s - 2)) t := by
  have hinner : HasDerivAt (fun τ : ℝ => x - τ - c) (-1) t := by
    simpa using ((hasDerivAt_id t).const_sub x).sub_const c
  have h := (hasDerivAt_signPow (s := s) hu).comp t hinner
  refine HasDerivAt.congr_deriv h ?_
  ring

/-- The integrable power `|u|^r` on any interval, for `r > -1`. -/
lemma intervalIntegrable_abs_rpow {r : ℝ} (hr : -1 < r) (A B : ℝ) :
    IntervalIntegrable (fun u : ℝ => |u| ^ r) volume A B := by
  have h0 : ∀ Q : ℝ, IntervalIntegrable (fun u : ℝ => |u| ^ r) volume 0 Q := by
    intro Q
    rcases le_total 0 Q with hQ | hQ
    · refine (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := Q) hr).congr_uIoo ?_
      intro x hx
      rw [uIoo, min_eq_left hQ, max_eq_right hQ] at hx
      simp only [abs_of_pos hx.1]
    · have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := -Q) hr).comp_sub_left 0
      simp only [sub_self, zero_sub, neg_neg] at h
      refine (h.congr_uIoo ?_)
      intro x hx
      rw [uIoo, min_eq_right hQ, max_eq_left hQ] at hx
      simp only [abs_of_neg hx.2]
  exact (h0 A).symm.trans (h0 B)

/-- Integrability of `t ↦ |c - t|^r` on any interval, for `r > -1`. -/
lemma intervalIntegrable_abs_sub_rpow {r : ℝ} (hr : -1 < r) (c a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => |c - t| ^ r) volume a b := by
  have h := (intervalIntegrable_abs_rpow hr (c - a) (c - b)).comp_sub_left c
  rw [sub_sub_cancel, sub_sub_cancel] at h
  exact h

/-- `|u| · |u|^{s-2} = |u|^{s-1}` for `s < 1`. -/
lemma abs_mul_rpow_sub_two {s : ℝ} (hs1 : s < 1) (u : ℝ) :
    |u| * |u| ^ (s - 2) = |u| ^ (s - 1) := by
  have h := Real.rpow_add' (abs_nonneg u) (show (1 : ℝ) + (s - 2) ≠ 0 by intro h; linarith)
  rw [Real.rpow_one] at h
  rw [show (s - 1 : ℝ) = 1 + (s - 2) by ring, h]

/-- `|u| · |u|^{s-1} = |u|^s` for `s > 0`. -/
lemma abs_mul_rpow_sub_one {s : ℝ} (hs0 : 0 < s) (u : ℝ) :
    |u| * |u| ^ (s - 1) = |u| ^ s := by
  have h := Real.rpow_add' (abs_nonneg u) (show (1 : ℝ) + (s - 1) ≠ 0 by intro h; linarith)
  rw [Real.rpow_one, show (1 : ℝ) + (s - 1) = s by ring] at h
  exact h.symm

/-- Splitting the fundamental theorem of calculus at a single point `c` of `[a, b]`, where the
primitive is only differentiable away from `c`. -/
lemma integral_eq_sub_of_hasDerivAt_except {H h : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hc : c ∈ Icc a b) (hcont : ContinuousOn H (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, t ≠ c → HasDerivAt H (h t) t)
    (hint : IntervalIntegrable h volume a b) :
    ∫ t in a..b, h t = H b - H a := by
  obtain ⟨hac, hcb⟩ := hc
  have hac' : IntervalIntegrable h volume a c :=
    hint.mono_set (by rw [uIcc_of_le hac, uIcc_of_le hab]; exact Icc_subset_Icc le_rfl hcb)
  have hcb' : IntervalIntegrable h volume c b :=
    hint.mono_set (by rw [uIcc_of_le hcb, uIcc_of_le hab]; exact Icc_subset_Icc hac le_rfl)
  have h1 : ∫ t in a..c, h t = H c - H a := by
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hac
      (hcont.mono (Icc_subset_Icc le_rfl hcb)) (fun t ht => ?_) hac'
    exact (hderiv t ⟨ht.1, ht.2.trans_le hcb⟩ ht.2.ne).hasDerivWithinAt
  have h2 : ∫ t in c..b, h t = H b - H c := by
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hcb
      (hcont.mono (Icc_subset_Icc hac le_rfl)) (fun t ht => ?_) hcb'
    exact (hderiv t ⟨lt_of_le_of_lt hac ht.1, ht.2⟩ (ne_of_gt ht.1)).hasDerivWithinAt
  rw [← intervalIntegral.integral_add_adjacent_intervals hac' hcb', h1, h2]
  ring

/-- The integration by parts identity for the singular kernel on `[0, 1]`:
`(1 - s) ∫_0^1 (Ξ(x) - Ξ(t)) |x - t - n|^{s-2} dt` equals the boundary term of
`H(t) = (Ξ(x) - Ξ(t)) sgn(x - t - n) |x - t - n|^{s-1}` plus `∫_0^1 Ξ'(t) sgn(x - t - n)|x - t - n|^{s-1} dt`.
The integer shift `n` puts the singularity at `t = x - n`, where the factor `Ξ(x) - Ξ(t)` vanishes. -/
lemma singular_ibp {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {Ξ ξ' : ℝ → ℝ} {M : ℝ}
    (hΞ : ∀ t, HasDerivAt Ξ (ξ' t) t) (hξc : Continuous ξ') (hξM : ∀ t, |ξ' t| ≤ M)
    (hper : Function.Periodic Ξ 1) (x : ℝ) (n : ℤ) :
    (1 - s) * ∫ t in (0 : ℝ)..1, (Ξ x - Ξ t) * |x - t - n| ^ (s - 2)
      = ((Ξ x - Ξ 1) * signPow s (x - 1 - n) - (Ξ x - Ξ 0) * signPow s (x - 0 - n))
        + ∫ t in (0 : ℝ)..1, ξ' t * signPow s (x - t - n) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hξM 0)
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = max 0 (min 1 (x - n)) := ⟨_, rfl⟩
  have hc : c ∈ Icc (0 : ℝ) 1 := by
    rw [hc_def]
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hΞy : Ξ (x - n) = Ξ x := by
    have := hper.sub_int_mul_eq (x := x) n
    simpa using this
  -- The factor `Ξ x - Ξ t` is `M|x - t - n|`-small.
  have hLip : ∀ t, |Ξ x - Ξ t| ≤ M * |x - t - n| := by
    intro t
    have h := abs_sub_le_of_hasDerivAt_bound hΞ hξM (x - n) t
    rw [hΞy, show x - n - t = x - t - n by ring] at h
    exact h
  -- Away from the clamp the singularity is absent.
  have hne : ∀ t ∈ Ioo (0 : ℝ) 1, t ≠ c → x - t - n ≠ 0 := by
    intro t ht htc h0
    apply htc
    have ht' : t = x - n := by linarith
    rw [ht'] at ht
    rw [hc_def, min_eq_right ht.2.le, max_eq_right ht.1.le]
    rw [ht']
  set H : ℝ → ℝ := fun t => (Ξ x - Ξ t) * signPow s (x - t - n) with hH
  set h : ℝ → ℝ := fun t => -(ξ' t * signPow s (x - t - n)) +
    (Ξ x - Ξ t) * ((1 - s) * |x - t - n| ^ (s - 2)) with hh
  have hHd : ∀ t, x - t - n ≠ 0 → HasDerivAt H (h t) t := by
    intro t ht
    have h1 : HasDerivAt (fun τ => Ξ x - Ξ τ) (-(ξ' t)) t := by
      simpa using (hΞ t).const_sub (Ξ x)
    have h2 := hasDerivAt_signPow_sub (s := s) (x := x) (c := (n : ℝ)) ht
    refine HasDerivAt.congr_deriv (h1.mul h2) ?_
    simp only [hh]
    ring
  -- Boundedness of `H`, uniformly in `t`, by `|x - t - n|^s`.
  have hbound : ∀ t, |H t| ≤ M * |x - t - n| ^ s := by
    intro t
    simp only [hH]
    rw [abs_mul]
    calc |Ξ x - Ξ t| * |signPow s (x - t - n)|
        ≤ (M * |x - t - n|) * |x - t - n| ^ (s - 1) :=
          mul_le_mul (hLip t) (abs_signPow_le s _) (abs_nonneg _)
            (mul_nonneg hM0 (abs_nonneg _))
      _ = M * (|x - t - n| * |x - t - n| ^ (s - 1)) := by ring
      _ = M * |x - t - n| ^ s := by rw [abs_mul_rpow_sub_one hs0]
  have hHcont : ContinuousOn H (Icc 0 1) := by
    intro t _
    by_cases h0 : x - t - n = 0
    · have hHt : H t = 0 := by simp only [hH, h0, signPow_zero, mul_zero]
      have hcont : Continuous fun τ : ℝ => M * |x - τ - n| ^ s :=
        continuous_const.mul ((by fun_prop : Continuous fun τ : ℝ => |x - τ - n|).rpow_const
          (fun _ => Or.inr hs0.le))
      have hlim : Tendsto (fun τ : ℝ => M * |x - τ - n| ^ s) (𝓝 t) (𝓝 0) := by
        have := hcont.tendsto t
        simp only [h0, abs_zero, Real.zero_rpow hs0.ne', mul_zero] at this
        exact this
      have hH0 : Tendsto H (𝓝 t) (𝓝 0) :=
        squeeze_zero_norm (fun τ => by rw [Real.norm_eq_abs]; exact hbound τ) hlim
      have hHat : ContinuousAt H t := by
        show Tendsto H (𝓝 t) (𝓝 (H t))
        rw [hHt]
        exact hH0
      exact hHat.continuousWithinAt
    · exact (hHd t h0).continuousAt.continuousWithinAt
  -- Integrability of the three pieces, dominated by multiples of `|x - t - n|^{r}`.
  have hΞc : Continuous Ξ := continuous_iff_continuousAt.2 fun t => (hΞ t).continuousAt
  have hpow : ∀ r : ℝ, -1 < r → IntervalIntegrable (fun t : ℝ => |x - t - n| ^ r) volume 0 1 := by
    intro r hr
    have := intervalIntegrable_abs_sub_rpow hr (x - n) 0 1
    simpa only [show ∀ t : ℝ, x - n - t = x - t - n from fun t => by ring] using this
  have hmeasU : ∀ r : ℝ, Measurable fun t : ℝ => |x - t - n| ^ r := fun r => by fun_prop
  have hΦm : Measurable fun t : ℝ => signPow s (x - t - n) := by
    unfold signPow
    exact (measurable_realSign.comp (by fun_prop)).mul (hmeasU (s - 1))
  have hb1 : ∀ t, ‖ξ' t * signPow s (x - t - n)‖ ≤ M * |x - t - n| ^ (s - 1) := by
    intro t
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hξM t) (abs_signPow_le s _) (abs_nonneg _) hM0
  have hint1 : IntervalIntegrable (fun t => ξ' t * signPow s (x - t - n)) volume 0 1 :=
    IntervalIntegrable.mono_fun' ((hpow (s - 1) (by linarith)).const_mul M)
      (hξc.measurable.mul hΦm).aestronglyMeasurable
      (ae_of_all _ fun t => hb1 t)
  have hb2 : ∀ t, ‖(Ξ x - Ξ t) * ((1 - s) * |x - t - n| ^ (s - 2))‖ ≤
      (M * (1 - s)) * |x - t - n| ^ (s - 1) := by
    intro t
    have h1s : (0 : ℝ) ≤ 1 - s := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h1s,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    calc |Ξ x - Ξ t| * ((1 - s) * |x - t - n| ^ (s - 2))
        ≤ (M * |x - t - n|) * ((1 - s) * |x - t - n| ^ (s - 2)) :=
          mul_le_mul_of_nonneg_right (hLip t)
            (mul_nonneg h1s (Real.rpow_nonneg (abs_nonneg _) _))
      _ = (M * (1 - s)) * (|x - t - n| * |x - t - n| ^ (s - 2)) := by ring
      _ = (M * (1 - s)) * |x - t - n| ^ (s - 1) := by rw [abs_mul_rpow_sub_two hs1]
  have hint2 : IntervalIntegrable (fun t => (Ξ x - Ξ t) * ((1 - s) * |x - t - n| ^ (s - 2)))
      volume 0 1 :=
    IntervalIntegrable.mono_fun' ((hpow (s - 1) (by linarith)).const_mul (M * (1 - s)))
      ((continuous_const.sub hΞc).measurable.mul (measurable_const.mul (hmeasU (s - 2)))).aestronglyMeasurable
      (ae_of_all _ fun t => hb2 t)
  have hint_h : IntervalIntegrable h volume 0 1 := hint1.neg.add hint2
  have hFTC := integral_eq_sub_of_hasDerivAt_except (H := H) (h := h) zero_le_one hc hHcont
    (fun t ht htc => hHd t (hne t ht htc)) hint_h
  have hpt : ∀ t, h t = -(ξ' t * signPow s (x - t - n)) +
      (1 - s) * ((Ξ x - Ξ t) * |x - t - n| ^ (s - 2)) := fun t => by
    simp only [hh]
    ring
  have hA : IntervalIntegrable (fun t : ℝ => -(ξ' t * signPow s (x - t - n))) volume 0 1 :=
    hint1.neg
  have hB : IntervalIntegrable (fun t : ℝ => (1 - s) * ((Ξ x - Ξ t) * |x - t - n| ^ (s - 2)))
      volume 0 1 := by
    have hfeq : (fun t : ℝ => (1 - s) * ((Ξ x - Ξ t) * |x - t - n| ^ (s - 2))) =
        fun t => (Ξ x - Ξ t) * ((1 - s) * |x - t - n| ^ (s - 2)) := by
      funext t; ring
    rw [hfeq]
    exact hint2
  have hsplit : ∫ t in (0 : ℝ)..1, h t = -(∫ t in (0 : ℝ)..1, ξ' t * signPow s (x - t - n))
      + (1 - s) * ∫ t in (0 : ℝ)..1, (Ξ x - Ξ t) * |x - t - n| ^ (s - 2) := by
    simp_rw [hpt]
    rw [intervalIntegral.integral_add hA hB, intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul]
  rw [hsplit] at hFTC
  simp only [hH] at hFTC
  linarith

/-- The integration by parts identity of `singular_ibp`, written with the quotient
`(Ξ(x) - Ξ(t)) / |x - t - n|^{2-s}` that appears in the singular integral formula. -/
lemma singular_ibp_div {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {Ξ ξ' : ℝ → ℝ} {M : ℝ}
    (hΞ : ∀ t, HasDerivAt Ξ (ξ' t) t) (hξc : Continuous ξ') (hξM : ∀ t, |ξ' t| ≤ M)
    (hper : Function.Periodic Ξ 1) (x : ℝ) (n : ℤ) :
    (1 - s) * ∫ t in (0 : ℝ)..1, (Ξ x - Ξ t) / |x - t - n| ^ (2 - s)
      = ((Ξ x - Ξ 1) * signPow s (x - 1 - n) - (Ξ x - Ξ 0) * signPow s (x - 0 - n))
        + ∫ t in (0 : ℝ)..1, ξ' t * signPow s (x - t - n) := by
  have hpt : ∀ t : ℝ, (Ξ x - Ξ t) / |x - t - n| ^ (2 - s) =
      (Ξ x - Ξ t) * |x - t - n| ^ (s - 2) := by
    intro t
    rw [div_eq_mul_inv, ← Real.rpow_neg (abs_nonneg _), show -(2 - s) = s - 2 by ring]
  simp_rw [hpt]
  exact singular_ibp hs0 hs1 hΞ hξc hξM hper x n

end Riesz1
