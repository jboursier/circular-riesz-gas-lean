/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportSingular

/-!
# Summation facts for the pointwise transport formula

The pointwise kernel `∑_n sgn(x - t - n) |x - t - n|^{s-1}` is only conditionally convergent, so
its terms are paired with the mean-zero density `ξ - m`. This file proves:

* symmetric partial sums over `ℤ` converge to the sum of a summable family.
* for a bounded mean-zero continuous `ξ'`, the integrated terms
  `∫_0^1 ξ'(t) sgn(x - t - n)|x - t - n|^{s-1} dt` are bounded by `C |n|^{s-2}` once `|n|`
  dominates `|x|`, hence summable over `n ∈ ℤ`.

These are the convergence statements needed for the pointwise transport formula.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology
open scoped ContDiff Real

namespace Riesz1

/-- Symmetric partial sums of a summable family over `ℤ` converge to its sum. -/
lemma tendsto_symmetric_sum {f : ℤ → ℝ} (hf : Summable f) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f n) atTop
      (𝓝 (∑' n, f n)) := by
  have hg : Tendsto (fun M : ℕ => Finset.Icc (-(M : ℤ)) (M : ℤ)) atTop atTop := by
    refine Filter.tendsto_atTop_finset_of_monotone ?_ ?_
    · intro M N hMN
      have hMN' : (M : ℤ) ≤ N := by exact_mod_cast hMN
      exact Finset.Icc_subset_Icc (by linarith) (by linarith)
    · intro a
      refine ⟨a.natAbs, ?_⟩
      simp only [Finset.mem_Icc]
      constructor <;> omega
  exact hf.hasSum.comp hg

/-- For `|n| ≥ 2|x| + 2`, the distance from `x - t` to `n` is at least `|n|/2` on `[0, 1]`. -/
lemma half_abs_le_abs_sub {x t : ℝ} {n : ℤ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hn : 2 * |x| + 2 ≤ |(n : ℝ)|) : |(n : ℝ)| / 2 ≤ |x - t - n| := by
  have h1 : |(n : ℝ)| ≤ |x - t| + |x - t - n| := by
    have := abs_sub (x - t) (x - t - n)
    rwa [show x - t - (x - t - n) = (n : ℝ) by ring] at this
  have h2 : |x - t| ≤ |x| + 1 := by
    have h3 := abs_sub x t
    have ht1 : |t| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    linarith
  linarith

/-- The derivative of the signed power is bounded on `[0, 1]` away from the singularity. -/
lemma abs_signPow_sub_sub_zero_le {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {n : ℤ}
    (hn : 2 * |x| + 2 ≤ |(n : ℝ)|) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |signPow s (x - t - n) - signPow s (x - 0 - n)| ≤ (1 - s) * (|(n : ℝ)| / 2) ^ (s - 2) := by
  have hpos : 0 < |(n : ℝ)| / 2 := by
    have : (2 : ℝ) ≤ |(n : ℝ)| := by linarith [abs_nonneg x]
    linarith
  have hne : ∀ τ ∈ Icc (0 : ℝ) 1, x - τ - n ≠ 0 := by
    intro τ hτ h0
    have := half_abs_le_abs_sub hτ hn
    rw [h0, abs_zero] at this
    linarith
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ)
    (f := fun τ : ℝ => signPow s (x - τ - n))
    (f' := fun τ : ℝ => (1 - s) * |x - τ - n| ^ (s - 2))
    (s := Icc (0 : ℝ) 1) (C := (1 - s) * (|(n : ℝ)| / 2) ^ (s - 2))
    (fun τ hτ => (hasDerivAt_signPow_sub (s := s) (x := x) (c := (n : ℝ)) (hne τ hτ)).hasDerivWithinAt)
    (fun τ hτ => by
      have hτ' := half_abs_le_abs_sub hτ hn
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hpos hτ' (by linarith)) (by linarith))
    (convex_Icc 0 1) (left_mem_Icc.2 zero_le_one) ht
  have ht1 : ‖t - 0‖ ≤ 1 := by
    rw [sub_zero, Real.norm_eq_abs, abs_le]; constructor <;> linarith [ht.1, ht.2]
  rw [Real.norm_eq_abs] at hmvt
  calc |signPow s (x - t - n) - signPow s (x - 0 - n)|
      ≤ (1 - s) * (|(n : ℝ)| / 2) ^ (s - 2) * ‖t - 0‖ := hmvt
    _ ≤ (1 - s) * (|(n : ℝ)| / 2) ^ (s - 2) * 1 := by
        apply mul_le_mul_of_nonneg_left ht1
        exact mul_nonneg (by linarith) (Real.rpow_nonneg hpos.le _)
    _ = (1 - s) * (|(n : ℝ)| / 2) ^ (s - 2) := mul_one _

/-- The signed power `t ↦ sgn(x - t - n)|x - t - n|^{s-1}` is measurable. -/
lemma measurable_signPow_sub (s x : ℝ) (n : ℤ) :
    Measurable fun t : ℝ => signPow s (x - t - n) := by
  unfold signPow
  refine (measurable_realSign.comp ?_).mul ?_
  · fun_prop
  · fun_prop

/-- Integrability of the centered integrand `t ↦ ξ'(t) sgn(x - t - n)|x - t - n|^{s-1}`. -/
lemma intervalIntegrable_centered_signPow {s x : ℝ} (hs0 : 0 < s) (_hs1 : s < 1)
    {ξ' : ℝ → ℝ} {M : ℝ} (hξc : Continuous ξ') (hξM : ∀ t, |ξ' t| ≤ M) (n : ℤ) :
    IntervalIntegrable (fun t => ξ' t * signPow s (x - t - n)) volume 0 1 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hξM 0)
  have hpow : IntervalIntegrable (fun t : ℝ => |x - t - n| ^ (s - 1)) volume 0 1 := by
    have := intervalIntegrable_abs_sub_rpow (r := s - 1) (by linarith) (x - n) 0 1
    simpa only [show ∀ t : ℝ, x - n - t = x - t - n from fun t => by ring] using this
  refine IntervalIntegrable.mono_fun' (hpow.const_mul M)
    (hξc.measurable.mul (measurable_signPow_sub s x n)).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  dsimp only
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hξM t) (abs_signPow_le s _) (abs_nonneg _) hM0

/-- The integrated centered term is bounded by `M (1 - s) (|n|/2)^{s-2}` once `|n| ≥ 2|x| + 2`,
because the mean-zero density kills the constant part of the signed power. -/
lemma abs_integral_centered_signPow_le {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {ξ' : ℝ → ℝ} {M : ℝ} (hξc : Continuous ξ') (hξM : ∀ t, |ξ' t| ≤ M)
    (hmean : ∫ t in (0 : ℝ)..1, ξ' t = 0) {n : ℤ} (hn : 2 * |x| + 2 ≤ |(n : ℝ)|) :
    |∫ t in (0 : ℝ)..1, ξ' t * signPow s (x - t - n)|
      ≤ M * ((1 - s) * (|(n : ℝ)| / 2) ^ (s - 2)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hξM 0)
  have hint := intervalIntegrable_centered_signPow (x := x) hs0 hs1 hξc hξM n
  have hint0 : IntervalIntegrable (fun t => ξ' t * signPow s (x - 0 - n)) volume 0 1 :=
    (hξc.intervalIntegrable 0 1).mul_const _
  have hsub : ∫ t in (0 : ℝ)..1, ξ' t * signPow s (x - t - n) =
      ∫ t in (0 : ℝ)..1, ξ' t * (signPow s (x - t - n) - signPow s (x - 0 - n)) := by
    have hpt : ∀ t, ξ' t * (signPow s (x - t - n) - signPow s (x - 0 - n)) =
        ξ' t * signPow s (x - t - n) - ξ' t * signPow s (x - 0 - n) := fun t => by ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_sub hint hint0, intervalIntegral.integral_mul_const, hmean,
      zero_mul, sub_zero]
  rw [hsub]
  have hpos : (0 : ℝ) < |(n : ℝ)| / 2 := by
    have : (2 : ℝ) ≤ |(n : ℝ)| := by linarith [abs_nonneg x]
    linarith
  have hIoc : ∀ t ∈ uIoc (0 : ℝ) 1, t ∈ Icc (0 : ℝ) 1 := fun t ht => by
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact ⟨ht.1.le, ht.2⟩
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := M * ((1 - s) * (|(n : ℝ)| / 2) ^ (s - 2)))
    (f := fun t => ξ' t * (signPow s (x - t - n) - signPow s (x - 0 - n))) (fun t ht => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hξM t) (abs_signPow_sub_sub_zero_le hs0 hs1 hn (hIoc t ht))
        (abs_nonneg _) hM0)
  rw [Real.norm_eq_abs] at hbound
  simpa using hbound

/-- The integrated centered terms are summable over `n ∈ ℤ`, with decay `|n|^{s-2}`. -/
lemma summable_centered_signPow {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {ξ' : ℝ → ℝ} {M : ℝ} (hξc : Continuous ξ') (hξM : ∀ t, |ξ' t| ≤ M)
    (hmean : ∫ t in (0 : ℝ)..1, ξ' t = 0) :
    Summable fun n : ℤ => ∫ t in (0 : ℝ)..1, ξ' t * signPow s (x - t - n) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hξM 0)
  have hsum : Summable fun n : ℤ => M * ((1 - s) * (|(n : ℝ)| / 2) ^ (s - 2)) := by
    have h := ((Real.summable_abs_int_rpow (b := 2 - s) (by linarith)).mul_left
      (M * (1 - s) * 2 ^ (2 - s)))
    refine h.congr fun n => ?_
    rcases eq_or_ne n 0 with hn0 | hn0
    · subst hn0
      simp [Real.zero_rpow (show s - 2 ≠ 0 by linarith)]
    · have hn : (0 : ℝ) < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn0)
      have e1 : (|(n : ℝ)| / 2) ^ (s - 2) = |(n : ℝ)| ^ (s - 2) * 2 ^ (2 - s) := by
        rw [div_eq_mul_inv, Real.mul_rpow hn.le (by norm_num), Real.inv_rpow (by norm_num),
          ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), neg_sub]
      rw [e1, show -(2 - s) = s - 2 by ring]
      ring
  refine Summable.of_norm_bounded_eventually hsum ?_
  have hfin : {n : ℤ | ¬ (2 * |x| + 2 ≤ |(n : ℝ)|)}.Finite := by
    refine (Set.finite_Icc (-⌈2 * |x| + 2⌉) ⌈2 * |x| + 2⌉).subset fun n hn => ?_
    simp only [mem_ofPred_eq, not_le] at hn
    have hc := Int.le_ceil (2 * |x| + 2)
    have hcast : |(n : ℝ)| = ((|n| : ℤ) : ℝ) := by push_cast; rfl
    have hlt : ((|n| : ℤ) : ℝ) ≤ (⌈2 * |x| + 2⌉ : ℝ) := by rw [← hcast]; linarith
    have hle : |n| ≤ ⌈2 * |x| + 2⌉ := by exact_mod_cast hlt
    simp only [Set.mem_Icc]
    constructor <;> linarith [abs_le.1 (le_refl |n|), neg_abs_le (n : ℤ), le_abs_self (n : ℤ)]
  refine Filter.eventually_cofinite.2 (hfin.subset fun n hn hcontra => hn ?_)
  rw [Real.norm_eq_abs]
  exact abs_integral_centered_signPow_le hs0 hs1 hξc hξM hmean hcontra

/-- Telescoping over an integer interval. -/
lemma sum_Ico_telescope_int (f : ℤ → ℝ) (a b : ℤ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (f (n + 1) - f n) = f b - f a := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ b hb ih =>
    rw [← Finset.Ico_union_Ico_eq_Ico hb (show b ≤ b + 1 by omega),
      Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive a b (b + 1)), ih,
      Finset.Ico_add_one_right_eq_Icc, Finset.Icc_self, Finset.sum_singleton]
    ring

/-- Telescoping over the symmetric interval `[-M, M]`. -/
lemma sum_Icc_telescope_int (f : ℤ → ℝ) (M : ℕ) :
    ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (f (n + 1) - f n) = f ((M : ℤ) + 1) - f (-(M : ℤ)) := by
  have hIcc : Finset.Icc (-(M : ℤ)) (M : ℤ) = Finset.Ico (-(M : ℤ)) ((M : ℤ) + 1) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, sum_Ico_telescope_int f _ _ (by omega)]

/-- The boundary sequence `sgn(x - k)|x - k|^{s-1}` tends to zero along any integer sequence
with `|k| → ∞`. -/
lemma tendsto_signPow_of_abs {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (k : ℕ → ℤ)
    (hk : Tendsto (fun M => |((k M : ℤ) : ℝ)|) atTop atTop) :
    Tendsto (fun M => signPow s (x - ((k M : ℤ) : ℝ))) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun M => |((k M : ℤ) : ℝ)| / 2) atTop atTop :=
    hk.atTop_div_const (by norm_num)
  have hlim : Tendsto (fun M => (|((k M : ℤ) : ℝ)| / 2) ^ (-(1 - s))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 1 - s)).comp hdiv
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun M : ℕ => (|((k M : ℤ) : ℝ)| / 2) ^ (-(1 - s)))
    (Eventually.of_forall fun M => norm_nonneg _) ?_ hlim
  · -- the eventual bound `|signPow| ≤ (|k|/2)^{s-1}`
    filter_upwards [hk.eventually_ge_atTop (2 * |x| + 2)] with M hM
    have hkx : |((k M : ℤ) : ℝ)| / 2 ≤ |x - ((k M : ℤ) : ℝ)| := by
      have h1 : |((k M : ℤ) : ℝ)| ≤ |x| + |x - ((k M : ℤ) : ℝ)| := by
        have := abs_sub x (x - ((k M : ℤ) : ℝ))
        rwa [show x - (x - ((k M : ℤ) : ℝ)) = ((k M : ℤ) : ℝ) by ring] at this
      linarith [abs_nonneg x]
    have hpos : 0 < |((k M : ℤ) : ℝ)| / 2 := by
      have : (2 : ℝ) ≤ |((k M : ℤ) : ℝ)| := by linarith [abs_nonneg x]
      linarith
    rw [Real.norm_eq_abs]
    calc |signPow s (x - ((k M : ℤ) : ℝ))| ≤ |x - ((k M : ℤ) : ℝ)| ^ (s - 1) :=
          abs_signPow_le s _
      _ ≤ (|((k M : ℤ) : ℝ)| / 2) ^ (s - 1) :=
          Real.rpow_le_rpow_of_nonpos hpos hkx (by linarith)
      _ = (|((k M : ℤ) : ℝ)| / 2) ^ (-(1 - s)) := by ring_nf

/-- The pointwise identity in summed form: `(1 - s) ∑_n ∫ (Ξ(x) - Ξ(t))/|x-t-n|^{2-s} dt`
equals `∑_n ∫ ξ'(t) sgn(x-t-n)|x-t-n|^{s-1} dt`, for a periodic primitive `Ξ` of a bounded
mean-zero `ξ'`, whenever the left series is summable. -/
lemma sum_singular_eq_sum_centered {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {Ξ ξ' : ℝ → ℝ} {M : ℝ} (hΞ : ∀ t, HasDerivAt Ξ (ξ' t) t) (hξc : Continuous ξ')
    (hξM : ∀ t, |ξ' t| ≤ M) (hper : Function.Periodic Ξ 1)
    (hmean : ∫ t in (0 : ℝ)..1, ξ' t = 0)
    (hJ : Summable fun n : ℤ => ∫ t in (0 : ℝ)..1, (Ξ x - Ξ t) / |x - t - n| ^ (2 - s)) :
    (1 - s) * ∑' n : ℤ, ∫ t in (0 : ℝ)..1, (Ξ x - Ξ t) / |x - t - n| ^ (2 - s)
      = ∑' n : ℤ, ∫ t in (0 : ℝ)..1, ξ' t * signPow s (x - t - n) := by
  set J : ℤ → ℝ := fun n => ∫ t in (0 : ℝ)..1, (Ξ x - Ξ t) / |x - t - n| ^ (2 - s) with hJdef
  set a : ℤ → ℝ := fun n => ∫ t in (0 : ℝ)..1, ξ' t * signPow s (x - t - n) with hadef
  set u : ℤ → ℝ := fun n => signPow s (x - (n : ℝ)) with hudef
  set c : ℝ := Ξ x - Ξ 0 with hc
  have hΞ1 : Ξ 1 = Ξ 0 := by simpa using hper 0
  -- The per-term identity, with the boundary term written through `u`.
  have hsing : ∀ n : ℤ, (1 - s) * J n = c * (u (n + 1) - u n) + a n := by
    intro n
    have hid := singular_ibp_div hs0 hs1 hΞ hξc hξM hper x n
    have hb : (Ξ x - Ξ 1) * signPow s (x - 1 - n) - (Ξ x - Ξ 0) * signPow s (x - 0 - n) =
        c * (u (n + 1) - u n) := by
      rw [hΞ1, hc, hudef]
      simp only
      rw [show x - 1 - (n : ℝ) = x - ((n + 1 : ℤ) : ℝ) by push_cast; ring, sub_zero]
      ring
    rw [hb] at hid
    simpa [hJdef, hadef] using hid
  have hasum : Summable a :=
    summable_centered_signPow hs0 hs1 hξc hξM hmean
  have hsumM : ∀ M : ℕ, (1 - s) * ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), J n =
      c * (u ((M : ℤ) + 1) - u (-(M : ℤ))) + ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a n := by
    intro M
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun n _ => hsing n), Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_Icc_telescope_int u M]
  have hL1 := (tendsto_symmetric_sum hJ).const_mul (1 - s)
  have hL2 := tendsto_symmetric_sum hasum
  have hu1 : Tendsto (fun M : ℕ => u ((M : ℤ) + 1)) atTop (𝓝 0) := by
    refine tendsto_signPow_of_abs hs0 hs1 (fun M : ℕ => (M : ℤ) + 1) ?_
    have hf : (fun M : ℕ => |(((M : ℤ) + 1 : ℤ) : ℝ)|) = fun M : ℕ => (M : ℝ) + 1 := by
      funext M
      rw [abs_of_nonneg (by push_cast; positivity)]
      push_cast; ring
    rw [hf]
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hu2 : Tendsto (fun M : ℕ => u (-(M : ℤ))) atTop (𝓝 0) := by
    refine tendsto_signPow_of_abs hs0 hs1 (fun M : ℕ => -(M : ℤ)) ?_
    have hf : (fun M : ℕ => |((-(M : ℤ) : ℤ) : ℝ)|) = fun M : ℕ => (M : ℝ) := by
      funext M
      simp
    rw [hf]
    exact tendsto_natCast_atTop_atTop
  have hL3 : Tendsto (fun M : ℕ => c * (u ((M : ℤ) + 1) - u (-(M : ℤ)))) atTop (𝓝 0) := by
    have := ((hu1.sub hu2).const_mul c)
    simpa using this
  have hcomb := hL3.add hL2
  have key := tendsto_nhds_unique (hL1.congr (fun M => (hsumM M))) hcomb
  simpa [hJdef, hadef] using key

end Riesz1
