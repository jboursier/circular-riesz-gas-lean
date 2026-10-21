/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Group.Integral

/-!
# A log-concave survival bound

Let `f` be a positive log-concave density on `(0, b)`, extended by zero, with mean one. Write
`S t = ∫_{[t, ∞)} f` for the survival function. The bound `S t ≤ 2 exp (-(log 2) t / 2)` holds
for every `t ≥ 0`.

The proof has four steps.

1. For `0 < t ≤ s` and `0 ≤ x`, concavity of `log f` gives `f (s + x) f t ≤ f (t + x) f s`.
   Integrating over `x ≥ 0` gives the hazard comparison `S s f t ≤ S t f s`.
2. The hazard `f / S` is nondecreasing, so `(log S)' = -f / S` is nonincreasing on `(0, b)`.
   Hence `log S` is concave on `[0, b)`, with `log S 0 = 0`.
3. Concavity at the points `0`, `2` and `t` gives `log S t ≤ (t / 2) log S 2`.
4. Markov's inequality gives `S 2 ≤ 1 / 2`, which yields the bound for `2 ≤ t < b`. The bound is
   trivial for `t < 2` (because `S ≤ 1`) and for `t ≥ b` (because `S t = 0`).
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- Translating a set integral over `[s, ∞)` to `[0, ∞)`: the integral of `g` over `[s, ∞)`
equals the integral over `[0, ∞)` of `y ↦ g (s + y)`. -/
theorem logConcave_setIntegral_Ici_translate (g : ℝ → ℝ) (s : ℝ) :
    ∫ x in Ici s, g x = ∫ y in Ici 0, g (s + y) := by
  calc ∫ x in Ici s, g x = ∫ x, (Ici s).indicator g x :=
        (integral_indicator measurableSet_Ici).symm
    _ = ∫ x, (Ici s).indicator g (s + x) := (integral_add_left_eq_self _ s).symm
    _ = ∫ y, (Ici 0).indicator (fun y => g (s + y)) y := by
        congr 1
        funext y
        simp only [Set.indicator_apply, Set.mem_Ici]
        by_cases hy : 0 ≤ y
        · have hsy : s ≤ s + y := by linarith
          simp [hy, hsy]
        · have hsy : ¬ s ≤ s + y := not_le.mpr (by linarith [not_le.mp hy])
          simp [hy, hsy]
    _ = ∫ y in Ici 0, g (s + y) := integral_indicator measurableSet_Ici

/-- A positive log-concave density is nonnegative everywhere, since it vanishes off `(0, b)`. -/
theorem logConcave_nonneg {b : ℝ} {f : ℝ → ℝ} (hfpos : ∀ x ∈ Ioo 0 b, 0 < f x)
    (hf0 : ∀ x ∉ Ioo 0 b, f x = 0) (x : ℝ) : 0 ≤ f x := by
  by_cases hx : x ∈ Ioo 0 b
  · exact (hfpos x hx).le
  · rw [hf0 x hx]

/-- **Shift inequality.** Let `log f` be concave on `(0, b)`. For `0 < t ≤ s` and `0 ≤ x`, it
holds that `f (s + x) f t ≤ f (t + x) f s`. -/
theorem logConcave_shift_le {b : ℝ} {f : ℝ → ℝ} (hfpos : ∀ x ∈ Ioo 0 b, 0 < f x)
    (hf0 : ∀ x ∉ Ioo 0 b, f x = 0)
    (hconc : ConcaveOn ℝ (Ioo 0 b) (fun x => Real.log (f x)))
    {t s x : ℝ} (ht : 0 < t) (hts : t ≤ s) (hx : 0 ≤ x) :
    f (s + x) * f t ≤ f (t + x) * f s := by
  have hnn := logConcave_nonneg hfpos hf0
  have hzero : ∀ y, b ≤ y → f y = 0 := fun y hy => hf0 y (fun h => (not_lt.mpr hy) h.2)
  rcases lt_or_ge (t + x) b with h1 | h1
  swap
  · rw [hzero (t + x) h1, hzero (s + x) (by linarith)]
    simp
  rcases lt_or_ge (s + x) b with h2 | h2
  swap
  · rw [hzero (s + x) h2, zero_mul]
    exact mul_nonneg (hnn _) (hnn _)
  -- All four points `t`, `s`, `t + x`, `s + x` lie in `(0, b)`.
  have hs : 0 < s := lt_of_lt_of_le ht hts
  have hmemt : t ∈ Ioo 0 b := ⟨ht, by linarith⟩
  have hmems : s ∈ Ioo 0 b := ⟨hs, by linarith⟩
  have hmemtx : t + x ∈ Ioo 0 b := ⟨by linarith, h1⟩
  have hmemsx : s + x ∈ Ioo 0 b := ⟨by linarith, h2⟩
  rcases hx.eq_or_lt with hx0 | hxpos
  · rw [← hx0]
    simp [mul_comm]
  -- Weights `lam = x / (s + x - t)` and `1 - lam`, so that
  -- `lam t + (1 - lam)(s + x) = s` and `(1 - lam) t + lam (s + x) = t + x`.
  have hDpos : 0 < s + x - t := by linarith
  set lam : ℝ := x / (s + x - t) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hx hDpos.le
  have hlam1 : 0 ≤ 1 - lam := by
    rw [hlam, sub_nonneg, div_le_one hDpos]
    linarith
  have hsum : lam + (1 - lam) = 1 := by ring
  have e1 : lam * t + (1 - lam) * (s + x) = s := by
    rw [hlam]
    field_simp
    ring
  have e2 : (1 - lam) * t + lam * (s + x) = t + x := by
    rw [hlam]
    field_simp
    ring
  have hc1 := hconc.2 hmemt hmemsx hlam0 hlam1 hsum
  have hc2 := hconc.2 hmemt hmemsx hlam1 hlam0 (by ring)
  simp only [smul_eq_mul] at hc1 hc2
  rw [e1] at hc1
  rw [e2] at hc2
  have hlog : Real.log (f t) + Real.log (f (s + x)) ≤
      Real.log (f s) + Real.log (f (t + x)) := by
    nlinarith [hc1, hc2]
  have hpos1 : 0 < f t * f (s + x) := mul_pos (hfpos t hmemt) (hfpos _ hmemsx)
  have hpos2 : 0 < f s * f (t + x) := mul_pos (hfpos s hmems) (hfpos _ hmemtx)
  have hlog' : Real.log (f t * f (s + x)) ≤ Real.log (f s * f (t + x)) := by
    rw [Real.log_mul (hfpos t hmemt).ne' (hfpos _ hmemsx).ne',
      Real.log_mul (hfpos s hmems).ne' (hfpos _ hmemtx).ne']
    exact hlog
  have hfin := (Real.log_le_log_iff hpos1 hpos2).mp hlog'
  rw [mul_comm (f (s + x)), mul_comm (f (t + x))]
  exact hfin

/-- **Hazard comparison.** Let `log f` be concave on `(0, b)`. For `0 < t ≤ s`, the inequality
`S s f t ≤ S t f s` holds, where `S v = ∫_{[v, ∞)} f`. -/
theorem logConcave_hazard_le {b : ℝ} {f : ℝ → ℝ} (hfint : Integrable f)
    (hfpos : ∀ x ∈ Ioo 0 b, 0 < f x) (hf0 : ∀ x ∉ Ioo 0 b, f x = 0)
    (hconc : ConcaveOn ℝ (Ioo 0 b) (fun x => Real.log (f x)))
    {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) :
    (∫ x in Ici s, f x) * f t ≤ (∫ x in Ici t, f x) * f s := by
  have hL : (∫ x in Ici s, f x) * f t = ∫ y in Ici 0, f (s + y) * f t := by
    rw [← integral_mul_const]
    exact logConcave_setIntegral_Ici_translate (fun x => f x * f t) s
  have hR : (∫ x in Ici t, f x) * f s = ∫ y in Ici 0, f (t + y) * f s := by
    rw [← integral_mul_const]
    exact logConcave_setIntegral_Ici_translate (fun x => f x * f s) t
  rw [hL, hR]
  refine setIntegral_mono_on ?_ ?_ measurableSet_Ici fun y hy =>
    logConcave_shift_le hfpos hf0 hconc ht hts (mem_Ici.mp hy)
  · exact ((hfint.comp_add_left s).mul_const (f t)).integrableOn
  · exact ((hfint.comp_add_left t).mul_const (f s)).integrableOn

/-- For `v ≤ b`, the tail integral over `[v, ∞)` equals the interval integral over `[v, b]`,
because `f` vanishes beyond `b`. -/
theorem logConcave_setIntegral_Ici_eq_intervalIntegral {b : ℝ} {f : ℝ → ℝ}
    (hf0 : ∀ x ∉ Ioo 0 b, f x = 0) {v : ℝ} (hv : v ≤ b) :
    ∫ x in Ici v, f x = ∫ x in v..b, f x := by
  rw [integral_Ici_eq_integral_Ioi, intervalIntegral.integral_of_le hv]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self ?_
  intro x hx
  apply hf0 x
  intro hxb
  exact hx.2 ⟨hx.1, hxb.2.le⟩

/-- The survival function is strictly positive on `[0, b)`. -/
theorem logConcave_survival_pos {b : ℝ} {f : ℝ → ℝ} (hfint : Integrable f)
    (hfpos : ∀ x ∈ Ioo 0 b, 0 < f x) (hf0 : ∀ x ∉ Ioo 0 b, f x = 0) {v : ℝ}
    (hv0 : 0 ≤ v) (hvb : v < b) : 0 < ∫ x in Ici v, f x := by
  rw [logConcave_setIntegral_Ici_eq_intervalIntegral hf0 hvb.le]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on hfint.intervalIntegrable ?_ hvb
  intro x hx
  exact hfpos x ⟨lt_of_le_of_lt hv0 hx.1, hx.2⟩

/-- A positive log-concave density is continuous on `(0, b)`. -/
theorem logConcave_continuousOn {b : ℝ} {f : ℝ → ℝ} (hfpos : ∀ x ∈ Ioo 0 b, 0 < f x)
    (hconc : ConcaveOn ℝ (Ioo 0 b) (fun x => Real.log (f x))) :
    ContinuousOn f (Ioo 0 b) := by
  have hlog : ContinuousOn (fun x => Real.log (f x)) (Ioo 0 b) := by
    simpa [interior_Ioo] using hconc.continuousOn_interior
  have hexp : ContinuousOn (fun x => Real.exp (Real.log (f x))) (Ioo 0 b) :=
    Real.continuous_exp.comp_continuousOn hlog
  exact hexp.congr fun x hx => (Real.exp_log (hfpos x hx)).symm

/-- The survival function has derivative `-f u` at each `u` in `(0, b)`. -/
theorem logConcave_hasDerivAt_survival {b : ℝ} {f : ℝ → ℝ} (hfint : Integrable f)
    (hf0 : ∀ x ∉ Ioo 0 b, f x = 0) (hfc : ContinuousOn f (Ioo 0 b)) {u : ℝ}
    (hu : u ∈ Ioo 0 b) : HasDerivAt (fun v => ∫ x in Ici v, f x) (-f u) u := by
  have h1 : HasDerivAt (fun v => ∫ x in v..b, f x) (-f u) u :=
    intervalIntegral.integral_hasDerivAt_left hfint.intervalIntegrable
      (hfc.stronglyMeasurableAtFilter isOpen_Ioo u hu)
      (hfc.continuousAt (Ioo_mem_nhds hu.1 hu.2))
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
  exact logConcave_setIntegral_Ici_eq_intervalIntegral hf0 hv.2.le

/-- The logarithm of the survival function has derivative `-f u / S u` at `u` in `(0, b)`,
where `S u = ∫_{[u, ∞)} f`. -/
theorem logConcave_hasDerivAt_log_survival {b : ℝ} {f : ℝ → ℝ} (hfint : Integrable f)
    (hfpos : ∀ x ∈ Ioo 0 b, 0 < f x) (hf0 : ∀ x ∉ Ioo 0 b, f x = 0)
    (hfc : ContinuousOn f (Ioo 0 b)) {u : ℝ} (hu : u ∈ Ioo 0 b) :
    HasDerivAt (fun v => Real.log (∫ x in Ici v, f x)) (-f u / ∫ x in Ici u, f x) u :=
  (logConcave_hasDerivAt_survival hfint hf0 hfc hu).log
    (logConcave_survival_pos hfint hfpos hf0 hu.1.le hu.2).ne'

/-- The survival function is continuous on `[0, b)`. -/
theorem logConcave_continuousOn_survival {b : ℝ} {f : ℝ → ℝ} (hfint : Integrable f)
    (hf0 : ∀ x ∉ Ioo 0 b, f x = 0) :
    ContinuousOn (fun v => ∫ x in Ici v, f x) (Ico 0 b) := by
  have hc : Continuous fun v => -(∫ x in b..v, f x) :=
    (intervalIntegral.continuous_primitive (fun a c => hfint.intervalIntegrable) b).neg
  refine ContinuousOn.congr hc.continuousOn ?_
  intro v hv
  show ∫ x in Ici v, f x = -(∫ x in b..v, f x)
  rw [logConcave_setIntegral_Ici_eq_intervalIntegral hf0 hv.2.le, intervalIntegral.integral_symm b v]

/-- **Concavity of the log-survival function.** Let `log f` be concave on `(0, b)`. Then
`v ↦ log (∫_{[v, ∞)} f)` is concave on `[0, b)`. -/
theorem logConcave_concaveOn_log_survival {b : ℝ} {f : ℝ → ℝ} (hfint : Integrable f)
    (hfpos : ∀ x ∈ Ioo 0 b, 0 < f x) (hf0 : ∀ x ∉ Ioo 0 b, f x = 0)
    (hconc : ConcaveOn ℝ (Ioo 0 b) (fun x => Real.log (f x))) :
    ConcaveOn ℝ (Ico 0 b) (fun v => Real.log (∫ x in Ici v, f x)) := by
  have hfc := logConcave_continuousOn hfpos hconc
  have hcont : ContinuousOn (fun v => Real.log (∫ x in Ici v, f x)) (Ico 0 b) :=
    (logConcave_continuousOn_survival hfint hf0).log fun v hv =>
      (logConcave_survival_pos hfint hfpos hf0 hv.1 hv.2).ne'
  refine AntitoneOn.concaveOn_of_deriv (convex_Ico 0 b) hcont ?_ ?_
  · rw [interior_Ico]
    intro v hv
    exact ((logConcave_hasDerivAt_log_survival hfint hfpos hf0 hfc hv).differentiableAt).differentiableWithinAt
  · rw [interior_Ico]
    intro a ha c hc hac
    rw [(logConcave_hasDerivAt_log_survival hfint hfpos hf0 hfc ha).deriv,
      (logConcave_hasDerivAt_log_survival hfint hfpos hf0 hfc hc).deriv]
    -- Need `f a / S a ≤ f c / S c`, which is the hazard comparison.
    have hSa := logConcave_survival_pos hfint hfpos hf0 ha.1.le ha.2
    have hSc := logConcave_survival_pos hfint hfpos hf0 hc.1.le hc.2
    have hhaz := logConcave_hazard_le hfint hfpos hf0 hconc ha.1 hac
    have hk : f a / ∫ x in Ici a, f x ≤ f c / ∫ x in Ici c, f x := by
      rw [div_le_div_iff₀ hSa hSc]
      nlinarith [hhaz]
    rw [neg_div, neg_div]
    exact neg_le_neg hk

/-- The survival function at `0` equals one, since `f` is a density supported in `[0, ∞)`. -/
theorem logConcave_survival_zero {b : ℝ} {f : ℝ → ℝ} (hint : ∫ x, f x = 1)
    (hf0 : ∀ x ∉ Ioo 0 b, f x = 0) : ∫ x in Ici (0 : ℝ), f x = 1 := by
  have hcompl : ∀ x, x ∉ Ici (0 : ℝ) → f x = 0 :=
    fun x hx => hf0 x (fun hxb => hx (le_of_lt hxb.1))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hcompl, hint]

/-- **Markov bound at two.** The survival function satisfies `S 2 ≤ 1 / 2`. -/
theorem logConcave_survival_two_le {f : ℝ → ℝ} (hfnn : ∀ x, 0 ≤ f x) (hfint : Integrable f)
    (hxfint : Integrable (fun x => x * f x)) (hxfnn : ∀ x, 0 ≤ x * f x)
    (hmean : ∫ x, x * f x = 1) : ∫ x in Ici (2 : ℝ), f x ≤ 1 / 2 := by
  have hpt : ∀ x, (Ici (2 : ℝ)).indicator f x ≤ (1 / 2) * (x * f x) := by
    intro x
    by_cases hx : 2 ≤ x
    · rw [indicator_of_mem (mem_Ici.mpr hx)]
      nlinarith [mul_nonneg (hfnn x) (sub_nonneg.mpr hx)]
    · rw [indicator_of_notMem (fun h => hx (mem_Ici.mp h))]
      exact mul_nonneg (by norm_num) (hxfnn x)
  calc ∫ x in Ici (2 : ℝ), f x = ∫ x, (Ici (2 : ℝ)).indicator f x :=
        (integral_indicator measurableSet_Ici).symm
    _ ≤ ∫ x, (1 / 2) * (x * f x) :=
        integral_mono (hfint.indicator measurableSet_Ici) (hxfint.const_mul _) hpt
    _ = 1 / 2 := by rw [integral_const_mul, hmean]; ring

/-- **Log-concave survival bound.** Let `b > 0` and let `f` be positive and log-concave on
`(0, b)`, extended by zero outside. Suppose `∫ f = 1` and `∫ x f(x) = 1`. Then for every
`t ≥ 0`, the tail `∫_{[t, ∞)} f` is at most `2 exp (-(log 2) t / 2)`. -/
theorem logConcave_survival_le {b : ℝ} (hb : 0 < b) (f : ℝ → ℝ)
    (hfpos : ∀ x ∈ Set.Ioo 0 b, 0 < f x) (hf0 : ∀ x ∉ Set.Ioo 0 b, f x = 0)
    (hconc : ConcaveOn ℝ (Set.Ioo 0 b) (fun x => Real.log (f x)))
    (hint : ∫ x, f x = 1) (hmean : ∫ x, x * f x = 1) (t : ℝ) (ht : 0 ≤ t) :
    ∫ x in Set.Ici t, f x ≤ 2 * Real.exp (-(Real.log 2) * t / 2) := by
  have hfint : Integrable f := by
    by_contra h
    rw [integral_undef h] at hint
    exact zero_ne_one hint
  have hxfint : Integrable (fun x => x * f x) := by
    by_contra h
    rw [integral_undef h] at hmean
    exact zero_ne_one hmean
  have hfnn := logConcave_nonneg hfpos hf0
  have hxfnn : ∀ x, 0 ≤ x * f x := fun x => by
    by_cases hx : x ∈ Ioo 0 b
    · exact mul_nonneg hx.1.le (hfnn x)
    · rw [hf0 x hx, mul_zero]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rcases lt_or_ge t 2 with h2 | h2
  · -- Case `t < 2`: the survival function is at most one, and the bound is at least one.
    have hS1 : ∫ x in Ici t, f x ≤ ∫ x, f x :=
      setIntegral_le_integral hfint (Filter.Eventually.of_forall hfnn)
    rw [hint] at hS1
    have hcoef : -Real.log 2 ≤ -(Real.log 2) * t / 2 := by
      nlinarith [mul_nonneg hlog2.le (by linarith : (0 : ℝ) ≤ 2 - t)]
    have hexp := Real.exp_le_exp.mpr hcoef
    rw [Real.exp_neg, Real.exp_log two_pos] at hexp
    linarith
  rcases lt_or_ge t b with htb | htb
  swap
  · -- Case `t ≥ b`: the tail vanishes.
    have hzero : ∫ x in Ici t, f x = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun x hx =>
        hf0 x fun hxb => absurd hxb.2 (not_lt.mpr (le_trans htb (mem_Ici.mp hx)))
    rw [hzero]
    positivity
  -- Case `2 ≤ t < b`: concavity of the log-survival function at the points `0`, `2`, `t`.
  have ht0 : 0 < t := by linarith
  have hconcL := logConcave_concaveOn_log_survival hfint hfpos hf0 hconc
  have hS0 := logConcave_survival_zero hint hf0
  have hSt := logConcave_survival_pos hfint hfpos hf0 (by linarith) htb
  have hS2 : 0 < ∫ x in Ici (2 : ℝ), f x :=
    logConcave_survival_pos hfint hfpos hf0 (by norm_num) (by linarith)
  have hS2le := logConcave_survival_two_le hfnn hfint hxfint hxfnn hmean
  have hw0 : 0 ≤ 2 / t := div_nonneg (by norm_num) ht0.le
  have hw1 : 0 ≤ 1 - 2 / t := by
    rw [sub_nonneg, div_le_one ht0]
    exact h2
  -- `2 = (2 / t) t + (1 - 2 / t) 0`, so concavity gives `(2 / t) log S t + (1 - 2 / t) log S 0
  -- ≤ log S 2`, and `log S 0 = 0`.
  have hcomb := hconcL.2 (⟨ht, htb⟩ : t ∈ Ico 0 b) (⟨le_refl 0, hb⟩ : (0 : ℝ) ∈ Ico 0 b) hw0 hw1
    (by ring)
  have e : 2 / t * t + (1 - 2 / t) * 0 = 2 := by
    rw [mul_zero, add_zero, div_mul_cancel₀ (2 : ℝ) ht0.ne']
  simp only [smul_eq_mul] at hcomb
  rw [e, hS0, Real.log_one, mul_zero, add_zero] at hcomb
  -- Markov's bound `S 2 ≤ 1 / 2` gives `log S 2 ≤ -log 2`.
  have hlogS2 : Real.log (∫ x in Ici (2 : ℝ), f x) ≤ -Real.log 2 := by
    have h := Real.log_le_log hS2 hS2le
    rw [one_div, Real.log_inv] at h
    exact h
  have hk : 2 / t * Real.log (∫ x in Ici t, f x) ≤ -Real.log 2 := hcomb.trans hlogS2
  have hlogt : Real.log (∫ x in Ici t, f x) ≤ -(Real.log 2) * t / 2 := by
    have hkey : t / 2 * (2 / t * Real.log (∫ x in Ici t, f x)) =
        Real.log (∫ x in Ici t, f x) := by
      field_simp
    calc Real.log (∫ x in Ici t, f x)
        = t / 2 * (2 / t * Real.log (∫ x in Ici t, f x)) := hkey.symm
      _ ≤ t / 2 * (-Real.log 2) :=
          mul_le_mul_of_nonneg_left hk (by linarith : (0 : ℝ) ≤ t / 2)
      _ = -(Real.log 2) * t / 2 := by ring
  have hfinal : ∫ x in Ici t, f x ≤ Real.exp (-(Real.log 2) * t / 2) :=
    calc ∫ x in Ici t, f x = Real.exp (Real.log (∫ x in Ici t, f x)) := (Real.exp_log hSt).symm
      _ ≤ Real.exp (-(Real.log 2) * t / 2) := Real.exp_le_exp.mpr hlogt
  linarith [Real.exp_pos (-(Real.log 2) * t / 2)]

end Riesz1
