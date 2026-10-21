/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.DerivativeBounds
public import Riesz1.ToMathlib.HurwitzKernel.Mean

/-!
# Integration by parts against the Riesz kernel

For `0 < s < 1` the kernel `g = hurwitzKernel s` is even, one-periodic and smooth off the
integers, and its derivatives obey the bounds of `iteratedDeriv_hurwitzKernel_bound`. This file
proves `∫₀¹ g'' A = ∫₀¹ g A''` for an even one-periodic function `A` with continuous second
derivative `A''`, under the size conditions `|A x| ≤ M dist(x, ℤ)²` and `|A' x| ≤ M' |x|`
and `|A'' x| ≤ M''`. This is the integration by parts step in the mean-field energy identity.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-! ### Parity and periodicity of derivatives -/

/-- The derivative of an even function is odd. -/
lemma deriv_neg_of_even {F : ℝ → ℝ} (he : ∀ x, F (-x) = F x) (x : ℝ) :
    deriv F (-x) = -deriv F x := by
  have hfun : (fun y => F (-y)) = F := funext he
  have h := deriv_comp_neg (f := F) (x := x)
  rw [hfun] at h
  linarith

/-- The derivative of a one-periodic function is one-periodic. -/
lemma deriv_add_one_of_periodic {F : ℝ → ℝ} (hp : ∀ x, F (x + 1) = F x) (x : ℝ) :
    deriv F (x + 1) = deriv F x := by
  have hfun : (fun y => F (y + 1)) = F := funext hp
  have h := deriv_comp_add_const (f := F) (x := x) (a := 1)
  rw [hfun] at h
  exact h.symm

/-- Reflection about `1/2` for an even one-periodic function. -/
lemma one_sub_of_even_periodic {F : ℝ → ℝ} (he : ∀ x, F (-x) = F x)
    (hp : ∀ x, F (x + 1) = F x) (h : ℝ) : F (1 - h) = F h := by
  rw [show 1 - h = -h + 1 by ring, hp, he]

/-- The derivative reverses sign under reflection about `1/2`. -/
lemma deriv_one_sub_of_even_periodic {F : ℝ → ℝ} (he : ∀ x, F (-x) = F x)
    (hp : ∀ x, F (x + 1) = F x) (h : ℝ) : deriv F (1 - h) = -deriv F h := by
  rw [show 1 - h = -h + 1 by ring, deriv_add_one_of_periodic hp, deriv_neg_of_even he]

/-! ### The kernel -/

/-- The kernel is even. -/
lemma hurwitzKernel_neg (s x : ℝ) : hurwitzKernel s (-x) = hurwitzKernel s x := by
  unfold hurwitzKernel
  rw [AddCircle.coe_neg, HurwitzZeta.hurwitzZetaEven_neg]

/-- The kernel is one-periodic. -/
lemma hurwitzKernel_add_one (s x : ℝ) : hurwitzKernel s (x + 1) = hurwitzKernel s x :=
  hurwitzKernel_periodic s x

/-- Points of `(0, 1)` are off the integers. -/
lemma coe_ne_zero_of_mem_Ioo01 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    (x : UnitAddCircle) ≠ 0 := by
  have h := coe_ne_zero_of_mem_Ioo_int 0 x ⟨by simpa using h0, by simpa using h1⟩
  simpa using h

/-- The kernel is smooth off the integers, with the first and second derivative of the kernel
given by the bounds of `hasDerivAt_deriv_hurwitzKernel`. -/
lemma hasDerivAt_deriv_hurwitzKernel_of_ne (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ)
    (hx : (x : UnitAddCircle) ≠ 0) :
    HasDerivAt (deriv (hurwitzKernel s)) (deriv (deriv (hurwitzKernel s)) x) x := by
  obtain ⟨h1, -, -⟩ := second_derivative_hurwitzKernel s hs0 hs1 x hx
  rw [h1.deriv]
  exact h1

/-- Derivative bound of order one for the kernel. -/
lemma deriv_hurwitzKernel_bound (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, (x : UnitAddCircle) ≠ 0 →
      |deriv (hurwitzKernel s) x| ≤ C * dist (x : UnitAddCircle) 0 ^ (-s - 1) := by
  obtain ⟨C, hC, h⟩ := iteratedDeriv_hurwitzKernel_bound s hs0 hs1 1
  refine ⟨C, hC, fun x hx => ?_⟩
  simpa [iteratedDeriv_one] using h x hx

/-- Derivative bound of order two for the kernel. -/
lemma deriv_deriv_hurwitzKernel_bound (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, (x : UnitAddCircle) ≠ 0 →
      |deriv (deriv (hurwitzKernel s)) x| ≤ C * dist (x : UnitAddCircle) 0 ^ (-s - 2) := by
  obtain ⟨C, hC, h⟩ := iteratedDeriv_hurwitzKernel_bound s hs0 hs1 2
  refine ⟨C, hC, fun x hx => ?_⟩
  have h2 := h x hx
  simpa [iteratedDeriv_succ, iteratedDeriv_one] using h2

/-- Zeroth derivative bound of the kernel. -/
lemma hurwitzKernel_bound (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, (x : UnitAddCircle) ≠ 0 →
      |hurwitzKernel s x| ≤ C * dist (x : UnitAddCircle) 0 ^ (-s) := by
  obtain ⟨C, hC, h⟩ := iteratedDeriv_hurwitzKernel_bound s hs0 hs1 0
  refine ⟨C, hC, fun x hx => ?_⟩
  simpa using h x hx

/-! ### Distance to the integers and an integrable majorant -/

/-- The distance to the nearest integer is the absolute value of `x - round x`. -/
lemma dist_coe_zero_eq (x : ℝ) : dist (x : UnitAddCircle) 0 = |x - round x| := by
  rw [dist_zero_right, UnitAddCircle.norm_eq]

/-- For `0 ≤ x < 1/2` the distance to the integers is `x`. -/
lemma dist_coe_zero_of_mem_Ico {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1 / 2) :
    dist (x : UnitAddCircle) 0 = x := by
  have hr : round x = 0 := by
    rw [round_eq, Int.floor_eq_zero_iff]
    constructor <;> linarith
  rw [dist_coe_zero_eq, hr]
  simp [abs_of_nonneg h0]

/-- On `(0, 1)` the distance to the integers is at least `min x (1 - x)`. -/
lemma min_le_dist_coe (x : ℝ) :
    min x (1 - x) ≤ dist (x : UnitAddCircle) 0 := by
  rw [dist_coe_zero_eq]
  rcases le_or_gt (round x : ℝ) 0 with hr | hr
  · calc min x (1 - x) ≤ x := min_le_left _ _
      _ ≤ x - round x := by linarith
      _ ≤ |x - round x| := le_abs_self _
  · have hr' : (1 : ℝ) ≤ round x := by
      have : (0 : ℤ) < round x := by exact_mod_cast hr
      exact_mod_cast this
    calc min x (1 - x) ≤ 1 - x := min_le_right _ _
      _ ≤ round x - x := by linarith
      _ ≤ |x - round x| := by rw [abs_sub_comm]; exact le_abs_self _

/-- The majorant `x ^ (-s) + (1 - x) ^ (-s)` dominates `dist (x : UnitAddCircle) 0 ^ (-s)`. -/
lemma dist_rpow_neg_le {s x : ℝ} (hs0 : 0 < s) (h0 : 0 < x) (h1 : x < 1) :
    dist (x : UnitAddCircle) 0 ^ (-s) ≤ x ^ (-s) + (1 - x) ^ (-s) := by
  have hm : 0 < min x (1 - x) := lt_min h0 (by linarith)
  have hd : min x (1 - x) ≤ dist (x : UnitAddCircle) 0 := min_le_dist_coe x
  have hdpos : 0 < dist (x : UnitAddCircle) 0 := lt_of_lt_of_le hm hd
  have h1' : dist (x : UnitAddCircle) 0 ^ (-s) ≤ (min x (1 - x)) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos hm hd (by linarith)
  rcases min_choice x (1 - x) with h | h
  · rw [h] at h1'
    have : 0 ≤ (1 - x) ^ (-s) := Real.rpow_nonneg (by linarith) _
    linarith
  · rw [h] at h1'
    have : 0 ≤ x ^ (-s) := Real.rpow_nonneg h0.le _
    linarith

/-- The majorant is integrable on `(0, 1)`. -/
lemma integrableOn_rpow_majorant {s : ℝ} (hs1 : s < 1) :
    IntegrableOn (fun x : ℝ => x ^ (-s) + (1 - x) ^ (-s)) (Ioo 0 1) := by
  have hpow : IntervalIntegrable (fun x : ℝ => x ^ (-s)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hpow' : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (-s)) volume 0 1 := by
    have h := (hpow.comp_sub_left 1).symm
    simpa using h
  have hsum := hpow.add hpow'
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hsum
  exact hsum

/-! ### Bounds for the integration by parts -/

/-- For `0 < h < 1/2` the kernel's first derivative is bounded by `C h ^ (-1 - s)`. -/
lemma deriv_hurwitzKernel_small (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, ∀ h : ℝ, 0 < h → h < 1 / 2 → |deriv (hurwitzKernel s) h| ≤ C * h ^ (-s - 1) := by
  obtain ⟨C, hC, hb⟩ := deriv_hurwitzKernel_bound s hs0 hs1
  refine ⟨C, fun h h0 h1 => ?_⟩
  have hne := coe_ne_zero_of_mem_Ioo01 h0 (by linarith)
  have := hb h hne
  rwa [dist_coe_zero_of_mem_Ico h0.le h1] at this

/-- For `0 < h < 1/2` the kernel is bounded by `C h ^ (-s)`. -/
lemma hurwitzKernel_small (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, ∀ h : ℝ, 0 < h → h < 1 / 2 → |hurwitzKernel s h| ≤ C * h ^ (-s) := by
  obtain ⟨C, hC, hb⟩ := hurwitzKernel_bound s hs0 hs1
  refine ⟨C, fun h h0 h1 => ?_⟩
  have hne := coe_ne_zero_of_mem_Ioo01 h0 (by linarith)
  have := hb h hne
  rwa [dist_coe_zero_of_mem_Ico h0.le h1] at this

/-- The product `g'' A` is dominated by a multiple of the majorant on `(0, 1)`. -/
lemma abs_deriv_deriv_mul_le (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (A : ℝ → ℝ) (M : ℝ)
    (hAb : ∀ x, |A x| ≤ M * dist (x : UnitAddCircle) 0 ^ 2) :
    ∃ K : ℝ, ∀ x : ℝ, 0 < x → x < 1 →
      |deriv (deriv (hurwitzKernel s)) x * A x| ≤ K * (x ^ (-s) + (1 - x) ^ (-s)) := by
  obtain ⟨C, hC, hb⟩ := deriv_deriv_hurwitzKernel_bound s hs0 hs1
  refine ⟨C * |M|, fun x h0 h1 => ?_⟩
  have hne := coe_ne_zero_of_mem_Ioo01 h0 h1
  set d := dist (x : UnitAddCircle) 0 with hd
  have hdpos : 0 < d := by
    rw [hd, dist_pos]
    intro h
    exact hne (by simpa using h)
  have hG2 := hb x hne
  have hAx := hAb x
  have hA0 : |A x| ≤ |M| * d ^ 2 := by
    refine hAx.trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self M) (sq_nonneg _)
  have hpow : d ^ (-s - 2) * d ^ 2 = d ^ (-s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hdpos]
    congr 1
    push_cast
    ring
  calc |deriv (deriv (hurwitzKernel s)) x * A x|
      = |deriv (deriv (hurwitzKernel s)) x| * |A x| := abs_mul _ _
    _ ≤ (C * d ^ (-s - 2)) * (|M| * d ^ 2) :=
        mul_le_mul hG2 hA0 (abs_nonneg _) (by positivity)
    _ = C * |M| * d ^ (-s) := by rw [← hpow]; ring
    _ ≤ C * |M| * (x ^ (-s) + (1 - x) ^ (-s)) := by
        apply mul_le_mul_of_nonneg_left (dist_rpow_neg_le hs0 h0 h1)
        positivity

/-- The product `g'' A` is interval integrable on `[0, 1]`. -/
lemma integrableOn_deriv_deriv_mul (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (A : ℝ → ℝ) (M : ℝ)
    (hA : Continuous A)
    (hAb : ∀ x, |A x| ≤ M * dist (x : UnitAddCircle) 0 ^ 2) :
    IntegrableOn (fun x => deriv (deriv (hurwitzKernel s)) x * A x) (Ioo 0 1) := by
  obtain ⟨K, hK⟩ := abs_deriv_deriv_mul_le s hs0 hs1 A M hAb
  have hmeas : Measurable (fun x => deriv (deriv (hurwitzKernel s)) x * A x) :=
    (measurable_deriv (deriv (hurwitzKernel s))).mul hA.measurable
  refine Integrable.mono' ((integrableOn_rpow_majorant hs1).const_mul K)
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs]
  exact hK x hx.1 hx.2

/-- An integrable function on the circle is interval integrable on `[0, 1]` after lifting. -/
lemma intervalIntegrable_of_integrable_circle {F : UnitAddCircle → ℝ} (hF : Integrable F) :
    IntervalIntegrable (fun x : ℝ => F (x : UnitAddCircle)) volume 0 1 := by
  have hmp := AddCircle.measurePreserving_mk (1 : ℝ) 0
  have h := hmp.integrable_comp_of_integrable hF
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have h2 : Integrable (F ∘ QuotientAddGroup.mk) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    simpa using h
  exact h2

/-- The kernel is interval integrable on `[0, 1]`. -/
lemma intervalIntegrable_hurwitzKernel (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    IntervalIntegrable (hurwitzKernel s) volume 0 1 :=
  intervalIntegrable_of_integrable_circle
    ((integrable_hurwitzZetaEven_re s hs0 hs1).const_mul 2)

/-- The product `g A''` is integrable on `(0, 1)` when `A''` is continuous. -/
lemma integrableOn_kernel_mul (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (A2 : ℝ → ℝ)
    (hA2c : Continuous A2) :
    IntegrableOn (fun x => hurwitzKernel s x * A2 x) (Ioo 0 1) := by
  have := (intervalIntegrable_hurwitzKernel s hs0 hs1).mul_continuousOn (g := A2)
    hA2c.continuousOn
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at this
  exact this

/-! ### Shrinking the interval -/

/-- Shrinking the symmetric intervals `[h, 1 - h]` to `[0, 1]` for a function integrable on
`(0, 1)`. -/
lemma tendsto_interval_shrink (F : ℝ → ℝ) (hF : IntegrableOn F (Ioo 0 1)) :
    Tendsto (fun h : ℝ => ∫ x in h..1 - h, F x) (𝓝[>] 0)
      (𝓝 (∫ x in (0 : ℝ)..1, F x)) := by
  set Ft : ℝ → ℝ := (Ioo 0 1).indicator F with hFt_def
  have hFt : Integrable Ft := hF.integrable_indicator measurableSet_Ioo
  have hint : ∫ x in (0 : ℝ)..1, F x = ∫ x, Ft x := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
      hFt_def, integral_indicator measurableSet_Ioo]
  have hrw : ∀ h : ℝ, 0 < h → h < 1 / 2 →
      ∫ x in h..1 - h, F x = ∫ x, (Ioo h (1 - h)).indicator Ft x := by
    intro h h0 h1
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo,
      integral_indicator measurableSet_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    have hx01 : x ∈ Ioo 0 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [hFt_def, indicator_of_mem hx01]
  have hzero : ∀ x ∉ Ioo (0 : ℝ) 1, Ft x = 0 := fun x hx => indicator_of_notMem hx _
  have hbnd : ∀ (h x : ℝ), ‖(Ioo h (1 - h)).indicator Ft x‖ ≤ ‖Ft x‖ :=
    fun h x => norm_indicator_le_norm_self _ _
  have key : Tendsto (fun h : ℝ => ∫ x, (Ioo h (1 - h)).indicator Ft x) (𝓝[>] 0)
      (𝓝 (∫ x, Ft x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖Ft x‖)
      (Eventually.of_forall fun h => (hFt.indicator measurableSet_Ioo).aestronglyMeasurable)
      (Eventually.of_forall fun h => Eventually.of_forall fun x => hbnd h x) hFt.norm
      (Eventually.of_forall fun x => ?_)
    · by_cases hx : x ∈ Ioo (0 : ℝ) 1
      · have hpos : 0 < min x (1 - x) := lt_min hx.1 (by linarith [hx.2])
        have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < min x (1 - x) :=
          nhdsWithin_le_nhds (Iio_mem_nhds hpos)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with h hh
        have hxmem : x ∈ Ioo h (1 - h) :=
          ⟨lt_of_lt_of_le hh (min_le_left _ _),
            by linarith [min_le_right x (1 - x)]⟩
        rw [indicator_of_mem hxmem]
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards with h
        rw [indicator_apply]
        split_ifs
        · rfl
        · exact hzero x hx
  have hfinal := key
  rw [hint]
  refine hfinal.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with h hh
  exact (hrw h hh.1 hh.2).symm

/-! ### Integration by parts -/

/-- Integration by parts for the Riesz kernel against an even one-periodic function `A` with
continuous second derivative: `∫₀¹ g'' A = ∫₀¹ g A''`. -/
theorem integral_deriv_deriv_kernel_mul (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (A A1 A2 : ℝ → ℝ) (M M1 : ℝ)
    (he : ∀ x, A (-x) = A x) (hp : ∀ x, A (x + 1) = A x)
    (hA1 : ∀ x, HasDerivAt A (A1 x) x) (hA2 : ∀ x, HasDerivAt A1 (A2 x) x)
    (hA2c : Continuous A2)
    (hAb : ∀ x, |A x| ≤ M * dist (x : UnitAddCircle) 0 ^ 2)
    (hA1b : ∀ x, |A1 x| ≤ M1 * |x|) :
    ∫ x in (0 : ℝ)..1, deriv (deriv (hurwitzKernel s)) x * A x =
      ∫ x in (0 : ℝ)..1, hurwitzKernel s x * A2 x := by
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun x => (hA1 x).continuousAt
  have hA1c : Continuous A1 := continuous_iff_continuousAt.2 fun x => (hA2 x).continuousAt
  have hA1eq : ∀ x, A1 x = deriv A x := fun x => (hA1 x).deriv.symm
  -- Reflection identities used at the endpoint `1 - h`.
  have hA1odd : ∀ h, A1 (1 - h) = -A1 h := by
    intro h
    rw [hA1eq, hA1eq, deriv_one_sub_of_even_periodic he hp]
  have hAsym : ∀ h, A (1 - h) = A h := one_sub_of_even_periodic he hp
  have hGsym : ∀ h, hurwitzKernel s (1 - h) = hurwitzKernel s h :=
    one_sub_of_even_periodic (hurwitzKernel_neg s) (hurwitzKernel_add_one s)
  have hG1odd : ∀ h, deriv (hurwitzKernel s) (1 - h) = -deriv (hurwitzKernel s) h :=
    deriv_one_sub_of_even_periodic (hurwitzKernel_neg s) (hurwitzKernel_add_one s)
  -- Smoothness of the kernel on `(0, 1)`.
  have hU : IsOpen {x : ℝ | (x : UnitAddCircle) ≠ 0} := by
    have hset : {x : ℝ | (x : UnitAddCircle) ≠ 0} = ⋃ n : ℤ, Ioo (n : ℝ) (n + 1) := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion, mem_Ioo]
      constructor
      · intro hx
        refine ⟨⌊x⌋, lt_of_le_of_ne (Int.floor_le x) fun h => hx ?_, Int.lt_floor_add_one x⟩
        rw [← h]
        exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨⌊x⌋, by simp⟩
      · rintro ⟨n, hn⟩
        exact coe_ne_zero_of_mem_Ioo_int n x ⟨hn.1, hn.2⟩
    rw [hset]
    exact isOpen_iUnion fun n => isOpen_Ioo
  have hGc : ContDiffOn ℝ ∞ (hurwitzKernel s) {x : ℝ | (x : UnitAddCircle) ≠ 0} :=
    contDiffOn_const.mul (contDiffOn_hurwitzZetaEven_re s hs0 hs1)
  have hG1c : ContDiffOn ℝ 1 (deriv (hurwitzKernel s)) {x : ℝ | (x : UnitAddCircle) ≠ 0} :=
    hGc.deriv_of_isOpen hU (m := 1) (by norm_num)
  have hG2cont : ContinuousOn (deriv (deriv (hurwitzKernel s)))
      {x : ℝ | (x : UnitAddCircle) ≠ 0} :=
    (hG1c.deriv_of_isOpen hU (m := 0) (by norm_num)).continuousOn
  have hG1cont : ContinuousOn (deriv (hurwitzKernel s)) {x : ℝ | (x : UnitAddCircle) ≠ 0} :=
    hG1c.continuousOn
  have hGcont : ContinuousOn (hurwitzKernel s) {x : ℝ | (x : UnitAddCircle) ≠ 0} :=
    hGc.continuousOn
  -- The integration by parts identity on `[h, 1 - h]`.
  have hIBP : ∀ h : ℝ, 0 < h → h < 1 / 4 →
      ∫ x in h..1 - h, deriv (deriv (hurwitzKernel s)) x * A x =
        -2 * (deriv (hurwitzKernel s) h * A h - hurwitzKernel s h * A1 h) +
          ∫ x in h..1 - h, hurwitzKernel s x * A2 x := by
    intro h h0 h1
    have hmem : ∀ x ∈ uIcc h (1 - h), 0 < x ∧ x < 1 := by
      intro x hx
      rw [uIcc_of_le (by linarith)] at hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hsub : uIcc h (1 - h) ⊆ {x : ℝ | (x : UnitAddCircle) ≠ 0} := by
      intro x hx
      exact coe_ne_zero_of_mem_Ioo01 (hmem x hx).1 (hmem x hx).2
    have hG1d : ∀ x ∈ uIcc h (1 - h),
        HasDerivAt (deriv (hurwitzKernel s)) (deriv (deriv (hurwitzKernel s)) x) x :=
      fun x hx => hasDerivAt_deriv_hurwitzKernel_of_ne s hs0 hs1 x (hsub hx)
    have hGd : ∀ x ∈ uIcc h (1 - h), HasDerivAt (hurwitzKernel s) (deriv (hurwitzKernel s) x) x :=
      fun x hx => (differentiableAt_hurwitzKernel_of_ne s hs0 hs1 x (hsub hx)).hasDerivAt
    have i1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := h) (b := 1 - h)
      (u := deriv (hurwitzKernel s)) (v := A) (u' := deriv (deriv (hurwitzKernel s)))
      (v' := A1) hG1d (fun x _ => hA1 x)
      (hG2cont.mono hsub |>.intervalIntegrable)
      (hA1c.intervalIntegrable _ _)
    have i2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := h) (b := 1 - h)
      (u := hurwitzKernel s) (v := A1) (u' := deriv (hurwitzKernel s))
      (v' := A2) hGd (fun x _ => hA2 x)
      (hG1cont.mono hsub |>.intervalIntegrable)
      (hA2c.intervalIntegrable _ _)
    rw [hG1odd h, hAsym h] at i1
    rw [hGsym h, hA1odd h] at i2
    linarith
  -- Bounds at `h` and the vanishing of the boundary term as `h → 0⁺`.
  obtain ⟨C1, hC1⟩ := deriv_hurwitzKernel_small s hs0 hs1
  obtain ⟨C0, hC0⟩ := hurwitzKernel_small s hs0 hs1
  have e1 : ∀ h : ℝ, 0 < h → h ^ (-s - 1) * h ^ 2 = h ^ (1 - s) := by
    intro h hh
    rw [← Real.rpow_natCast, ← Real.rpow_add hh]
    congr 1
    push_cast
    ring
  have e2 : ∀ h : ℝ, 0 < h → h ^ (-s) * h = h ^ (1 - s) := by
    intro h hh
    have : h ^ (1 - s) = h ^ (-s) * h ^ (1 : ℝ) := by
      rw [← Real.rpow_add hh]
      congr 1
      ring
    rw [this, Real.rpow_one]
  have hbd : Tendsto (fun h : ℝ => -2 * (deriv (hurwitzKernel s) h * A h -
      hurwitzKernel s h * A1 h)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun h : ℝ => h ^ (1 - s)) (𝓝[>] 0) (𝓝 0) := by
      have h0 := (Real.continuousAt_rpow_const 0 (1 - s) (Or.inr (by linarith))).tendsto
      rw [Real.zero_rpow (by linarith : (0 : ℝ) < 1 - s).ne'] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have hK : Tendsto (fun h : ℝ => 2 * (C1 * |M| + C0 * |M1|) * h ^ (1 - s)) (𝓝[>] 0)
        (𝓝 0) := by
      have := hc.const_mul (2 * (C1 * |M| + C0 * |M1|))
      rwa [mul_zero] at this
    refine squeeze_zero_norm' ?_ hK
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with h hh
    have hd : dist (h : UnitAddCircle) 0 = h :=
      dist_coe_zero_of_mem_Ico hh.1.le (by linarith [hh.2])
    have hAh : |A h| ≤ |M| * h ^ 2 := by
      have := hAb h
      rw [hd] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (sq_nonneg h))
    have hA1h : |A1 h| ≤ |M1| * h := by
      have := hA1b h
      rw [abs_of_pos hh.1] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self M1) hh.1.le)
    have hX : |deriv (hurwitzKernel s) h * A h| ≤ C1 * |M| * h ^ (1 - s) := by
      rw [abs_mul]
      calc |deriv (hurwitzKernel s) h| * |A h|
          ≤ (C1 * h ^ (-s - 1)) * (|M| * h ^ 2) :=
            mul_le_mul (hC1 h hh.1 (by linarith [hh.2])) hAh (abs_nonneg _)
              ((abs_nonneg _).trans (hC1 h hh.1 (by linarith [hh.2])))
        _ = C1 * |M| * (h ^ (-s - 1) * h ^ 2) := by ring
        _ = C1 * |M| * h ^ (1 - s) := by rw [e1 h hh.1]
    have hY : |hurwitzKernel s h * A1 h| ≤ C0 * |M1| * h ^ (1 - s) := by
      rw [abs_mul]
      calc |hurwitzKernel s h| * |A1 h|
          ≤ (C0 * h ^ (-s)) * (|M1| * h) :=
            mul_le_mul (hC0 h hh.1 (by linarith [hh.2])) hA1h (abs_nonneg _)
              ((abs_nonneg _).trans (hC0 h hh.1 (by linarith [hh.2])))
        _ = C0 * |M1| * (h ^ (-s) * h) := by ring
        _ = C0 * |M1| * h ^ (1 - s) := by rw [e2 h hh.1]
    rw [Real.norm_eq_abs]
    calc |-2 * (deriv (hurwitzKernel s) h * A h - hurwitzKernel s h * A1 h)|
        = 2 * |deriv (hurwitzKernel s) h * A h - hurwitzKernel s h * A1 h| := by
          rw [abs_mul]
          norm_num
      _ ≤ 2 * (|deriv (hurwitzKernel s) h * A h| + |hurwitzKernel s h * A1 h|) := by
          gcongr
          exact abs_sub _ _
      _ ≤ 2 * (C1 * |M| * h ^ (1 - s) + C0 * |M1| * h ^ (1 - s)) := by gcongr
      _ = 2 * (C1 * |M| + C0 * |M1|) * h ^ (1 - s) := by ring
  -- Passage to the limit on both sides of the identity.
  have hint1 : IntegrableOn (fun x => deriv (deriv (hurwitzKernel s)) x * A x) (Ioo 0 1) :=
    integrableOn_deriv_deriv_mul s hs0 hs1 A M hAc hAb
  have hint2 : IntegrableOn (fun x => hurwitzKernel s x * A2 x) (Ioo 0 1) :=
    integrableOn_kernel_mul s hs0 hs1 A2 hA2c
  have hT1 := tendsto_interval_shrink _ hint1
  have hT2 := tendsto_interval_shrink _ hint2
  have heq : (fun h : ℝ => ∫ x in h..1 - h, deriv (deriv (hurwitzKernel s)) x * A x) =ᶠ[𝓝[>] 0]
      (fun h : ℝ => -2 * (deriv (hurwitzKernel s) h * A h - hurwitzKernel s h * A1 h) +
        ∫ x in h..1 - h, hurwitzKernel s x * A2 x) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with h hh
    exact hIBP h hh.1 hh.2
  have hsum : Tendsto (fun h : ℝ => ∫ x in h..1 - h, deriv (deriv (hurwitzKernel s)) x * A x)
      (𝓝[>] 0) (𝓝 (0 + ∫ x in (0 : ℝ)..1, hurwitzKernel s x * A2 x)) :=
    ((hbd.add hT2).congr' heq.symm)
  rw [zero_add] at hsum
  exact tendsto_nhds_unique hT1 hsum

end Riesz1

