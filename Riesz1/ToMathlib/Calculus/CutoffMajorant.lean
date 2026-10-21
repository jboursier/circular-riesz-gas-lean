/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The majorant of the derivative of the exterior kernel

Lemma 5.2, exterior tail. The derivative bound of the kernel `f` is
`|f'(u)| ≤ 1_{|u| ≤ 2} / max(|u|, K⁻¹)^{1+λ} + 1_{|u| ≥ 2} / |u|^{3-s}`. The function
`cutoffMajorant` is this bound as a function of the distance `t = |u|`, with both indicators closed.
It is the sum of `majorantNear` (the first summand) and `majorantFar` (the second summand).

The file proves the integral estimates needed by the exterior tail:
* `integral_cutoffMajorant_le`: for `K ≥ 1`, `λ ≥ 0`, `ε > 0` and `c ≥ 0`, the integral over
  `[0, c]` is at most `M K^{λ+ε}`, where `M` depends on `s, λ, ε` only.
* `integral_cutoffMajorant_tail`: for `2 ≤ r ≤ c`, the integral over `[r, c]` is at most
  `r^{s-2}/(2-s)`.
* `integral_cutoffMajorant_tail_le`: for `0 ≤ r ≤ c`, the integral over `[r, c]` is at most the
  integral over `[0, c]`.
-/

@[expose] public section

open MeasureTheory Set

namespace Riesz1

/-- The first summand of the majorant: `max(t, K⁻¹)^{-(1+λ)}` for `t ≤ 2`, and `0` otherwise. -/
noncomputable def majorantNear (lam K t : ℝ) : ℝ :=
  if t ≤ 2 then 1 / (max t K⁻¹) ^ (1 + lam) else 0

/-- The second summand of the majorant: `t^{s-3}` for `2 ≤ t`, and `0` otherwise. -/
noncomputable def majorantFar (s t : ℝ) : ℝ :=
  if 2 ≤ t then 1 / t ^ (3 - s) else 0

/-- The majorant of `|f'|` at distance `t` from the origin, a sum of the two closed summands. -/
noncomputable def cutoffMajorant (s lam K t : ℝ) : ℝ :=
  majorantNear lam K t + majorantFar s t

/-! ### Elementary bounds -/

/-- Nonnegativity of the first summand, when `K > 0`. -/
theorem majorantNear_nonneg {lam K : ℝ} (hK : 0 < K) (t : ℝ) : 0 ≤ majorantNear lam K t := by
  unfold majorantNear
  split_ifs
  · exact div_nonneg zero_le_one (Real.rpow_nonneg (le_max_of_le_right (inv_pos.mpr hK).le) _)
  · exact le_rfl

/-- Nonnegativity of the second summand. -/
theorem majorantFar_nonneg (s t : ℝ) : 0 ≤ majorantFar s t := by
  unfold majorantFar
  split_ifs with h
  · exact div_nonneg zero_le_one (Real.rpow_nonneg (by linarith) _)
  · exact le_rfl

/-- Nonnegativity of the majorant, when `K > 0`. -/
theorem cutoffMajorant_nonneg {s lam K : ℝ} (hK : 0 < K) (t : ℝ) :
    0 ≤ cutoffMajorant s lam K t :=
  add_nonneg (majorantNear_nonneg hK t) (majorantFar_nonneg s t)

/-- The first summand is at most `K^{1+λ}` when `K ≥ 1`. -/
theorem majorantNear_le {lam K : ℝ} (hK : 1 ≤ K) (hlam : 0 ≤ lam) (t : ℝ) :
    majorantNear lam K t ≤ K ^ (1 + lam) := by
  have hK0 : 0 < K := by linarith
  unfold majorantNear
  split_ifs
  · have hmax : (K⁻¹) ^ (1 + lam) ≤ (max t K⁻¹) ^ (1 + lam) :=
      Real.rpow_le_rpow (inv_pos.mpr hK0).le (le_max_right _ _) (by linarith)
    rw [Real.inv_rpow hK0.le] at hmax
    have hpos : 0 < (K ^ (1 + lam))⁻¹ := by positivity
    calc 1 / (max t K⁻¹) ^ (1 + lam) ≤ 1 / (K ^ (1 + lam))⁻¹ :=
          one_div_le_one_div_of_le hpos hmax
      _ = K ^ (1 + lam) := by rw [one_div, inv_inv]
  · exact Real.rpow_nonneg hK0.le _

/-- The second summand is at most one when `s < 3`. -/
theorem majorantFar_le_one {s : ℝ} (hs : s < 3) (t : ℝ) : majorantFar s t ≤ 1 := by
  unfold majorantFar
  split_ifs with h
  · have hp : 1 ≤ t ^ (3 - s) := Real.one_le_rpow (by linarith) (by linarith)
    exact (one_div_le_one_div_of_le zero_lt_one hp).trans_eq one_div_one
  · exact zero_le_one

/-- Reciprocal power: `1 / t^{3-s} = t^{s-3}` for `t > 0`. -/
theorem one_div_rpow_eq {t s : ℝ} (ht : 0 < t) : 1 / t ^ (3 - s) = t ^ (s - 3) := by
  rw [one_div, ← Real.rpow_neg ht.le]
  congr 1
  ring

/-- Comparison of a power with a shifted power: if `z/2 ≤ x` with `z > 0` and `b ≥ 0`, then
`x^{-b} ≤ 2^b z^{-b}`. -/
theorem rpow_neg_le_two_pow_mul {x z b : ℝ} (hz : 0 < z) (hxz : z / 2 ≤ x) (hb : 0 ≤ b) :
    x ^ (-b) ≤ 2 ^ b * z ^ (-b) := by
  have hx : 0 < z / 2 := by linarith
  have h1 : x ^ (-b) ≤ (z / 2) ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos hx hxz (by linarith)
  have h2 : (z / 2) ^ (-b) = 2 ^ b * z ^ (-b) := by
    rw [Real.div_rpow hz.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul, mul_comm]
  linarith

/-! ### Pointwise bounds by power functions -/

/-- The first summand is dominated by a shifted power, for `t ≥ 0`, `K ≥ 1` and `ε > 0`. -/
theorem majorantNear_le_shift {lam K ε t : ℝ} (hK : 1 ≤ K) (hlam : 0 ≤ lam) (hε : 0 < ε)
    (ht : 0 ≤ t) :
    majorantNear lam K t ≤ 2 ^ (ε + (1 + lam + ε)) * (t + K⁻¹) ^ (-(1 + lam + ε)) := by
  have hK0 : 0 < K := by linarith
  have hδ0 : 0 < K⁻¹ := inv_pos.mpr hK0
  have hδ1 : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
  have hzpos : 0 < t + K⁻¹ := by linarith
  unfold majorantNear
  split_ifs with h
  · have hy0 : 0 < max t K⁻¹ := lt_max_of_lt_right hδ0
    have hy2 : max t K⁻¹ ≤ 2 := max_le h (by linarith)
    have hyz : (t + K⁻¹) / 2 ≤ max t K⁻¹ := by
      linarith [le_max_left t K⁻¹, le_max_right t K⁻¹]
    have hsplit : (max t K⁻¹) ^ (-(1 + lam)) =
        (max t K⁻¹) ^ (-(1 + lam + ε)) * (max t K⁻¹) ^ ε := by
      rw [← Real.rpow_add hy0]
      congr 1
      ring
    have hε2 : (max t K⁻¹) ^ ε ≤ 2 ^ ε := Real.rpow_le_rpow hy0.le hy2 hε.le
    have hneg : (max t K⁻¹) ^ (-(1 + lam + ε)) ≤
        2 ^ (1 + lam + ε) * (t + K⁻¹) ^ (-(1 + lam + ε)) :=
      rpow_neg_le_two_pow_mul hzpos hyz (by linarith)
    have hyε : 0 ≤ (max t K⁻¹) ^ ε := Real.rpow_nonneg hy0.le _
    have hcomb : (max t K⁻¹) ^ (-(1 + lam)) ≤
        2 ^ (1 + lam + ε) * (t + K⁻¹) ^ (-(1 + lam + ε)) * 2 ^ ε := by
      rw [hsplit]
      exact mul_le_mul hneg hε2 hyε (by positivity)
    have hfin : 2 ^ (1 + lam + ε) * (t + K⁻¹) ^ (-(1 + lam + ε)) * 2 ^ ε =
        2 ^ (ε + (1 + lam + ε)) * (t + K⁻¹) ^ (-(1 + lam + ε)) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2) ε (1 + lam + ε)]
      ring
    calc 1 / (max t K⁻¹) ^ (1 + lam) = (max t K⁻¹) ^ (-(1 + lam)) := by
          rw [Real.rpow_neg hy0.le, one_div]
      _ ≤ 2 ^ (1 + lam + ε) * (t + K⁻¹) ^ (-(1 + lam + ε)) * 2 ^ ε := hcomb
      _ = 2 ^ (ε + (1 + lam + ε)) * (t + K⁻¹) ^ (-(1 + lam + ε)) := hfin
  · positivity

/-- The second summand is dominated by a shifted power, for `t ≥ 0` and `s < 2`. -/
theorem majorantFar_le_shift {s t : ℝ} (hs : s < 2) (ht : 0 ≤ t) :
    majorantFar s t ≤ 2 ^ (3 - s) * (t + 1) ^ (-(3 - s)) := by
  unfold majorantFar
  split_ifs with h
  · have ht1 : 1 ≤ t := by linarith
    have ht0 : 0 < t := by linarith
    rw [one_div_rpow_eq ht0]
    have hz : 0 < t + 1 := by linarith
    have h2 : t ^ (-(3 - s)) ≤ 2 ^ (3 - s) * (t + 1) ^ (-(3 - s)) :=
      rpow_neg_le_two_pow_mul hz (by linarith) (by linarith)
    rw [show s - 3 = -(3 - s) by ring]
    exact h2
  · have hz : 0 < t + 1 := by linarith
    have : 0 ≤ 2 ^ (3 - s) * (t + 1) ^ (-(3 - s)) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg hz.le _)
    exact this

/-! ### Measurability and integrability -/

/-- The first summand is measurable. -/
theorem measurable_majorantNear (lam K : ℝ) : Measurable (majorantNear lam K) := by
  unfold majorantNear
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) ?_ measurable_const
  fun_prop

/-- The second summand is measurable. -/
theorem measurable_majorantFar (s : ℝ) : Measurable (majorantFar s) := by
  unfold majorantFar
  refine Measurable.ite (measurableSet_le measurable_const measurable_id) ?_ measurable_const
  fun_prop

/-- A measurable function bounded by a constant is interval integrable. -/
theorem intervalIntegrable_of_bounded {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ t, |g t| ≤ M) (a b : ℝ) : IntervalIntegrable g volume a b :=
  IntervalIntegrable.mono_fun' (g := fun _ => M) intervalIntegrable_const
    hg.aestronglyMeasurable (ae_of_all _ fun t => by simpa [Real.norm_eq_abs] using hM t)

/-- The first summand is interval integrable on every interval, when `K ≥ 1`. -/
theorem majorantNear_intervalIntegrable {lam K : ℝ} (hK : 1 ≤ K) (hlam : 0 ≤ lam) (a b : ℝ) :
    IntervalIntegrable (majorantNear lam K) volume a b := by
  refine intervalIntegrable_of_bounded (measurable_majorantNear lam K) (M := K ^ (1 + lam))
    (fun t => ?_) a b
  rw [abs_of_nonneg (majorantNear_nonneg (by linarith) t)]
  exact majorantNear_le hK hlam t

/-- The second summand is interval integrable on every interval, when `s < 3`. -/
theorem majorantFar_intervalIntegrable {s : ℝ} (hs : s < 3) (a b : ℝ) :
    IntervalIntegrable (majorantFar s) volume a b := by
  refine intervalIntegrable_of_bounded (measurable_majorantFar s) (M := 1) (fun t => ?_) a b
  have h0 : 0 ≤ majorantFar s t := by
    unfold majorantFar
    split_ifs with h
    · exact div_nonneg zero_le_one (Real.rpow_nonneg (by linarith) _)
    · exact le_rfl
  rw [abs_of_nonneg h0]
  exact majorantFar_le_one hs t

/-- The majorant is interval integrable on every interval, when `K ≥ 1` and `s < 2`. -/
theorem cutoffMajorant_intervalIntegrable {s lam K : ℝ} (hs : s < 2) (hK : 1 ≤ K)
    (hlam : 0 ≤ lam) (a b : ℝ) : IntervalIntegrable (cutoffMajorant s lam K) volume a b :=
  (majorantNear_intervalIntegrable hK hlam a b).add (majorantFar_intervalIntegrable (by linarith) a b)

/-! ### Integral estimates -/

/-- Power-shift comparison: `∫_0^c (t + a)^{-b} dt ≤ a^{1-b}/(b-1)` for `a > 0`, `b > 1`, `c ≥ 0`. -/
theorem integral_add_rpow_neg_le {a b c : ℝ} (ha : 0 < a) (hb : 1 < b) (hc : 0 ≤ c) :
    ∫ t in (0 : ℝ)..c, (t + a) ^ (-b) ≤ a ^ (1 - b) / (b - 1) := by
  have hshift : ∫ t in (0 : ℝ)..c, (t + a) ^ (-b) = ∫ x in a..(c + a), x ^ (-b) := by
    have h := intervalIntegral.integral_comp_add_right (a := 0) (b := c)
      (fun x : ℝ => x ^ (-b)) a
    simpa using h
  have hzero : (0 : ℝ) ∉ uIcc a (c + a) := by
    intro h
    rw [Set.mem_uIcc] at h
    rcases h with h | h <;> linarith
  rw [hshift, integral_rpow (Or.inr ⟨by linarith, hzero⟩)]
  have hb1 : 0 < b - 1 := by linarith
  have hnn : 0 ≤ (c + a) ^ (-(b - 1)) := Real.rpow_nonneg (by linarith) _
  rw [show -b + 1 = -(b - 1) by ring, show 1 - b = -(b - 1) by ring, div_neg, ← neg_div,
    div_le_div_iff_of_pos_right hb1]
  linarith

/-- The first summand integrates to at most `2^{1+λ+2ε}/(λ+ε) · K^{λ+ε}` over `[0, c]`. -/
theorem integral_majorantNear_le {lam K ε c : ℝ} (hK : 1 ≤ K) (hlam : 0 ≤ lam) (hε : 0 < ε)
    (hc : 0 ≤ c) :
    ∫ t in (0 : ℝ)..c, majorantNear lam K t ≤
      2 ^ (ε + (1 + lam + ε)) / (lam + ε) * K ^ (lam + ε) := by
  have hK0 : 0 < K := by linarith
  have hδ : 0 < K⁻¹ := inv_pos.mpr hK0
  have hb1 : 1 < 1 + lam + ε := by linarith
  have hint2 : IntervalIntegrable (fun t : ℝ => 2 ^ (ε + (1 + lam + ε)) *
      (t + K⁻¹) ^ (-(1 + lam + ε))) volume 0 c := by
    refine IntervalIntegrable.const_mul ?_ _
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.rpow_const (by fun_prop) (fun x hx => Or.inl ?_)
    have : (0 : ℝ) ≤ x := by
      rw [uIcc_of_le hc] at hx
      exact hx.1
    linarith
  have hmono : ∫ t in (0 : ℝ)..c, majorantNear lam K t ≤
      ∫ t in (0 : ℝ)..c, 2 ^ (ε + (1 + lam + ε)) * (t + K⁻¹) ^ (-(1 + lam + ε)) :=
    intervalIntegral.integral_mono_on hc (majorantNear_intervalIntegrable hK hlam 0 c) hint2
      (fun t ht => majorantNear_le_shift hK hlam hε ht.1)
  rw [intervalIntegral.integral_const_mul] at hmono
  have hbound := integral_add_rpow_neg_le (a := K⁻¹) (b := 1 + lam + ε) hδ hb1 hc
  have hpow : (K⁻¹) ^ (1 - (1 + lam + ε)) = K ^ (lam + ε) := by
    rw [show 1 - (1 + lam + ε) = -(lam + ε) by ring, Real.rpow_neg (inv_pos.mpr hK0).le,
      Real.inv_rpow hK0.le, inv_inv]
  rw [hpow, show 1 + lam + ε - 1 = lam + ε by ring] at hbound
  have hcoef : (0 : ℝ) ≤ 2 ^ (ε + (1 + lam + ε)) := by positivity
  calc ∫ t in (0 : ℝ)..c, majorantNear lam K t
      ≤ 2 ^ (ε + (1 + lam + ε)) * ∫ t in (0 : ℝ)..c, (t + K⁻¹) ^ (-(1 + lam + ε)) := hmono
    _ ≤ 2 ^ (ε + (1 + lam + ε)) * (K ^ (lam + ε) / (lam + ε)) :=
        mul_le_mul_of_nonneg_left hbound hcoef
    _ = 2 ^ (ε + (1 + lam + ε)) / (lam + ε) * K ^ (lam + ε) := by ring

/-- The second summand integrates to at most `2^{3-s}/(2-s)` over `[0, c]`. -/
theorem integral_majorantFar_le {s c : ℝ} (hs : s < 2) (hc : 0 ≤ c) :
    ∫ t in (0 : ℝ)..c, majorantFar s t ≤ 2 ^ (3 - s) / (2 - s) := by
  have hint2 : IntervalIntegrable (fun t : ℝ => 2 ^ (3 - s) * (t + 1) ^ (-(3 - s))) volume 0 c := by
    refine IntervalIntegrable.const_mul ?_ _
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.rpow_const (by fun_prop) (fun x hx => Or.inl ?_)
    have : (0 : ℝ) ≤ x := by
      rw [uIcc_of_le hc] at hx
      exact hx.1
    linarith
  have hmono : ∫ t in (0 : ℝ)..c, majorantFar s t ≤
      ∫ t in (0 : ℝ)..c, 2 ^ (3 - s) * (t + 1) ^ (-(3 - s)) :=
    intervalIntegral.integral_mono_on hc (majorantFar_intervalIntegrable (by linarith) 0 c) hint2
      (fun t ht => majorantFar_le_shift hs ht.1)
  rw [intervalIntegral.integral_const_mul] at hmono
  have hbound := integral_add_rpow_neg_le (a := 1) (b := 3 - s) one_pos (by linarith) hc
  rw [Real.one_rpow, show 3 - s - 1 = 2 - s by ring, one_div] at hbound
  calc ∫ t in (0 : ℝ)..c, majorantFar s t
      ≤ 2 ^ (3 - s) * ∫ t in (0 : ℝ)..c, (t + 1) ^ (-(3 - s)) := hmono
    _ ≤ 2 ^ (3 - s) * (1 / (2 - s)) :=
        mul_le_mul_of_nonneg_left (by simpa [div_eq_mul_inv, one_mul] using hbound) (by positivity)
    _ = 2 ^ (3 - s) / (2 - s) := by ring

/-- **Integral of the majorant near the origin.** For `K ≥ 1`, `λ ≥ 0`, `ε > 0` and `c ≥ 0`, the
integral of the majorant over `[0, c]` is at most `M K^{λ+ε}`, where `M` depends on `s, λ, ε`. -/
theorem integral_cutoffMajorant_le {s lam K ε c : ℝ} (hs : s < 2) (hK : 1 ≤ K) (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hc : 0 ≤ c) :
    ∫ t in (0 : ℝ)..c, cutoffMajorant s lam K t ≤
      (2 ^ (ε + (1 + lam + ε)) / (lam + ε) + 2 ^ (3 - s) / (2 - s)) * K ^ (lam + ε) := by
  have hK1 : 1 ≤ K ^ (lam + ε) := Real.one_le_rpow hK (by linarith)
  have hsplit : ∫ t in (0 : ℝ)..c, cutoffMajorant s lam K t =
      (∫ t in (0 : ℝ)..c, majorantNear lam K t) + ∫ t in (0 : ℝ)..c, majorantFar s t :=
    intervalIntegral.integral_add (majorantNear_intervalIntegrable hK hlam 0 c)
      (majorantFar_intervalIntegrable (by linarith) 0 c)
  have h1 := integral_majorantNear_le hK hlam hε hc
  have h2 := integral_majorantFar_le hs hc
  have h3 : 2 ^ (3 - s) / (2 - s) ≤ 2 ^ (3 - s) / (2 - s) * K ^ (lam + ε) :=
    le_mul_of_one_le_right (by positivity) hK1
  rw [hsplit, add_mul]
  linarith

/-- **Integral of the majorant beyond distance two.** For `2 ≤ r ≤ c` and `s < 2`, the integral of
the majorant over `[r, c]` is at most `r^{s-2}/(2-s)`. -/
theorem integral_cutoffMajorant_tail {s lam K r c : ℝ} (hs : s < 2) (hr : 2 ≤ r) (hrc : r ≤ c) :
    ∫ t in r..c, cutoffMajorant s lam K t ≤ r ^ (s - 2) / (2 - s) := by
  have hcongr : ∫ t in r..c, cutoffMajorant s lam K t = ∫ t in r..c, t ^ (s - 3) := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
    rw [uIoc_of_le hrc] at ht
    have ht2 : 2 < t := lt_of_le_of_lt hr ht.1
    unfold cutoffMajorant majorantNear majorantFar
    simp only [not_le.mpr ht2, ht2.le, ↓reduceIte, zero_add]
    exact one_div_rpow_eq (by linarith)
  have hzero : (0 : ℝ) ∉ uIcc r c := by
    intro h
    rw [Set.mem_uIcc] at h
    rcases h with h | h <;> linarith
  rw [hcongr, integral_rpow (Or.inr ⟨by intro h; linarith, hzero⟩)]
  have hc0 : 0 ≤ c ^ (-(2 - s)) := Real.rpow_nonneg (by linarith) _
  have he : 0 < 2 - s := by linarith
  rw [show s - 3 + 1 = -(2 - s) by ring, show s - 2 = -(2 - s) by ring, div_neg, ← neg_div,
    div_le_div_iff_of_pos_right he]
  linarith

/-- **Majorant integral is monotone in the lower endpoint.** For `0 ≤ r ≤ c`, the integral of the
majorant over `[r, c]` is at most its integral over `[0, c]`. -/
theorem integral_cutoffMajorant_tail_le {s lam K r c : ℝ} (hs : s < 2) (hK : 1 ≤ K)
    (hlam : 0 ≤ lam) (hr : 0 ≤ r) :
    ∫ t in r..c, cutoffMajorant s lam K t ≤ ∫ t in (0 : ℝ)..c, cutoffMajorant s lam K t := by
  have hK0 : 0 < K := by linarith
  have hint : ∀ a b : ℝ, IntervalIntegrable (cutoffMajorant s lam K) volume a b := fun a b =>
    (majorantNear_intervalIntegrable hK hlam a b).add (majorantFar_intervalIntegrable (by linarith) a b)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint 0 r) (hint r c)
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..r, cutoffMajorant s lam K t :=
    intervalIntegral.integral_nonneg hr fun u _ => cutoffMajorant_nonneg hK0 u
  linarith

end Riesz1

end
