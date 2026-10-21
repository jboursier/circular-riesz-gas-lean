/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Trigonometric series for the mean-field energy

For a nonnegative coefficient sequence `a : ℤ → ℝ` with `∑ a k` and `∑ k² a k` finite, the
functions
`A(r) = ∑ a k (2 - 2 cos (2π k r))`, `A'(r) = ∑ a k (4π k sin (2π k r))` and
`A''(r) = ∑ a k (8π² k² cos (2π k r))`
are the first and second derivatives of `A`, and they obey the bounds used by the integration
by parts. The series in `A` are the Fourier expansion of the
translation autocorrelation `r ↦ ∫ (ψ(x) - ψ(x - r))²`, computed in
`Riesz1.hasSum_translate_sq`.
-/

public section

open Filter Topology
open scoped Real

namespace Riesz1

/-- The translation series `∑ a k (2 - 2 cos (2π k r))`. -/
@[expose] noncomputable def energySeries (a : ℤ → ℝ) (r : ℝ) : ℝ :=
  ∑' k : ℤ, a k * (2 - 2 * Real.cos (2 * π * k * r))

/-- The first derivative series `∑ a k (4π k sin (2π k r))`. -/
@[expose] noncomputable def energySeries1 (a : ℤ → ℝ) (r : ℝ) : ℝ :=
  ∑' k : ℤ, a k * (4 * π * k * Real.sin (2 * π * k * r))

/-- The second derivative series `∑ a k (8π² k² cos (2π k r))`. -/
@[expose] noncomputable def energySeries2 (a : ℤ → ℝ) (r : ℝ) : ℝ :=
  ∑' k : ℤ, a k * (8 * π ^ 2 * (k : ℝ) ^ 2 * Real.cos (2 * π * k * r))

/-- The summability of `|k| a k`, from those of `a k` and `k² a k`. -/
lemma summable_abs_mul_of_sq {a : ℤ → ℝ} (ha0 : ∀ k, 0 ≤ a k) (ha : Summable a)
    (hM : Summable fun k : ℤ => (k : ℝ) ^ 2 * a k) :
    Summable fun k : ℤ => |(k : ℝ)| * a k := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (ha0 k)) (fun k => ?_)
    ((ha.add hM).mul_left (1 / 2 : ℝ))
  have hk : |(k : ℝ)| ≤ (1 + (k : ℝ) ^ 2) / 2 := by
    nlinarith [sq_abs (k : ℝ), sq_nonneg (|(k : ℝ)| - 1)]
  have h := ha0 k
  nlinarith [mul_le_mul_of_nonneg_right hk h]

/-- The derivative of one term of the translation series. -/
lemma hasDerivAt_term (a : ℤ → ℝ) (k : ℤ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => a k * (2 - 2 * Real.cos (2 * π * k * r)))
      (a k * (4 * π * k * Real.sin (2 * π * k * r))) r := by
  have h1 : HasDerivAt (fun r : ℝ => 2 * π * k * r) (2 * π * k) r := by
    simpa using (hasDerivAt_id r).const_mul (2 * π * (k : ℝ))
  have h2 := ((h1.cos).const_mul (2 : ℝ)).const_sub (2 : ℝ) |>.const_mul (a k)
  convert h2 using 1
  ring

/-- The derivative of one term of the first derivative series. -/
lemma hasDerivAt_term1 (a : ℤ → ℝ) (k : ℤ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => a k * (4 * π * k * Real.sin (2 * π * k * r)))
      (a k * (8 * π ^ 2 * (k : ℝ) ^ 2 * Real.cos (2 * π * k * r))) r := by
  have h1 : HasDerivAt (fun r : ℝ => 2 * π * k * r) (2 * π * k) r := by
    simpa using (hasDerivAt_id r).const_mul (2 * π * (k : ℝ))
  have h2 := ((h1.sin).const_mul (4 * π * (k : ℝ))).const_mul (a k)
  convert h2 using 1
  ring

/-- The series `∑ a k (2 - 2 cos)` is differentiable with derivative `energySeries1`. -/
lemma hasDerivAt_energySeries {a : ℤ → ℝ} (ha0 : ∀ k, 0 ≤ a k) (ha : Summable a)
    (hM : Summable fun k : ℤ => (k : ℝ) ^ 2 * a k) (r : ℝ) :
    HasDerivAt (energySeries a) (energySeries1 a r) r := by
  have hu : Summable fun k : ℤ => a k * (4 * π * |(k : ℝ)|) :=
    (summable_abs_mul_of_sq ha0 ha hM).mul_left (4 * π) |>.congr fun k => by ring
  have hb : ∀ k : ℤ, ∀ y : ℝ, ‖a k * (4 * π * k * Real.sin (2 * π * k * y))‖ ≤
      a k * (4 * π * |(k : ℝ)|) := by
    intro k y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 k)]
    refine mul_le_mul_of_nonneg_left ?_ (ha0 k)
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have := Real.abs_sin_le_one (2 * π * k * y)
    exact mul_le_of_le_one_right (by positivity) this
  have h0 : Summable fun k : ℤ => a k * (2 - 2 * Real.cos (2 * π * k * (0 : ℝ))) :=
    summable_zero.congr fun k => by simp
  have := hasDerivAt_tsum hu (fun k y => hasDerivAt_term a k y)
    (fun k y => hb k y) h0 r
  exact this

/-- The series `energySeries1` is differentiable with derivative `energySeries2`. -/
lemma hasDerivAt_energySeries1 {a : ℤ → ℝ} (ha0 : ∀ k, 0 ≤ a k)
    (hM : Summable fun k : ℤ => (k : ℝ) ^ 2 * a k) (r : ℝ) :
    HasDerivAt (energySeries1 a) (energySeries2 a r) r := by
  have hu : Summable fun k : ℤ => 8 * π ^ 2 * ((k : ℝ) ^ 2 * a k) :=
    hM.mul_left (8 * π ^ 2)
  have hb : ∀ k : ℤ, ∀ y : ℝ, ‖a k * (8 * π ^ 2 * (k : ℝ) ^ 2 * Real.cos (2 * π * k * y))‖ ≤
      8 * π ^ 2 * ((k : ℝ) ^ 2 * a k) := by
    intro k y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 k)]
    have hc := Real.abs_cos_le_one (2 * π * k * y)
    have hpos : 0 ≤ 8 * π ^ 2 * (k : ℝ) ^ 2 := by positivity
    have : |8 * π ^ 2 * (k : ℝ) ^ 2 * Real.cos (2 * π * k * y)| ≤ 8 * π ^ 2 * (k : ℝ) ^ 2 := by
      rw [abs_mul, abs_of_nonneg hpos]
      exact mul_le_of_le_one_right hpos hc
    calc a k * |8 * π ^ 2 * (k : ℝ) ^ 2 * Real.cos (2 * π * k * y)|
        ≤ a k * (8 * π ^ 2 * (k : ℝ) ^ 2) := mul_le_mul_of_nonneg_left this (ha0 k)
      _ = 8 * π ^ 2 * ((k : ℝ) ^ 2 * a k) := by ring
  have h0 : Summable fun k : ℤ => a k * (4 * π * k * Real.sin (2 * π * k * (0 : ℝ))) :=
    summable_zero.congr fun k => by simp
  exact hasDerivAt_tsum hu (fun k y => hasDerivAt_term1 a k y) hb h0 r

/-- The second derivative series is continuous. -/
lemma continuous_energySeries2 {a : ℤ → ℝ} (ha0 : ∀ k, 0 ≤ a k)
    (hM : Summable fun k : ℤ => (k : ℝ) ^ 2 * a k) : Continuous (energySeries2 a) := by
  refine continuous_tsum (fun k => ?_) (hM.mul_left (8 * π ^ 2)) (fun k y => ?_)
  · fun_prop
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 k)]
    have hc := Real.abs_cos_le_one (2 * π * k * y)
    have hpos : 0 ≤ 8 * π ^ 2 * (k : ℝ) ^ 2 := by positivity
    have : |8 * π ^ 2 * (k : ℝ) ^ 2 * Real.cos (2 * π * k * y)| ≤ 8 * π ^ 2 * (k : ℝ) ^ 2 := by
      rw [abs_mul, abs_of_nonneg hpos]
      exact mul_le_of_le_one_right hpos hc
    calc a k * |8 * π ^ 2 * (k : ℝ) ^ 2 * Real.cos (2 * π * k * y)|
        ≤ a k * (8 * π ^ 2 * (k : ℝ) ^ 2) := mul_le_mul_of_nonneg_left this (ha0 k)
      _ = 8 * π ^ 2 * ((k : ℝ) ^ 2 * a k) := by ring

/-- Bound on the first derivative series: `|A'(r)| ≤ 8 π² M |r|`, where
`M = ∑ k² a k`. -/
lemma abs_energySeries1_le {a : ℤ → ℝ} (ha0 : ∀ k, 0 ≤ a k)
    (hM : Summable fun k : ℤ => (k : ℝ) ^ 2 * a k) (r : ℝ) :
    |energySeries1 a r| ≤ 8 * π ^ 2 * (∑' k : ℤ, (k : ℝ) ^ 2 * a k) * |r| := by
  have hterm : ∀ k : ℤ, |a k * (4 * π * k * Real.sin (2 * π * k * r))| ≤
      8 * π ^ 2 * ((k : ℝ) ^ 2 * a k) * |r| := by
    intro k
    rw [abs_mul, abs_of_nonneg (ha0 k)]
    have hs := Real.abs_sin_le_abs (x := 2 * π * k * r)
    have e : |2 * π * (k : ℝ) * r| = 2 * π * |(k : ℝ)| * |r| := by
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    have e2 : |(k : ℝ)| ^ 2 = (k : ℝ) ^ 2 := sq_abs _
    have hpos : 0 ≤ 4 * π * |(k : ℝ)| := by positivity
    have hk : |4 * π * (k : ℝ) * Real.sin (2 * π * k * r)| ≤ 8 * π ^ 2 * (k : ℝ) ^ 2 * |r| := by
      calc |4 * π * (k : ℝ) * Real.sin (2 * π * k * r)|
          = 4 * π * |(k : ℝ)| * |Real.sin (2 * π * k * r)| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
              abs_of_pos Real.pi_pos]
        _ ≤ 4 * π * |(k : ℝ)| * (2 * π * |(k : ℝ)| * |r|) := by
            rw [← e]
            exact mul_le_mul_of_nonneg_left hs hpos
        _ = 8 * π ^ 2 * (k : ℝ) ^ 2 * |r| := by
            rw [← e2]
            ring
    calc a k * |4 * π * (k : ℝ) * Real.sin (2 * π * k * r)|
        ≤ a k * (8 * π ^ 2 * (k : ℝ) ^ 2 * |r|) := mul_le_mul_of_nonneg_left hk (ha0 k)
      _ = 8 * π ^ 2 * ((k : ℝ) ^ 2 * a k) * |r| := by ring
  have hsum : Summable fun k : ℤ => 8 * π ^ 2 * ((k : ℝ) ^ 2 * a k) * |r| :=
    (hM.mul_left (8 * π ^ 2)).mul_right |r|
  have hnorm : Summable fun k : ℤ =>
      ‖a k * (4 * π * k * Real.sin (2 * π * k * r))‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => by rw [Real.norm_eq_abs]; exact hterm k) hsum
  calc |energySeries1 a r| = ‖energySeries1 a r‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' k : ℤ, ‖a k * (4 * π * k * Real.sin (2 * π * k * r))‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℤ, 8 * π ^ 2 * ((k : ℝ) ^ 2 * a k) * |r| :=
        Summable.tsum_le_tsum (fun k => by rw [Real.norm_eq_abs]; exact hterm k) hnorm hsum
    _ = 8 * π ^ 2 * (∑' k : ℤ, (k : ℝ) ^ 2 * a k) * |r| := by
        rw [tsum_mul_right, tsum_mul_left]

/-- The translation series has nonnegative terms. -/
lemma energySeries_nonneg {a : ℤ → ℝ} (ha0 : ∀ k, 0 ≤ a k) (r : ℝ) :
    0 ≤ energySeries a r :=
  tsum_nonneg fun k => mul_nonneg (ha0 k) (by linarith [Real.cos_le_one (2 * π * k * r)])

/-- The translation series is at most `4 π² M r²`, where `M = ∑ k² a k`. -/
lemma energySeries_le {a : ℤ → ℝ} (ha0 : ∀ k, 0 ≤ a k)
    (hM : Summable fun k : ℤ => (k : ℝ) ^ 2 * a k) (r : ℝ) :
    energySeries a r ≤ 4 * π ^ 2 * (∑' k : ℤ, (k : ℝ) ^ 2 * a k) * r ^ 2 := by
  have hterm : ∀ k : ℤ, a k * (2 - 2 * Real.cos (2 * π * k * r)) ≤
      4 * π ^ 2 * ((k : ℝ) ^ 2 * a k) * r ^ 2 := by
    intro k
    have hc := Real.one_sub_sq_div_two_le_cos (x := 2 * π * k * r)
    have h2 : 2 - 2 * Real.cos (2 * π * k * r) ≤ (2 * π * k * r) ^ 2 := by nlinarith
    calc a k * (2 - 2 * Real.cos (2 * π * k * r)) ≤ a k * (2 * π * k * r) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (ha0 k)
      _ = 4 * π ^ 2 * ((k : ℝ) ^ 2 * a k) * r ^ 2 := by ring
  have hsum : Summable fun k : ℤ => 4 * π ^ 2 * ((k : ℝ) ^ 2 * a k) * r ^ 2 :=
    (hM.mul_left (4 * π ^ 2)).mul_right (r ^ 2)
  have hlhs : Summable fun k : ℤ => a k * (2 - 2 * Real.cos (2 * π * k * r)) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (ha0 k) (by linarith [Real.cos_le_one (2 * π * k * r)])) hterm hsum
  unfold energySeries
  calc ∑' k : ℤ, a k * (2 - 2 * Real.cos (2 * π * k * r))
      ≤ ∑' k : ℤ, 4 * π ^ 2 * ((k : ℝ) ^ 2 * a k) * r ^ 2 :=
        Summable.tsum_le_tsum hterm hlhs hsum
    _ = 4 * π ^ 2 * (∑' k : ℤ, (k : ℝ) ^ 2 * a k) * r ^ 2 := by
        rw [tsum_mul_right, tsum_mul_left]

/-- The translation series is invariant under integer shifts. -/
lemma energySeries_add_int (a : ℤ → ℝ) (n : ℤ) (r : ℝ) :
    energySeries a (r + n) = energySeries a r := by
  unfold energySeries
  refine tsum_congr fun k => ?_
  have h : 2 * π * k * (r + n) = 2 * π * k * r + ((k * n : ℤ) : ℝ) * (2 * π) := by
    push_cast
    ring
  rw [h, Real.cos_add_int_mul_two_pi]

/-- The translation series is even. -/
lemma energySeries_neg (a : ℤ → ℝ) (r : ℝ) : energySeries a (-r) = energySeries a r := by
  unfold energySeries
  refine tsum_congr fun k => ?_
  have h : 2 * π * k * (-r) = -(2 * π * k * r) := by ring
  rw [h, Real.cos_neg]

/-- The translation series at a point, reduced to the distance to the integers: this is the
bound `|A(x)| ≤ 4 π² M dist(x, ℤ)²` used in the integration by parts. -/
lemma abs_energySeries_le_sub_round {a : ℤ → ℝ} (ha0 : ∀ k, 0 ≤ a k)
    (hM : Summable fun k : ℤ => (k : ℝ) ^ 2 * a k) (x : ℝ) :
    |energySeries a x| ≤ 4 * π ^ 2 * (∑' k : ℤ, (k : ℝ) ^ 2 * a k) * (x - round x) ^ 2 := by
  have h1 : energySeries a (x - round x) = energySeries a x := by
    have := energySeries_add_int a (-round x) x
    rw [Int.cast_neg, ← sub_eq_add_neg] at this
    exact this
  rw [← h1, abs_of_nonneg (energySeries_nonneg ha0 _)]
  exact energySeries_le ha0 hM _

end Riesz1
