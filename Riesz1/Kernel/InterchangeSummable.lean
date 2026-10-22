/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.InterchangeBound
public import Riesz1.ToMathlib.HeatKernel.Circle
public import Mathlib.Analysis.PSeries
public import Mathlib.Tactic

/-!
# Absolute summability of the interchange integrals

The interchange integrals `∑_k ∫_{(0,∞)} |u_k^x(t)| dt` are summable for `0 < x < 1`. The time
axis is split at `t = 1`.

* On `(0, 1]` the sum over `k` is taken first. The Gaussian averages sum to the heat kernel times
  `√(4πt)`, and the Gaussians of the points at distance at least `min(x, 1-x)` from the origin
  are exponentially small in `1/t`. The power `t^{-1-s/2}` is integrable against this decay.
* On `[1, ∞)` the sum over `k` is again taken first. The pointwise bound
  `|u_k^x(t)| ≤ t^{-1-s/2} (|k|+1)/(2t) e^{-k²/(16t)}` for `|k| ≥ 2` and the crude bound for
  `|k| ≤ 1` give a weighted Gaussian lattice sum, which is at most a constant times `t^p` with
  `p = 1 + s/4`. The power `t^{-2-s/2} t^p` is integrable on `[1, ∞)`.

Main results:
* `Riesz1.abs_interchangeTerm_le`: the pointwise bound for `|k| ≥ 2`.
* `Riesz1.summable_integral_abs_interchangeTerm`: `∑_k ∫_{(0,∞)} |u_k^x(t)| dt` converges.
-/

public section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- For `|k| ≥ 2`, `|u_k^x(t)| ≤ t^{-1-s/2} · (|k|+1)/(2t) · e^{-k²/(16t)}` for every `t > 0`. -/
lemma abs_interchangeTerm_le {s x : ℝ} (k : ℤ) (hk : 2 ≤ |(k : ℝ)|) (hx0 : 0 < x) (hx1 : x < 1)
    {t : ℝ} (ht : 0 < t) :
    |interchangeTerm s x k t| ≤
      t ^ (-1 - s / 2) * ((|(k : ℝ)| + 1) / (2 * t) * Real.exp (-((k : ℝ) ^ 2 / (16 * t)))) := by
  have hpow : 0 ≤ t ^ (-1 - s / 2) := Real.rpow_nonneg ht.le _
  rw [show interchangeTerm s x k t = t ^ (-1 - s / 2) *
      (Real.exp (-(x - k) ^ 2 / (4 * t)) - gaussAverage k t) from rfl]
  -- The average of the Gaussian differences over `[0, 1]` is bounded pointwise.
  have hdiff : |Real.exp (-(x - k) ^ 2 / (4 * t)) - gaussAverage k t| ≤
      (|(k : ℝ)| + 1) / (2 * t) * Real.exp (-((k : ℝ) ^ 2 / (16 * t))) := by
    have hrepr : Real.exp (-(x - k) ^ 2 / (4 * t)) - gaussAverage k t =
        ∫ y in (0 : ℝ)..1, (Real.exp (-(x - k) ^ 2 / (4 * t)) -
          Real.exp (-(y - k) ^ 2 / (4 * t))) := by
      simp only [gaussAverage]
      rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable 0 1)
        ((continuous_gauss_shift k t).intervalIntegrable 0 1)]
      simp
    rw [hrepr]
    have hC := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1)
      (C := (|(k : ℝ)| + 1) / (2 * t) * Real.exp (-((k : ℝ) ^ 2 / (16 * t))))
      (f := fun y : ℝ => Real.exp (-(x - k) ^ 2 / (4 * t)) -
        Real.exp (-(y - k) ^ 2 / (4 * t))) (fun y hy => by
        rw [uIoc_of_le zero_le_one] at hy
        rw [Real.norm_eq_abs]
        exact abs_gauss_sub_gauss_le ht k hk hx0.le hx1.le hy.1.le hy.2)
    rw [Real.norm_eq_abs] at hC
    simpa using hC
  rw [abs_mul, abs_of_nonneg hpow]
  exact mul_le_mul_of_nonneg_left hdiff hpow

/-- The Gaussian periodization is the heat kernel times `√(4πt)`:
`∑_n e^{-(y-n)²/(4t)} = (4πt)^{1/2} W_t(y)`. -/
lemma tsum_gauss_eq_rpow_mul_heat {t : ℝ} (ht : 0 < t) (y : ℝ) :
    ∑' n : ℤ, Real.exp (-(y - n) ^ 2 / (4 * t)) =
      (4 * Real.pi * t) ^ (1 / 2 : ℝ) * circleHeatKernel t ht y := by
  rw [circleHeatKernel_eq_gauss t ht y, ← mul_assoc, ← Real.rpow_add (by positivity)]
  norm_num

/-- The Gaussian averages over `[0, 1]` have partial sums at most `√(4πt)`. -/
lemma sum_gaussAverage_le {t : ℝ} (ht : 0 < t) (u : Finset ℤ) :
    ∑ k ∈ u, gaussAverage k t ≤ Real.sqrt (4 * Real.pi * t) := by
  have hcont : ∀ k : ℤ, Continuous fun y : ℝ => Real.exp (-(y - k) ^ 2 / (4 * t)) :=
    fun k => by fun_prop
  have hsum : Continuous fun y : ℝ => ∑ k ∈ u, Real.exp (-(y - k) ^ 2 / (4 * t)) :=
    continuous_finsetSum u fun k _ => hcont k
  have hmono : ∫ y in (0 : ℝ)..1, ∑ k ∈ u, Real.exp (-(y - k) ^ 2 / (4 * t)) ≤
      ∫ y in (0 : ℝ)..1, (4 * Real.pi * t) ^ (1 / 2 : ℝ) * circleHeatKernel t ht y := by
    refine intervalIntegral.integral_mono_on zero_le_one
      (hsum.intervalIntegrable 0 1)
      (((continuous_circleHeatKernel t ht).const_mul _).intervalIntegrable 0 1) (fun y _ => ?_)
    rw [← tsum_gauss_eq_rpow_mul_heat ht y]
    exact (summable_gauss_int t ht y).sum_le_tsum u (fun k _ => (Real.exp_pos _).le)
  rw [intervalIntegral.integral_finsetSum (fun k _ => (hcont k).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral_circleHeatKernel, mul_one] at hmono
  rw [Real.sqrt_eq_rpow]
  exact hmono

/-- The distance from `x ∈ (0, 1)` to every integer `k` is at least `min(x, 1-x)`. -/
lemma min_le_abs_sub_int {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (k : ℤ) :
    min x (1 - x) ≤ |x - k| := by
  rcases le_or_gt k 0 with h | h
  · have hk : (k : ℝ) ≤ 0 := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith [min_le_left x (1 - x)]
  · have hk : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
    rw [abs_of_nonpos (by linarith)]
    linarith [min_le_right x (1 - x)]

/-- The Gaussian at distance at least `min(x, 1-x)` decays at least like `e^{-δ²/(8t)}` for
`t ≤ 1`, times a Gaussian of width `2` that does not depend on `t`. -/
lemma exp_gauss_le_exp_mul {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) (k : ℤ) :
    Real.exp (-(x - k) ^ 2 / (4 * t)) ≤
      Real.exp (-(min x (1 - x)) ^ 2 / (8 * t)) * Real.exp (-(x - k) ^ 2 / (4 * 2)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have hd : (min x (1 - x)) ^ 2 ≤ (x - k) ^ 2 := by
    have h := min_le_abs_sub_int hx0 hx1 k
    have hm : 0 ≤ min x (1 - x) := le_min hx0.le (by linarith)
    nlinarith [sq_abs (x - (k : ℝ))]
  have h1 : (min x (1 - x)) ^ 2 / (8 * t) ≤ (x - k) ^ 2 / (8 * t) :=
    div_le_div_of_nonneg_right hd (by positivity)
  have h2 : (x - k) ^ 2 / 8 ≤ (x - k) ^ 2 / (8 * t) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
  have h3 : -(x - k) ^ 2 / (4 * t) = -((x - k) ^ 2 / (8 * t)) + -((x - k) ^ 2 / (8 * t)) := by
    field_simp
    ring
  have h4 : -(x - k) ^ 2 / (4 * 2) = -((x - k) ^ 2 / 8) := by
    rw [neg_div]
    norm_num
  have h5 : -(min x (1 - x)) ^ 2 / (8 * t) = -((min x (1 - x)) ^ 2 / (8 * t)) := by
    rw [neg_div]
  rw [h3, h4, h5]
  linarith [h1, h2]

/-- The sum over `k` of the Gaussian weights `e^{-(x-k)²/8}` is finite. -/
lemma summable_gauss_width_two (x : ℝ) :
    Summable (fun k : ℤ => Real.exp (-(x - k) ^ 2 / (4 * 2))) :=
  summable_gauss_int 2 two_pos x


/-- The bound `e^{-y} y^p ≤ m!` for `y > 0`, where `1 ≤ p ≤ m`. -/
lemma exp_neg_mul_rpow_le {p : ℝ} {m : ℕ} (hp : 1 ≤ p) (hpm : p ≤ m) {y : ℝ} (hy : 0 < y) :
    Real.exp (-y) * y ^ p ≤ (m.factorial : ℝ) := by
  have hm1 : (1 : ℝ) ≤ (m.factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero m)
  rcases le_total y 1 with h | h
  · have h1 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h2 : y ^ p ≤ 1 := Real.rpow_le_one hy.le h (by linarith)
    have h3 : 0 ≤ y ^ p := Real.rpow_nonneg hy.le p
    have h4 : 0 ≤ Real.exp (-y) := (Real.exp_pos _).le
    nlinarith
  · have h1 : y ^ p ≤ y ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le h hpm
    rw [Real.rpow_natCast] at h1
    have h2 : y ^ m / (m.factorial : ℝ) ≤ Real.exp y := Real.pow_div_factorial_le_exp y hy.le m
    have h3 : y ^ m ≤ Real.exp y * (m.factorial : ℝ) := by
      rw [div_le_iff₀ (by positivity)] at h2
      linarith
    have h4 : Real.exp (-y) * y ^ m ≤ (m.factorial : ℝ) := by
      rw [Real.exp_neg, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos y)]
      linarith
    exact (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le).trans h4

/-- The weighted Gaussian lattice sums `∑_{k ∈ u} (|k|+1) e^{-k²/(16t)}` are bounded by a
constant times `t^p` for `t ≥ 1`, uniformly in the finite family `u`, when `p > 1`. Each term is
bounded by a summable sequence `2 m! (16t)^p |k|^{1-2p}`, plus the Kronecker term at `k = 0`. -/
lemma exists_sum_weighted_gauss_le {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ∀ u : Finset ℤ,
      ∑ k ∈ u, (|(k : ℝ)| + 1) * Real.exp (-((k : ℝ) ^ 2 / (16 * t))) ≤ C * t ^ p := by
  set m : ℕ := ⌈p⌉₊ with hm
  have hpm : p ≤ m := Nat.le_ceil p
  have hsum : Summable (fun k : ℤ => |(k : ℝ)| ^ (-(2 * p - 1))) :=
    Real.summable_abs_int_rpow (by linarith)
  set S : ℝ := ∑' k : ℤ, |(k : ℝ)| ^ (-(2 * p - 1)) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun k => Real.rpow_nonneg (abs_nonneg _) _
  refine ⟨2 * (m.factorial : ℝ) * 16 ^ p * S + 1, fun t ht u => ?_⟩
  have ht0 : 0 < t := by linarith
  have hA0 : 0 < (16 * t) ^ p := Real.rpow_pos_of_pos (by linarith) _
  set G : ℤ → ℝ := fun k => 2 * (m.factorial : ℝ) * (16 * t) ^ p *
    |(k : ℝ)| ^ (-(2 * p - 1)) + if k = 0 then 1 else 0 with hG
  have hGsum : Summable G :=
    (hsum.mul_left _).add (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  have hterm : ∀ k : ℤ, (|(k : ℝ)| + 1) * Real.exp (-((k : ℝ) ^ 2 / (16 * t))) ≤ G k := by
    intro k
    by_cases hk : k = 0
    · subst hk
      have h0 : |((0 : ℤ) : ℝ)| ^ (-(2 * p - 1)) = 0 := by
        rw [Int.cast_zero, abs_zero]
        exact Real.zero_rpow (by linarith : -(2 * p - 1) < 0).ne
      show (|((0 : ℤ) : ℝ)| + 1) * Real.exp (-(((0 : ℤ) : ℝ) ^ 2 / (16 * t))) ≤
        2 * (m.factorial : ℝ) * (16 * t) ^ p * |((0 : ℤ) : ℝ)| ^ (-(2 * p - 1)) +
          if (0 : ℤ) = 0 then 1 else 0
      rw [h0]
      norm_num
    · have hr : 0 < |(k : ℝ)| := abs_pos.2 (by exact_mod_cast hk)
      have hr1 : 1 ≤ |(k : ℝ)| := by
        have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
        exact_mod_cast this
      have hk2 : (k : ℝ) ^ 2 = |(k : ℝ)| ^ 2 := (sq_abs _).symm
      set y : ℝ := (k : ℝ) ^ 2 / (16 * t) with hy_def
      have hy : 0 < y := by
        have : (0 : ℝ) < (k : ℝ) ^ 2 := by rw [hk2]; positivity
        positivity
      have h1 := exp_neg_mul_rpow_le (m := m) (by linarith) hpm hy
      -- `y^p (16t)^p = |k|^{2p}`
      have hyA : y ^ p * (16 * t) ^ p = |(k : ℝ)| ^ (2 * p) := by
        rw [← Real.mul_rpow hy.le (by positivity), hy_def, div_mul_cancel₀ _ (by positivity),
          hk2, Real.rpow_mul hr.le, Real.rpow_two]
      have key : Real.exp (-y) * |(k : ℝ)| ^ (2 * p) ≤ (m.factorial : ℝ) * (16 * t) ^ p := by
        rw [← hyA]
        calc Real.exp (-y) * (y ^ p * (16 * t) ^ p) = (Real.exp (-y) * y ^ p) * (16 * t) ^ p := by
              ring
          _ ≤ (m.factorial : ℝ) * (16 * t) ^ p := mul_le_mul_of_nonneg_right h1 hA0.le
      -- `r = r^{1-2p} r^{2p}` with `r = |k| ≥ 1`
      have hsplit : |(k : ℝ)| = |(k : ℝ)| ^ (-(2 * p - 1)) * |(k : ℝ)| ^ (2 * p) := by
        rw [← Real.rpow_add hr]
        rw [show -(2 * p - 1) + 2 * p = (1 : ℝ) by ring, Real.rpow_one]
      have hw : 0 ≤ |(k : ℝ)| ^ (-(2 * p - 1)) := Real.rpow_nonneg hr.le _
      have hE : 0 ≤ Real.exp (-y) := (Real.exp_pos _).le
      have hk_ite : (if k = 0 then (1 : ℝ) else 0) = 0 := by simp [hk]
      simp only [hG, hk_ite, add_zero]
      calc (|(k : ℝ)| + 1) * Real.exp (-y) ≤ 2 * |(k : ℝ)| * Real.exp (-y) := by
            apply mul_le_mul_of_nonneg_right _ hE
            linarith
        _ = 2 * |(k : ℝ)| ^ (-(2 * p - 1)) * (Real.exp (-y) * |(k : ℝ)| ^ (2 * p)) := by
            linear_combination (2 * Real.exp (-y)) * hsplit
        _ ≤ 2 * |(k : ℝ)| ^ (-(2 * p - 1)) * ((m.factorial : ℝ) * (16 * t) ^ p) :=
            mul_le_mul_of_nonneg_left key (by positivity)
        _ = 2 * (m.factorial : ℝ) * (16 * t) ^ p * |(k : ℝ)| ^ (-(2 * p - 1)) := by ring
  have hG_nonneg : ∀ k : ℤ, 0 ≤ G k := fun k => by
    have h1 : 0 ≤ |(k : ℝ)| ^ (-(2 * p - 1)) := Real.rpow_nonneg (abs_nonneg _) _
    have h2 : 0 ≤ 2 * (m.factorial : ℝ) * (16 * t) ^ p := by positivity
    have h3 : 0 ≤ (if k = 0 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    exact add_nonneg (mul_nonneg h2 h1) h3
  calc ∑ k ∈ u, (|(k : ℝ)| + 1) * Real.exp (-((k : ℝ) ^ 2 / (16 * t)))
      ≤ ∑ k ∈ u, G k := Finset.sum_le_sum fun k _ => hterm k
    _ ≤ ∑' k, G k := hGsum.sum_le_tsum u fun k _ => hG_nonneg k
    _ = 2 * (m.factorial : ℝ) * (16 * t) ^ p * S + 1 := by
        simp only [hG]
        rw [Summable.tsum_add (hsum.mul_left _) (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable,
          tsum_mul_left, tsum_ite_eq]
    _ ≤ (2 * (m.factorial : ℝ) * 16 ^ p * S + 1) * t ^ p := by
        have hT : (1 : ℝ) ≤ t ^ p := Real.one_le_rpow ht (by linarith)
        rw [Real.mul_rpow (by norm_num) ht0.le]
        nlinarith [hT]


/-- The power identity `t^{-1-s/2} · (1/(2t)) · t^{1+s/4} = (1/2) t^{-1-s/4}` for `t > 0`. -/
lemma rpow_mul_inv_mul_rpow {s t : ℝ} (ht : 0 < t) :
    t ^ (-1 - s / 2) * (1 / (2 * t)) * t ^ (1 + s / 4) = (1 / 2) * t ^ (-1 - s / 4) := by
  have hinv : (1 : ℝ) / (2 * t) = (1 / 2) * t ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one]
    field_simp
  have h1 : t ^ (-1 - s / 2) * t ^ (-1 : ℝ) * t ^ (1 + s / 4) = t ^ (-1 - s / 4) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht]
    congr 1
    ring
  rw [hinv]
  calc t ^ (-1 - s / 2) * ((1 / 2) * t ^ (-1 : ℝ)) * t ^ (1 + s / 4)
      = (1 / 2) * (t ^ (-1 - s / 2) * t ^ (-1 : ℝ) * t ^ (1 + s / 4)) := by ring
    _ = (1 / 2) * t ^ (-1 - s / 4) := by rw [h1]

/-- For `0 < t ≤ 1` and every finite family `u`, the partial sums of the absolute interchange
integrands are at most `t^{-1-s/2}` times the sum of the Gaussian tail `e^{-δ²/(8t)}` times the
constant `∑_k e^{-(x-k)²/8}`, plus `√(4πt)`, where `δ = min(x, 1-x)`. -/
lemma sum_abs_interchangeTerm_le_of_le_one {s x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) (u : Finset ℤ) :
    ∑ k ∈ u, |interchangeTerm s x k t| ≤
      t ^ (-1 - s / 2) * (Real.exp (-(min x (1 - x)) ^ 2 / (8 * t)) *
        ∑' k : ℤ, Real.exp (-(x - k) ^ 2 / (4 * 2)) + Real.sqrt (4 * Real.pi * t)) := by
  have hpow : 0 ≤ t ^ (-1 - s / 2) := Real.rpow_nonneg ht0.le _
  have hterm : ∀ k : ℤ, |interchangeTerm s x k t| ≤ t ^ (-1 - s / 2) *
      (Real.exp (-(x - k) ^ 2 / (4 * t)) + gaussAverage k t) := by
    intro k
    unfold interchangeTerm
    rw [abs_mul, abs_of_nonneg hpow]
    apply mul_le_mul_of_nonneg_left _ hpow
    rw [abs_sub_le_iff]
    constructor <;> linarith [gaussAverage_nonneg k t, (Real.exp_pos (-(x - k) ^ 2 / (4 * t))).le]
  have hE : ∑ k ∈ u, Real.exp (-(x - k) ^ 2 / (4 * t)) ≤
      Real.exp (-(min x (1 - x)) ^ 2 / (8 * t)) * ∑' k : ℤ, Real.exp (-(x - k) ^ 2 / (4 * 2)) := by
    calc ∑ k ∈ u, Real.exp (-(x - k) ^ 2 / (4 * t))
        ≤ ∑ k ∈ u, Real.exp (-(min x (1 - x)) ^ 2 / (8 * t)) *
            Real.exp (-(x - k) ^ 2 / (4 * 2)) :=
          Finset.sum_le_sum fun k _ => exp_gauss_le_exp_mul hx0 hx1 ht0 ht1 k
      _ = Real.exp (-(min x (1 - x)) ^ 2 / (8 * t)) *
            ∑ k ∈ u, Real.exp (-(x - k) ^ 2 / (4 * 2)) := (Finset.mul_sum _ _ _).symm
      _ ≤ Real.exp (-(min x (1 - x)) ^ 2 / (8 * t)) *
            ∑' k : ℤ, Real.exp (-(x - k) ^ 2 / (4 * 2)) :=
          mul_le_mul_of_nonneg_left
            ((summable_gauss_width_two x).sum_le_tsum u fun k _ => (Real.exp_pos _).le)
            (Real.exp_pos _).le
  have hA : ∑ k ∈ u, gaussAverage k t ≤ Real.sqrt (4 * Real.pi * t) := sum_gaussAverage_le ht0 u
  calc ∑ k ∈ u, |interchangeTerm s x k t|
      ≤ ∑ k ∈ u, t ^ (-1 - s / 2) * (Real.exp (-(x - k) ^ 2 / (4 * t)) + gaussAverage k t) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = t ^ (-1 - s / 2) * (∑ k ∈ u, Real.exp (-(x - k) ^ 2 / (4 * t)) +
          ∑ k ∈ u, gaussAverage k t) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ t ^ (-1 - s / 2) * (Real.exp (-(min x (1 - x)) ^ 2 / (8 * t)) *
          ∑' k : ℤ, Real.exp (-(x - k) ^ 2 / (4 * 2)) + Real.sqrt (4 * Real.pi * t)) :=
        mul_le_mul_of_nonneg_left (add_le_add hE hA) hpow

/-- The bound `M(t) = t^{-1-s/2}(e^{-δ²/(8t)} C + √(4πt))` is integrable on `(0, 1]`. -/
lemma integrableOn_sum_bound_Ioc {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hx0 : 0 < x)
    (hx1 : x < 1) :
    IntegrableOn (fun t : ℝ => t ^ (-1 - s / 2) * (Real.exp (-(min x (1 - x)) ^ 2 / (8 * t)) *
        ∑' k : ℤ, Real.exp (-(x - k) ^ 2 / (4 * 2)) + Real.sqrt (4 * Real.pi * t))) (Ioc 0 1) := by
  have hδ0 : 0 < min x (1 - x) := lt_min hx0 (by linarith)
  set C : ℝ := ∑' k : ℤ, Real.exp (-(x - k) ^ 2 / (4 * 2)) with hC
  have h1 : IntegrableOn (fun t : ℝ => t ^ (-1 - s / 2) *
      Real.exp (-((min x (1 - x)) ^ 2 / 8) / t)) (Ioi 0) :=
    integrableOn_rpow_neg_exp_div_Ioi (by linarith) (by positivity)
  have h1' : IntegrableOn (fun t : ℝ => t ^ (-1 - s / 2) *
      Real.exp (-(min x (1 - x)) ^ 2 / (8 * t)) * C) (Ioc 0 1) := by
    refine IntegrableOn.congr_fun ((h1.mono_set Ioc_subset_Ioi_self).mul_const C)
      (fun t ht => ?_) measurableSet_Ioc
    have ht0 : 0 < t := ht.1
    congr 3
    field_simp
  have h2 : IntegrableOn (fun t : ℝ => t ^ (-1 - s / 2) * Real.sqrt (4 * Real.pi * t))
      (Ioc 0 1) := by
    have hi : IntervalIntegrable (fun t : ℝ => Real.sqrt (4 * Real.pi) * t ^ (-(1 + s) / 2))
        volume 0 1 :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
    refine IntegrableOn.congr_fun ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hi)
      (fun t ht => ?_) measurableSet_Ioc
    have ht0 : 0 < t := ht.1
    have hsq : Real.sqrt (4 * Real.pi * t) = Real.sqrt (4 * Real.pi) * t ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    have hexp : t ^ (-1 - s / 2) * t ^ (1 / 2 : ℝ) = t ^ (-(1 + s) / 2) := by
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    rw [hsq, ← hexp]
    ring
  have h3 := h1'.add h2
  refine IntegrableOn.congr_fun h3 (fun t _ => ?_) measurableSet_Ioc
  simp only [Pi.add_apply]
  ring

/-- The sum over the Gaussian tail of the absolute interchange integrals on `(0, 1]` is summable:
the sum over `k` is taken first, and the partial sums are dominated by the integrable bound
`M(t)`. -/
lemma summable_integral_abs_interchangeTerm_Ioc {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hx0 : 0 < x) (hx1 : x < 1) :
    Summable (fun k : ℤ => ∫ t in Ioc (0 : ℝ) 1, |interchangeTerm s x k t|) := by
  have hM := integrableOn_sum_bound_Ioc hs0 hs1 hx0 hx1
  refine summable_of_sum_le (c := ∫ t in Ioc (0 : ℝ) 1, (t ^ (-1 - s / 2) *
      (Real.exp (-(min x (1 - x)) ^ 2 / (8 * t)) *
        ∑' k : ℤ, Real.exp (-(x - k) ^ 2 / (4 * 2)) + Real.sqrt (4 * Real.pi * t))))
    (fun k => setIntegral_nonneg measurableSet_Ioc (fun t _ => abs_nonneg _)) ?_
  intro u
  have hab : ∀ k : ℤ, IntegrableOn (fun t => |interchangeTerm s x k t|) (Ioi (0 : ℝ)) :=
    fun k => (integrableOn_interchangeTerm hs0 hs1 hx0 hx1 k).abs
  have hint : ∀ k : ℤ, IntegrableOn (fun t => |interchangeTerm s x k t|) (Ioc (0 : ℝ) 1) :=
    fun k => (hab k).mono_set Ioc_subset_Ioi_self
  calc ∑ k ∈ u, ∫ t in Ioc (0 : ℝ) 1, |interchangeTerm s x k t|
      = ∫ t in Ioc (0 : ℝ) 1, ∑ k ∈ u, |interchangeTerm s x k t| :=
        (integral_finsetSum u fun k _ => hint k).symm
    _ ≤ _ := setIntegral_mono_on (integrable_finsetSum u fun k _ => hint k) hM
        measurableSet_Ioc fun t ht => sum_abs_interchangeTerm_le_of_le_one hx0 hx1 ht.1 ht.2 u

/-- For `t ≥ 1`, the absolute interchange integrand is bounded by the weighted lattice term plus
a constant on the two central indices `|k| ≤ 1`, where the crude bound `2 t^{-1-s/2}` holds. -/
lemma abs_interchangeTerm_le_of_one_le {s x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {t : ℝ} (ht : 1 ≤ t)
    (k : ℤ) :
    |interchangeTerm s x k t| ≤
      t ^ (-1 - s / 2) * ((|(k : ℝ)| + 1) / (2 * t) * Real.exp (-((k : ℝ) ^ 2 / (16 * t)))) +
        if |(k : ℝ)| ≤ 1 then 2 * t ^ (-1 - s / 2) else 0 := by
  have ht0 : 0 < t := by linarith
  have hpow : 0 ≤ t ^ (-1 - s / 2) := Real.rpow_nonneg ht0.le _
  have hfirst : 0 ≤ t ^ (-1 - s / 2) * ((|(k : ℝ)| + 1) / (2 * t) *
      Real.exp (-((k : ℝ) ^ 2 / (16 * t)))) := by positivity
  by_cases hk : |(k : ℝ)| ≤ 1
  · simp only [hk, ite_true]
    have hcrude : |interchangeTerm s x k t| ≤ 2 * t ^ (-1 - s / 2) := by
      unfold interchangeTerm
      rw [abs_mul, abs_of_nonneg hpow]
      have hE : Real.exp (-(x - k) ^ 2 / (4 * t)) ≤ 1 :=
        Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _))
          (by positivity))
      have hE0 := (Real.exp_pos (-(x - k) ^ 2 / (4 * t))).le
      have hA : gaussAverage k t ≤ 1 := gaussAverage_le_one k ht0
      have hA0 := gaussAverage_nonneg k t
      have habs : |Real.exp (-(x - k) ^ 2 / (4 * t)) - gaussAverage k t| ≤ 1 :=
        abs_le.2 ⟨by linarith, by linarith⟩
      calc t ^ (-1 - s / 2) * |Real.exp (-(x - k) ^ 2 / (4 * t)) - gaussAverage k t|
          ≤ t ^ (-1 - s / 2) * 1 := mul_le_mul_of_nonneg_left habs hpow
        _ ≤ 2 * t ^ (-1 - s / 2) := by linarith
    linarith
  · simp only [hk, ite_false, add_zero]
    have hZ : (1 : ℤ) < |k| := by
      have h1 : (1 : ℝ) < |(k : ℝ)| := lt_of_not_ge hk
      rw [← Int.cast_abs] at h1
      exact_mod_cast h1
    have h2 : (2 : ℤ) ≤ |k| := by omega
    have hk2 : (2 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast h2
    exact abs_interchangeTerm_le k hk2 hx0 hx1 ht0


/-- The partial sums of the indicator of `|k| ≤ 1` are at most three times its value. -/
lemma sum_ite_abs_le_one_le_three (u : Finset ℤ) {c : ℝ} (hc : 0 ≤ c) :
    ∑ k ∈ u, (if |(k : ℝ)| ≤ 1 then c else 0) ≤ 3 * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hsub : u.filter (fun k : ℤ => |(k : ℝ)| ≤ 1) ⊆ Finset.Icc (-1 : ℤ) 1 := by
    intro k hk
    rw [Finset.mem_filter] at hk
    have h := abs_le.1 hk.2
    rw [Finset.mem_Icc]
    constructor
    · have : (-1 : ℝ) ≤ k := h.1
      exact_mod_cast this
    · have : (k : ℝ) ≤ 1 := h.2
      exact_mod_cast this
  have hcard : ((u.filter (fun k : ℤ => |(k : ℝ)| ≤ 1)).card : ℝ) ≤ 3 := by
    have h := Finset.card_le_card hsub
    rw [Int.card_Icc] at h
    have h' : ((u.filter (fun k : ℤ => |(k : ℝ)| ≤ 1)).card) ≤ 3 := by
      simpa using h
    exact_mod_cast h'
  exact mul_le_mul_of_nonneg_right hcard hc

/-- For `t ≥ 1`, the sum over a finite family of the bounds of `|u_k^x(t)|` is at most the
lattice constant times `t^{-1-s/2}/(2t) · t^{1+s/4}`, plus `6 t^{-1-s/2}`. -/
lemma sum_abs_interchangeTerm_le_of_one_le {s x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {C : ℝ}
    (hC : ∀ t : ℝ, 1 ≤ t → ∀ u : Finset ℤ,
      ∑ k ∈ u, (|(k : ℝ)| + 1) * Real.exp (-((k : ℝ) ^ 2 / (16 * t))) ≤ C * t ^ (1 + s / 4))
    {t : ℝ} (ht : 1 ≤ t) (u : Finset ℤ) :
    ∑ k ∈ u, |interchangeTerm s x k t| ≤ (C / 2) * t ^ (-1 - s / 4) + 6 * t ^ (-1 - s / 2) := by
  have ht0 : 0 < t := by linarith
  calc ∑ k ∈ u, |interchangeTerm s x k t|
      ≤ ∑ k ∈ u, (t ^ (-1 - s / 2) * ((|(k : ℝ)| + 1) / (2 * t) *
          Real.exp (-((k : ℝ) ^ 2 / (16 * t)))) +
          if |(k : ℝ)| ≤ 1 then 2 * t ^ (-1 - s / 2) else 0) :=
        Finset.sum_le_sum fun k _ => abs_interchangeTerm_le_of_one_le hx0 hx1 ht k
    _ = t ^ (-1 - s / 2) * (1 / (2 * t)) * ∑ k ∈ u, (|(k : ℝ)| + 1) *
          Real.exp (-((k : ℝ) ^ 2 / (16 * t))) +
          ∑ k ∈ u, (if |(k : ℝ)| ≤ 1 then 2 * t ^ (-1 - s / 2) else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ ≤ t ^ (-1 - s / 2) * (1 / (2 * t)) * (C * t ^ (1 + s / 4)) +
          3 * (2 * t ^ (-1 - s / 2)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (hC t ht u) (by positivity)
        · exact sum_ite_abs_le_one_le_three u (by positivity)
    _ = (C / 2) * t ^ (-1 - s / 4) + 6 * t ^ (-1 - s / 2) := by
        linear_combination C * rpow_mul_inv_mul_rpow (s := s) ht0

/-- The sum over `k` of the absolute interchange integrals on `[1, ∞)` is summable. -/
lemma summable_integral_abs_interchangeTerm_Ioi {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hx0 : 0 < x) (hx1 : x < 1) :
    Summable (fun k : ℤ => ∫ t in Ioi (1 : ℝ), |interchangeTerm s x k t|) := by
  obtain ⟨C, hC⟩ := exists_sum_weighted_gauss_le (p := 1 + s / 4) (by linarith)
  have hN : IntegrableOn (fun t : ℝ => (C / 2) * t ^ (-1 - s / 4) + 6 * t ^ (-1 - s / 2))
      (Ioi (1 : ℝ)) := by
    have h1 := integrableOn_Ioi_rpow_of_lt (a := -1 - s / 4) (c := 1) (by linarith) one_pos
    have h2 := integrableOn_Ioi_rpow_of_lt (a := -1 - s / 2) (c := 1) (by linarith) one_pos
    exact (h1.const_mul (C / 2)).add (h2.const_mul 6)
  refine summable_of_sum_le (c := ∫ t in Ioi (1 : ℝ),
      ((C / 2) * t ^ (-1 - s / 4) + 6 * t ^ (-1 - s / 2)))
    (fun k => setIntegral_nonneg measurableSet_Ioi (fun t _ => abs_nonneg _)) ?_
  intro u
  have hab : ∀ k : ℤ, IntegrableOn (fun t => |interchangeTerm s x k t|) (Ioi (0 : ℝ)) :=
    fun k => (integrableOn_interchangeTerm hs0 hs1 hx0 hx1 k).abs
  have hint : ∀ k : ℤ, IntegrableOn (fun t => |interchangeTerm s x k t|) (Ioi (1 : ℝ)) :=
    fun k => (hab k).mono_set (Ioi_subset_Ioi zero_le_one)
  calc ∑ k ∈ u, ∫ t in Ioi (1 : ℝ), |interchangeTerm s x k t|
      = ∫ t in Ioi (1 : ℝ), ∑ k ∈ u, |interchangeTerm s x k t| :=
        (integral_finsetSum u fun k _ => hint k).symm
    _ ≤ _ := setIntegral_mono_on (integrable_finsetSum u fun k _ => hint k) hN measurableSet_Ioi
        fun t ht => sum_abs_interchangeTerm_le_of_one_le hx0 hx1 hC (le_of_lt ht) u

/-- **Absolute summability of the interchange integrals.** For `0 < s < 1` and `0 < x < 1`, the
sum over `k` of `∫_{(0,∞)} |u_k^x(t)| dt` converges. The time axis is split at `t = 1`, and the
sum over `k` is taken first on each piece. -/
theorem summable_integral_abs_interchangeTerm {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hx0 : 0 < x) (hx1 : x < 1) :
    Summable (fun k : ℤ => ∫ t in Ioi (0 : ℝ), |interchangeTerm s x k t|) := by
  have hsplit : ∀ k : ℤ, ∫ t in Ioi (0 : ℝ), |interchangeTerm s x k t| =
      (∫ t in Ioc (0 : ℝ) 1, |interchangeTerm s x k t|) +
        (∫ t in Ioi (1 : ℝ), |interchangeTerm s x k t|) := by
    intro k
    have hint : IntegrableOn (fun t => |interchangeTerm s x k t|) (Ioi (0 : ℝ)) :=
      (integrableOn_interchangeTerm hs0 hs1 hx0 hx1 k).abs
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi zero_le_one))
  exact ((summable_integral_abs_interchangeTerm_Ioc hs0 hs1 hx0 hx1).add
    (summable_integral_abs_interchangeTerm_Ioi hs0 hs1 hx0 hx1)).congr (fun k => (hsplit k).symm)

end Riesz1

end
