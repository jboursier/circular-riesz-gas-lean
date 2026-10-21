/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.InterchangeAverage
public import Mathlib.Analysis.PSeries
public import Mathlib.Tactic

/-!
# The interchange integrand and its absolute summability

The integrand of Lemma 2.1 is, for `0 < s < 1`, `0 < x < 1`,
`k ∈ ℤ` and `t > 0`,
`u_k^x(t) = t^{-1-s/2} (e^{-(x-k)^2/(4t)} - ∫_0^1 e^{-(y-k)^2/(4t)} dy)`.
This file proves that each `u_k^x` is integrable on `(0, ∞)`, that its integral equals
`Γ(s/2) (((x-k)^2/4)^{-s/2} - ∫_0^1 ((y-k)^2/4)^{-s/2} dy)`, and that the integrals of the
absolute values are summable over `k`.

The summability uses the cancellation of the two Gaussian terms for `|k| ≥ 2`: their difference is
at most `(|k| + 1) / (2t) · e^{-k²/(16t)}` uniformly in `x, y ∈ [0, 1]`, and the resulting
time integrals decay like `|k|^{-(1+s)}`, which is summable.

Main results:
* `Riesz1.interchangeTerm`: the integrand `u_k^x(t)`.
* `Riesz1.integrableOn_interchangeTerm`, `Riesz1.integral_interchangeTerm`.
* `Riesz1.summable_integral_abs_interchangeTerm`: `∑_k ∫_{(0,∞)} |u_k^x(t)| dt < ∞`.
* `Riesz1.rpow_sq_div_four_neg_half`: the identity `((z)^2/4)^{-s/2} = 2^s |z|^{-s}`.
-/

public section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- The integrand `u_k^x(t) = t^{-1-s/2} (e^{-(x-k)^2/(4t)} - ∫_0^1 e^{-(y-k)^2/(4t)} dy)`
of Lemma 2.1. The formula is the paper's for `t > 0`. Its values at
`t ≤ 0` never enter, because every integral in this file is over `(0, ∞)`. -/
@[expose] noncomputable def interchangeTerm (s x : ℝ) (k : ℤ) (t : ℝ) : ℝ :=
  t ^ (-1 - s / 2) * (Real.exp (-(x - k) ^ 2 / (4 * t)) - gaussAverage k t)

/-- The difference of two Gaussians, for a Gaussian and an average, is a difference of two
products with `t^{-1-s/2}`. -/
lemma interchangeTerm_eq_sub (s x : ℝ) (k : ℤ) (t : ℝ) :
    interchangeTerm s x k t = t ^ (-1 - s / 2) * Real.exp (-(x - k) ^ 2 / (4 * t)) -
      t ^ (-1 - s / 2) * gaussAverage k t := by
  unfold interchangeTerm
  ring

/-- The rpow identity `((z)^2/4)^{-s/2} = 2^s |z|^{-s}` for every real `z` and `s`. -/
lemma rpow_sq_div_four_neg_half (s z : ℝ) :
    ((z ^ 2 / 4) ^ (-(s / 2))) = 2 ^ s * |z| ^ (-s) := by
  have h4 : ((4 : ℝ) ^ (s / 2)) = 2 ^ s := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hsq : (z ^ 2) ^ (-(s / 2)) = |z| ^ (-s) := by
    rw [← sq_abs z, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg z)]
    congr 1
    push_cast
    ring
  rw [Real.div_rpow (sq_nonneg z) (by norm_num), hsq, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
    ← h4]
  field_simp

/-- The Gaussian in the form `exp(-c/t)` with `c = z²/4` is the Gaussian `exp(-z²/(4t))`. -/
lemma exp_neg_quarter_sq_div (z t : ℝ) :
    Real.exp (-(z ^ 2 / 4) / t) = Real.exp (-z ^ 2 / (4 * t)) := by
  congr 1
  ring

/-- The integrand is integrable on `(0, ∞)` for `0 < s < 1`, `0 < x < 1` and every `k ∈ ℤ`. -/
lemma integrableOn_interchangeTerm {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hx0 : 0 < x)
    (hx1 : x < 1) (k : ℤ) : IntegrableOn (interchangeTerm s x k) (Ioi 0) := by
  have hxk : x - k ≠ 0 := by
    intro h
    have hk : x = k := by linarith
    have h1 : (k : ℝ) < 1 := hk ▸ hx1
    have h2 : (0 : ℝ) < k := hk ▸ hx0
    have h3 : (0 : ℤ) < k := by exact_mod_cast h2
    have h4 : k < (1 : ℤ) := by exact_mod_cast h1
    omega
  have hc : 0 < (x - k) ^ 2 / 4 := by
    have : 0 < (x - k) ^ 2 := by positivity
    linarith
  have hI1 : IntegrableOn (fun t : ℝ => t ^ (-1 - s / 2) * Real.exp (-(x - k) ^ 2 / (4 * t)))
      (Ioi 0) := by
    have h := integrableOn_rpow_neg_exp_div_Ioi (α := s / 2) (c := (x - k) ^ 2 / 4)
      (by linarith) hc
    have hfun1 : (fun t : ℝ => t ^ (-1 - s / 2) * Real.exp (-(x - k) ^ 2 / (4 * t))) =
        fun t : ℝ => t ^ (-1 - s / 2) * Real.exp (-((x - k) ^ 2 / 4) / t) := by
      funext t
      rw [exp_neg_quarter_sq_div]
    rw [hfun1]
    exact h
  have hI2 : IntegrableOn (fun t : ℝ => t ^ (-1 - s / 2) * gaussAverage k t) (Ioi 0) :=
    integrableOn_rpow_mul_gaussAverage (by linarith) (by linarith) k
  have hfun : interchangeTerm s x k = fun t : ℝ =>
      t ^ (-1 - s / 2) * Real.exp (-(x - k) ^ 2 / (4 * t)) - t ^ (-1 - s / 2) * gaussAverage k t := by
    funext t
    exact interchangeTerm_eq_sub s x k t
  rw [hfun]
  exact hI1.sub hI2

/-- The integral of the interchange integrand over `(0, ∞)` is the difference of the two
reciprocal-time Gamma integrals, for `0 < s < 1`, `0 < x < 1` and every `k ∈ ℤ`. -/
lemma integral_interchangeTerm {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hx0 : 0 < x)
    (hx1 : x < 1) (k : ℤ) :
    ∫ t in Ioi (0 : ℝ), interchangeTerm s x k t =
      Real.Gamma (s / 2) * (((x - k) ^ 2 / 4) ^ (-(s / 2)) -
        ∫ y in (0 : ℝ)..1, ((y - k) ^ 2 / 4) ^ (-(s / 2))) := by
  have hxk : x - k ≠ 0 := by
    intro h
    have hk : x = k := by linarith
    have h1 : (k : ℝ) < 1 := hk ▸ hx1
    have h2 : (0 : ℝ) < k := hk ▸ hx0
    have h3 : (0 : ℤ) < k := by exact_mod_cast h2
    have h4 : k < (1 : ℤ) := by exact_mod_cast h1
    omega
  have hc : 0 < (x - k) ^ 2 / 4 := by
    have : 0 < (x - k) ^ 2 := by positivity
    linarith
  have hI1 : IntegrableOn (fun t : ℝ => t ^ (-1 - s / 2) * Real.exp (-(x - k) ^ 2 / (4 * t)))
      (Ioi 0) := by
    have h := integrableOn_rpow_neg_exp_div_Ioi (α := s / 2) (c := (x - k) ^ 2 / 4)
      (by linarith) hc
    have hfun1 : (fun t : ℝ => t ^ (-1 - s / 2) * Real.exp (-(x - k) ^ 2 / (4 * t))) =
        fun t : ℝ => t ^ (-1 - s / 2) * Real.exp (-((x - k) ^ 2 / 4) / t) := by
      funext t
      rw [exp_neg_quarter_sq_div]
    rw [hfun1]
    exact h
  have hI2 : IntegrableOn (fun t : ℝ => t ^ (-1 - s / 2) * gaussAverage k t) (Ioi 0) :=
    integrableOn_rpow_mul_gaussAverage (by linarith) (by linarith) k
  have hfun : (fun t : ℝ => interchangeTerm s x k t) = fun t : ℝ =>
      t ^ (-1 - s / 2) * Real.exp (-(x - k) ^ 2 / (4 * t)) - t ^ (-1 - s / 2) * gaussAverage k t := by
    funext t
    exact interchangeTerm_eq_sub s x k t
  have hG := integral_rpow_neg_exp_div_Ioi (α := s / 2) (c := (x - k) ^ 2 / 4) (by linarith) hc
  have hA := integral_rpow_mul_gaussAverage (α := s / 2) (by linarith) (by linarith) k
  have hE : ∫ t in Ioi (0 : ℝ), t ^ (-1 - s / 2) * Real.exp (-(x - k) ^ 2 / (4 * t)) =
      ((x - k) ^ 2 / 4) ^ (-(s / 2)) * Real.Gamma (s / 2) := by
    rw [← hG]
    congr 1
    funext t
    rw [exp_neg_quarter_sq_div]
  rw [hfun, integral_sub hI1 hI2, hE, hA]
  ring

/-- If `M ≤ a ≤ b`, then `|e^{-a} - e^{-b}| ≤ |a - b| e^{-M}`. -/
lemma abs_exp_neg_sub_exp_neg_le_of_le {a b M : ℝ} (ha : M ≤ a) (hab : a ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| * Real.exp (-M) := by
  have hnn : 0 ≤ b - a := sub_nonneg.2 hab
  have hexp : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 : 1 - (b - a) ≤ Real.exp (-(b - a)) := Real.one_sub_le_exp_neg _
  have h3 : Real.exp (-a) ≤ Real.exp (-M) := Real.exp_le_exp.2 (neg_le_neg ha)
  have hpos : 0 < Real.exp (-a) := Real.exp_pos _
  have hdiff : Real.exp (-a) - Real.exp (-b) = Real.exp (-a) * (1 - Real.exp (-(b - a))) := by
    rw [hexp]
    ring
  have hlow : 0 ≤ 1 - Real.exp (-(b - a)) := by
    have : Real.exp (-(b - a)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  rw [hdiff, abs_of_nonneg (mul_nonneg hpos.le hlow), abs_sub_comm a b, abs_of_nonneg hnn]
  calc Real.exp (-a) * (1 - Real.exp (-(b - a))) ≤ Real.exp (-a) * (b - a) :=
        mul_le_mul_of_nonneg_left (by linarith) hpos.le
    _ ≤ Real.exp (-M) * (b - a) := mul_le_mul_of_nonneg_right h3 hnn
    _ = (b - a) * Real.exp (-M) := mul_comm _ _

/-- If `M ≤ a` and `M ≤ b`, then `|e^{-a} - e^{-b}| ≤ |a - b| e^{-M}`. -/
lemma abs_exp_neg_sub_exp_neg_le {a b M : ℝ} (ha : M ≤ a) (hb : M ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| * Real.exp (-M) := by
  rcases le_total a b with hab | hab
  · exact abs_exp_neg_sub_exp_neg_le_of_le ha hab
  · have h := abs_exp_neg_sub_exp_neg_le_of_le hb hab
    rw [abs_sub_comm (Real.exp (-a)), abs_sub_comm a b]
    exact h

/-- For `|k| ≥ 2` the difference of two Gaussians at points of `[0, 1]` is at most
`(|k| + 1) / (2t) · e^{-k²/(16t)}`. -/
lemma abs_gauss_sub_gauss_le {x y t : ℝ} (ht : 0 < t) (k : ℤ) (hk : 2 ≤ |(k : ℝ)|)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |Real.exp (-(x - k) ^ 2 / (4 * t)) - Real.exp (-(y - k) ^ 2 / (4 * t))| ≤
      (|(k : ℝ)| + 1) / (2 * t) * Real.exp (-((k : ℝ) ^ 2 / (16 * t))) := by
  -- The common lower bound `M = k²/(16t)` for both exponents.
  have hk2 : 4 ≤ (k : ℝ) ^ 2 := by
    have h := sq_abs (k : ℝ)
    nlinarith [abs_nonneg (k : ℝ)]
  have hxk : (k : ℝ) ^ 2 / 4 ≤ (x - k) ^ 2 := by
    have h1 : |(k : ℝ)| - 1 ≤ |x - k| := by
      have := abs_sub_abs_le_abs_sub (k : ℝ) x
      rw [abs_sub_comm (k : ℝ) x, abs_of_nonneg hx0] at this
      have hab : |(k : ℝ) - x| = |x - k| := abs_sub_comm _ _
      linarith
    have h2 : |(k : ℝ)| / 2 ≤ |x - k| := by linarith
    have h3 : (|(k : ℝ)| / 2) ^ 2 ≤ |x - k| ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    have h4 : (|(k : ℝ)| / 2) ^ 2 = (k : ℝ) ^ 2 / 4 := by
      rw [div_pow, sq_abs]
      ring
    have h5 : |x - k| ^ 2 = (x - k) ^ 2 := sq_abs _
    linarith
  have hyk : (k : ℝ) ^ 2 / 4 ≤ (y - k) ^ 2 := by
    have h1 : |(k : ℝ)| - 1 ≤ |y - k| := by
      have := abs_sub_abs_le_abs_sub (k : ℝ) y
      rw [abs_sub_comm (k : ℝ) y, abs_of_nonneg hy0] at this
      have hab : |(k : ℝ) - y| = |y - k| := abs_sub_comm _ _
      linarith
    have h2 : |(k : ℝ)| / 2 ≤ |y - k| := by linarith
    have h3 : (|(k : ℝ)| / 2) ^ 2 ≤ |y - k| ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    have h4 : (|(k : ℝ)| / 2) ^ 2 = (k : ℝ) ^ 2 / 4 := by
      rw [div_pow, sq_abs]
      ring
    have h5 : |y - k| ^ 2 = (y - k) ^ 2 := sq_abs _
    linarith
  -- The two exponents dominate `M = k²/(16t)`.
  have hM : (k : ℝ) ^ 2 / (16 * t) = (k : ℝ) ^ 2 / 4 / (4 * t) := by
    field_simp
    ring
  have hMa : (k : ℝ) ^ 2 / (16 * t) ≤ (x - k) ^ 2 / (4 * t) := by
    rw [hM]
    exact div_le_div_of_nonneg_right hxk (by positivity)
  have hMb : (k : ℝ) ^ 2 / (16 * t) ≤ (y - k) ^ 2 / (4 * t) := by
    rw [hM]
    exact div_le_div_of_nonneg_right hyk (by positivity)
  -- The difference of the exponents is `(x - y)(x + y - 2k) / (4t)`.
  have hdiff : |(x - k) ^ 2 / (4 * t) - (y - k) ^ 2 / (4 * t)| ≤ (|(k : ℝ)| + 1) / (2 * t) := by
    have e : (x - k) ^ 2 / (4 * t) - (y - k) ^ 2 / (4 * t) =
        (x - y) * (x + y - 2 * k) / (4 * t) := by
      field_simp
      ring
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * t), div_le_div_iff₀ (by positivity)
      (by positivity), abs_mul]
    have hxy : |x - y| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hs : |x + y - 2 * k| ≤ 2 + 2 * |(k : ℝ)| := by
      rw [abs_le]
      have := le_abs_self (k : ℝ)
      have := neg_abs_le (k : ℝ)
      constructor <;> linarith
    have hprod : |x - y| * |x + y - 2 * k| ≤ 1 * (2 + 2 * |(k : ℝ)|) :=
      mul_le_mul hxy hs (abs_nonneg _) zero_le_one
    nlinarith [abs_nonneg (k : ℝ), abs_nonneg (x - y), abs_nonneg (x + y - 2 * k)]
  -- Now the exponential estimate between two points above `M`.
  have key := abs_exp_neg_sub_exp_neg_le hMa hMb
  calc |Real.exp (-(x - k) ^ 2 / (4 * t)) - Real.exp (-(y - k) ^ 2 / (4 * t))|
      = |Real.exp (-((x - k) ^ 2 / (4 * t))) - Real.exp (-((y - k) ^ 2 / (4 * t)))| := by
        congr 2 <;> ring_nf
    _ ≤ |(x - k) ^ 2 / (4 * t) - (y - k) ^ 2 / (4 * t)| *
          Real.exp (-((k : ℝ) ^ 2 / (16 * t))) := key
    _ ≤ (|(k : ℝ)| + 1) / (2 * t) * Real.exp (-((k : ℝ) ^ 2 / (16 * t))) :=
        mul_le_mul_of_nonneg_right hdiff (Real.exp_pos _).le

end Riesz1
