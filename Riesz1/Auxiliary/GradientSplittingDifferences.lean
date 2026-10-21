/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Riesz1.ToMathlib.CircDist

/-!
# Circular distance, the weight `w_1`, and the antipodal bound

The differences part of Lemma 5.7, its first claim: for a
smooth periodic `ψ` on `ℓ^{-1}𝕋` with `|ψ'| ≤ C_0 w_1`, and every `u` with `|u| ≥ 1`,
`|ψ(u) - ψ((2ℓ)^{-1})| ≤ C C_0 |u|^{s-1}`.

Here `L = ℓ^{-1}` is the length of the circle `ℓ^{-1}𝕋`, the antipode of `0` is `L / 2`, and the
circular distance `|u|` is `circDist L u`. The weight `w_1` is the one of
the data part of Lemma 5.7.
-/

@[expose] public section

open Set MeasureTheory
open scoped ContDiff

namespace Riesz1

/-- The weight `w_1` of the data part of Lemma 5.7 on `L𝕋`, with `L = ℓ^{-1}` and
the parameter `K`: `max(|u|, K^{-1})^{-a}` when `|u| < 1`, and `|u|^{s-2}` when `|u| ≥ 1`. -/
noncomputable def gradWeightOne (s a K L u : ℝ) : ℝ :=
  if circDist L u < 1 then max (circDist L u) K⁻¹ ^ (-a) else circDist L u ^ (s - 2)

/-- On `[0, L/2]` the circular distance is the identity. -/
lemma circDist_of_mem_Icc {L t : ℝ} (hL : 0 < L) (ht0 : 0 ≤ t) (htL : t ≤ L / 2) :
    circDist L t = t := by
  rcases eq_or_lt_of_le htL with h | h
  · have hround : round (t / L) = 1 := by
      rw [h, round_eq]
      have : (L / 2) / L + 1 / 2 = 1 := by field_simp; ring
      rw [this, Int.floor_one]
    rw [circDist, hround, h]
    rw [show L / 2 - L * ((1 : ℤ) : ℝ) = -(L / 2) by push_cast; ring, abs_neg,
      abs_of_pos (by linarith)]
  · have hround : round (t / L) = 0 := by
      rw [round_eq_zero_iff]
      constructor
      · have := div_nonneg ht0 hL.le
        linarith
      · rw [div_lt_iff₀ hL]
        linarith
    rw [circDist, hround, Int.cast_zero, mul_zero, sub_zero, abs_of_nonneg ht0]

/-- On `[-L/2, 0]` the circular distance of `-t` is the distance of `t`: it equals `t` for
`t ∈ [0, L/2]`. -/
lemma circDist_neg_of_mem_Icc {L t : ℝ} (hL : 0 < L) (ht0 : 0 ≤ t) (htL : t ≤ L / 2) :
    circDist L (-t) = t := by
  have hround : round (-t / L) = 0 := by
    rw [round_eq_zero_iff]
    constructor
    · rw [neg_div, le_neg, ← neg_div]
      have : t / L ≤ 1 / 2 := by
        rw [div_le_iff₀ hL]
        linarith
      linarith
    · have := div_nonneg ht0 hL.le
      rw [neg_div]
      linarith
  rw [circDist, hround, Int.cast_zero, mul_zero, sub_zero, abs_neg, abs_of_nonneg ht0]

/-- On `[1, L/2]`, the weight `w_1` is the power `|u|^{s-2}`. -/
lemma gradWeightOne_of_one_le {s a K L t : ℝ} (ht1 : 1 ≤ circDist L t) :
    gradWeightOne s a K L t = circDist L t ^ (s - 2) := by
  simp [gradWeightOne, not_lt.mpr ht1]

/-- The power integral `∫_p^q t^{s-2} dt` for `1 ≤ p ≤ q`, bounded by `p^{s-1}/(1-s)`. -/
lemma integral_rpow_sub_two_le {s p q : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hp : 1 ≤ p)
    (hpq : p ≤ q) : ∫ t in p..q, t ^ (s - 2) ≤ p ^ (s - 1) / (1 - s) := by
  have hzero : (0 : ℝ) ∉ Set.uIcc p q := by
    intro h
    rw [Set.mem_uIcc] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  rw [integral_rpow (Or.inr ⟨by intro h; linarith, hzero⟩)]
  have e : s - 2 + 1 = s - 1 := by ring
  rw [e]
  have hq : 0 ≤ q ^ (s - 1) := Real.rpow_nonneg (by linarith) _
  have h1s : (1 - s) ≠ 0 := by linarith
  calc (q ^ (s - 1) - p ^ (s - 1)) / (s - 1)
      = (p ^ (s - 1) - q ^ (s - 1)) / (1 - s) := by
        rw [show s - 1 = -(1 - s) by ring, div_neg, ← neg_div, neg_sub]
    _ ≤ p ^ (s - 1) / (1 - s) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- Positive-side antipodal bound: for a smooth `φ` with `|φ'| ≤ C_0 t^{s-2}` on `[t_0, L/2]`,
with `1 ≤ t_0 ≤ L/2`, one has `|φ(L/2) - φ(t_0)| ≤ C_0 t_0^{s-1}/(1-s)`. -/
lemma abs_sub_antipode_le_of_mem {s C0 L t0 : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hC0 : 0 ≤ C0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (ht1 : 1 ≤ t0) (ht0L : t0 ≤ L / 2)
    (hbd : ∀ t ∈ Icc t0 (L / 2), |deriv φ t| ≤ C0 * t ^ (s - 2)) :
    |φ (L / 2) - φ t0| ≤ C0 / (1 - s) * t0 ^ (s - 1) := by
  have hFTC : ∫ t in t0..(L / 2), deriv φ t = φ (L / 2) - φ t0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => (hφ.differentiable (by simp) x).hasDerivAt)
      (Continuous.intervalIntegrable (hφ.continuous_deriv (by simp)) _ _)
  have hcont : ContinuousOn (fun t : ℝ => C0 * t ^ (s - 2)) (uIcc t0 (L / 2)) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    left
    rw [Set.uIcc_of_le ht0L] at hx
    show x ≠ 0
    exact ne_of_gt (by linarith [hx.1])
  have hle : |∫ t in t0..(L / 2), deriv φ t| ≤ ∫ t in t0..(L / 2), C0 * t ^ (s - 2) := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le ht0L
      (ae_of_all _ fun t ht => ?_) hcont.intervalIntegrable
    rw [Real.norm_eq_abs]
    exact hbd t ⟨ht.1.le, ht.2⟩
  rw [hFTC, intervalIntegral.integral_const_mul] at hle
  have hint := integral_rpow_sub_two_le hs0 hs1 ht1 ht0L
  calc |φ (L / 2) - φ t0| ≤ C0 * ∫ t in t0..(L / 2), t ^ (s - 2) := hle
    _ ≤ C0 * (t0 ^ (s - 1) / (1 - s)) := mul_le_mul_of_nonneg_left hint hC0
    _ = C0 / (1 - s) * t0 ^ (s - 1) := by ring


/-- The differences part of Lemma 5.7, first claim: for a smooth `L`-periodic `ψ`
with `|ψ'| ≤ C_0 w_1` on the circle `L𝕋` and every `u` with `|u| ≥ 1`,
`|ψ(u) - ψ(L/2)| ≤ C_0 (1-s)^{-1} |u|^{s-1}`. The antipode of `0` on `L𝕋` is `L/2`. -/
theorem gradSplit_antipode_bound {s a K L C0 : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    (hC0 : 0 ≤ C0) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hper : Function.Periodic ψ L)
    (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K L t) {u : ℝ} (hu : 1 ≤ circDist L u) :
    |ψ u - ψ (L / 2)| ≤ C0 / (1 - s) * circDist L u ^ (s - 1) := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = round (u / L) := ⟨_, rfl⟩
  have hL0 : L ≠ 0 := hL.ne'
  -- The representative `u' = u - L n` of `u` lies in `[-L/2, L/2]`.
  have hcirc : circDist L u = |u - L * n| := by rw [circDist, hn]
  have hψu : ψ u = ψ (u - L * n) := by
    have h := hper.int_mul n (u - L * n)
    rw [show u - L * n + n * L = u by ring] at h
    exact h
  have hhalf : ψ (L / 2) = ψ (-(L / 2)) := by
    have h := hper (-(L / 2))
    rw [show -(L / 2) + L = L / 2 by ring] at h
    exact h
  have hu'L : |u - L * n| ≤ L / 2 := by
    have h := abs_sub_round (u / L)
    rw [← hn] at h
    rw [show u - L * n = L * (u / L - n) by field_simp, abs_mul, abs_of_pos hL]
    calc L * |u / L - n| ≤ L * (1 / 2) := mul_le_mul_of_nonneg_left h hL.le
      _ = L / 2 := by ring
  rw [hcirc] at hu ⊢
  rcases le_or_gt 0 (u - L * n) with h0 | h0
  · -- The representative is nonnegative, so it equals `|u|`.
    rw [abs_of_nonneg h0] at hu ⊢
    rw [hψu, abs_sub_comm]
    refine abs_sub_antipode_le_of_mem hs0 hs1 hC0 hψ hu (by linarith [abs_le.mp hu'L]) ?_
    intro t ht
    have hct : circDist L t = t := circDist_of_mem_Icc hL (by linarith [ht.1]) ht.2
    have ht1 : 1 ≤ circDist L t := by rw [hct]; exact le_trans hu ht.1
    rw [hct] at ht1
    have := hbd t
    rw [gradWeightOne_of_one_le (by rw [hct]; exact ht1), hct] at this
    exact this
  · -- The representative is negative: reflect `ψ` through `0`.
    rw [abs_of_neg h0] at hu ⊢
    set φ : ℝ → ℝ := fun t => ψ (-t) with hφdef
    have hφ : ContDiff ℝ ∞ φ := hψ.comp contDiff_neg
    have hφhalf : φ (L / 2) = ψ (L / 2) := by
      show ψ (-(L / 2)) = ψ (L / 2)
      exact hhalf.symm
    have hφv : φ (-(u - L * n)) = ψ (u - L * n) := by simp [hφdef]
    rw [hψu, ← hφv, ← hφhalf, abs_sub_comm]
    refine abs_sub_antipode_le_of_mem hs0 hs1 hC0 hφ hu (by linarith [abs_le.mp hu'L]) ?_
    intro t ht
    have hct : circDist L (-t) = t := circDist_neg_of_mem_Icc hL (by linarith [ht.1]) ht.2
    have ht1 : 1 ≤ circDist L (-t) := by rw [hct]; exact le_trans hu ht.1
    have hderiv : deriv φ t = -deriv ψ (-t) := deriv_comp_neg ψ t
    rw [hderiv, abs_neg]
    have := hbd (-t)
    rw [gradWeightOne_of_one_le ht1, hct] at this
    exact this

end Riesz1

end
