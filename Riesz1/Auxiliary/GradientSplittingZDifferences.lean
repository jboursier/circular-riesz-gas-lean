/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingZBounds

/-!
# Divided differences of the gradient splitting

The differences part of Lemma 5.7 and its definitions: the divided difference `Z` and its
derivatives `Z_x, Z_y, Z_xy`, and the circle `ℓ^{-1}𝕋` with circular distance `circDist`.

The circle is `ℓ^{-1}𝕋 = ℝ/ℓ^{-1}ℤ`, so `L = ℓ^{-1}`, and the weights are `w_1, w_2` of
the data part of Lemma 5.7 evaluated at `x/ℓ`.

This file states the definitions in the variables `x, y` and proves the bounds on
`Z`, `Z_x`, `Z_y`, `Z_xy` that come from the derivative estimates of
`GradientSplittingZBounds.lean`. The finite-difference bounds of the paper are not in this file.
-/

@[expose] public section

open Set MeasureTheory
open scoped ContDiff

namespace Riesz1

/-- The divided difference `Z(x,y) = ∫_0^1 ψ'((x + θ(y-x))/ℓ) dθ`. -/
noncomputable def gradZ (ψ : ℝ → ℝ) (ℓ x y : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..1, deriv ψ ((x + θ * (y - x)) / ℓ)

/-- `Z_x = (Z - ψ'(x/ℓ))/(y - x)` of the differences part of Lemma 5.7. -/
noncomputable def gradZx (ψ : ℝ → ℝ) (ℓ x y : ℝ) : ℝ :=
  (gradZ ψ ℓ x y - deriv ψ (x / ℓ)) / (y - x)

/-- `Z_y = (ψ'(y/ℓ) - Z)/(y - x)` of the differences part of Lemma 5.7. -/
noncomputable def gradZy (ψ : ℝ → ℝ) (ℓ x y : ℝ) : ℝ :=
  (deriv ψ (y / ℓ) - gradZ ψ ℓ x y) / (y - x)

/-- `Z_xy = (Z_y - Z_x)/(y - x)` of the differences part of Lemma 5.7. -/
noncomputable def gradZxy (ψ : ℝ → ℝ) (ℓ x y : ℝ) : ℝ :=
  (gradZy ψ ℓ x y - gradZx ψ ℓ x y) / (y - x)

/-- The divided difference is the average of the derivative in the variables `u = x/ℓ`. -/
lemma gradZ_eq_gradZavg (ψ : ℝ → ℝ) (ℓ x y : ℝ) :
    gradZ ψ ℓ x y = gradZavg ψ (x / ℓ) (y / ℓ) := by
  unfold gradZ gradZavg
  congr 1
  funext θ
  congr 1
  ring

/-- If `|A| ≤ B d` with `d > 0`, then `|A/d| ≤ B`. -/
lemma abs_div_le_of_abs_le_mul {A d B : ℝ} (hd : 0 < d) (h : |A| ≤ B * d) : |A / d| ≤ B := by
  rw [abs_div, abs_of_pos hd, div_le_iff₀ hd]
  exact h

/-- The constant of the divided-difference bounds: it dominates `gradZConst` and `2 (gradZConst+1)`. -/
noncomputable def gradZTotalConst (a s : ℝ) : ℝ := 2 * (gradZConst a s + 1) + 1 / (1 - s)

lemma gradZConst_nonneg {a s : ℝ} (ha1 : a < 1) (hs1 : s < 1) : 0 ≤ gradZConst a s := by
  unfold gradZConst
  have h1 : 0 ≤ 1 / (1 - a) := div_nonneg zero_le_one (by linarith)
  have h2 : 0 ≤ 1 / (1 - s) := div_nonneg zero_le_one (by linarith)
  linarith

lemma gradZTotalConst_facts {a s : ℝ} (ha1 : a < 1) (hs1 : s < 1) :
    gradZConst a s ≤ gradZTotalConst a s ∧ 2 * (gradZConst a s + 1) ≤ gradZTotalConst a s ∧
      1 / (1 - s) ≤ gradZTotalConst a s ∧ 0 ≤ gradZTotalConst a s := by
  have h0 := gradZConst_nonneg ha1 hs1
  have h2 : 0 ≤ 1 / (1 - s) := div_nonneg zero_le_one (by linarith)
  unfold gradZTotalConst
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The `Z_x` bound: `|Z_x| ≤ C C_0 ℓ^{-1}(w_2(x/ℓ) + w_2(y/ℓ))` with `C = gradZConst + 1`. -/
lemma gradZx_abs_le {s a K ℓ C0 : ℝ} {ψ : ℝ → ℝ} (hℓ : 0 < ℓ) (hs0 : 0 < s) (hs1 : s < 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hK : 1 ≤ K) (hC0 : 0 ≤ C0) (hψ : ContDiff ℝ ∞ ψ)
    (hper : Function.Periodic ψ ℓ⁻¹) (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K ℓ⁻¹ t)
    (hbd2 : ∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s a K ℓ⁻¹ t) {x y : ℝ}
    (hd : 0 < |y - x|) :
    |gradZx ψ ℓ x y| ≤ (gradZConst a s + 1) * C0 * ℓ⁻¹ *
      (gradWeightTwo s a K ℓ⁻¹ (x / ℓ) + gradWeightTwo s a K ℓ⁻¹ (y / ℓ)) := by
  have hL : 0 < ℓ⁻¹ := inv_pos.mpr hℓ
  have hqp : |y / ℓ - x / ℓ| = |y - x| * ℓ⁻¹ := by
    rw [show y / ℓ - x / ℓ = (y - x) * ℓ⁻¹ by ring, abs_mul, abs_of_pos hL]
  have h := gradZavg_sub_deriv_le (s := s) (a := a) (K := K) (ψ := ψ) hL hs0 hs1 ha0 ha1 hK hC0
    hψ hper hbd hbd2 (x / ℓ) (y / ℓ)
  rw [hqp] at h
  unfold gradZx
  rw [gradZ_eq_gradZavg, abs_div]
  apply div_le_of_le_mul₀ hd.le (mul_nonneg (mul_nonneg (mul_nonneg (by linarith [gradZConst_nonneg ha1 hs1]) hC0)
    (inv_nonneg.mpr hℓ.le)) (add_nonneg (gradWeightTwo_nonneg hK) (gradWeightTwo_nonneg hK)))
  calc |gradZavg ψ (x / ℓ) (y / ℓ) - deriv ψ (x / ℓ)|
      ≤ (gradZConst a s + 1) * C0 * (|y - x| * ℓ⁻¹) *
        (gradWeightTwo s a K ℓ⁻¹ (x / ℓ) + gradWeightTwo s a K ℓ⁻¹ (y / ℓ)) := h
    _ = (gradZConst a s + 1) * C0 * ℓ⁻¹ *
        (gradWeightTwo s a K ℓ⁻¹ (x / ℓ) + gradWeightTwo s a K ℓ⁻¹ (y / ℓ)) * |y - x| := by ring

/-- The `Z_y` bound: `|Z_y| ≤ C C_0 ℓ^{-1}(w_2(x/ℓ) + w_2(y/ℓ))` with `C = gradZConst + 1`. -/
lemma gradZy_abs_le {s a K ℓ C0 : ℝ} {ψ : ℝ → ℝ} (hℓ : 0 < ℓ) (hs0 : 0 < s) (hs1 : s < 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hK : 1 ≤ K) (hC0 : 0 ≤ C0) (hψ : ContDiff ℝ ∞ ψ)
    (hper : Function.Periodic ψ ℓ⁻¹) (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K ℓ⁻¹ t)
    (hbd2 : ∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s a K ℓ⁻¹ t) {x y : ℝ}
    (hd : 0 < |y - x|) :
    |gradZy ψ ℓ x y| ≤ (gradZConst a s + 1) * C0 * ℓ⁻¹ *
      (gradWeightTwo s a K ℓ⁻¹ (x / ℓ) + gradWeightTwo s a K ℓ⁻¹ (y / ℓ)) := by
  have hL : 0 < ℓ⁻¹ := inv_pos.mpr hℓ
  have hqp : |y / ℓ - x / ℓ| = |y - x| * ℓ⁻¹ := by
    rw [show y / ℓ - x / ℓ = (y - x) * ℓ⁻¹ by ring, abs_mul, abs_of_pos hL]
  have h := gradZavg_sub_deriv_le_right (s := s) (a := a) (K := K) (ψ := ψ) hL hs0 hs1 ha0 ha1 hK
    hC0 hψ hper hbd hbd2 (x / ℓ) (y / ℓ)
  rw [hqp] at h
  unfold gradZy
  rw [gradZ_eq_gradZavg, abs_div, abs_sub_comm (deriv ψ (y / ℓ))]
  apply div_le_of_le_mul₀ hd.le (mul_nonneg (mul_nonneg (mul_nonneg (by linarith [gradZConst_nonneg ha1 hs1]) hC0)
    (inv_nonneg.mpr hℓ.le)) (add_nonneg (gradWeightTwo_nonneg hK) (gradWeightTwo_nonneg hK)))
  calc |gradZavg ψ (x / ℓ) (y / ℓ) - deriv ψ (y / ℓ)|
      ≤ (gradZConst a s + 1) * C0 * (|y - x| * ℓ⁻¹) *
        (gradWeightTwo s a K ℓ⁻¹ (x / ℓ) + gradWeightTwo s a K ℓ⁻¹ (y / ℓ)) := h
    _ = (gradZConst a s + 1) * C0 * ℓ⁻¹ *
        (gradWeightTwo s a K ℓ⁻¹ (x / ℓ) + gradWeightTwo s a K ℓ⁻¹ (y / ℓ)) * |y - x| := by ring

/-- The differences part of Lemma 5.7: the data are those of
the data part of Lemma 5.7 with `a = 1 - s + α`, `K = Nℓ`, and `L = ℓ^{-1}`. The constant `C`
depends only on `s` and `α`. The statement gathers the first claim (the antipodal bound), the
bound on `Z`, the bounds on `Z_x`, `Z_y`, and the bound on `Z_xy`. -/
theorem gradSplit_differences_bounds {s α : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hα0 : s - 1 ≤ α)
    (hα1 : α < s / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (ℓ C0 : ℝ) (ψ : ℝ → ℝ),
      2 ≤ N → 0 < ℓ → ℓ ≤ 1 → 1 ≤ N * ℓ → 0 ≤ C0 → ContDiff ℝ ∞ ψ →
      Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) (N * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ t) →
      (∀ u : ℝ, 1 ≤ circDist ℓ⁻¹ u →
        |ψ u - ψ ((2 * ℓ)⁻¹)| ≤ C * C0 * circDist ℓ⁻¹ u ^ (s - 1)) ∧
      (∀ x y : ℝ, |gradZ ψ ℓ x y| ≤ C * C0 *
        (gradWeightOne s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
          gradWeightOne s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ))) ∧
      (∀ x y : ℝ, 0 < |y - x| →
        |gradZx ψ ℓ x y| + |gradZy ψ ℓ x y| ≤ C * C0 * ℓ⁻¹ *
          (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ))) ∧
      (∀ x y : ℝ, 0 < |y - x| →
        |gradZxy ψ ℓ x y| ≤ C * C0 * ℓ⁻¹ * |y - x|⁻¹ *
          (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ))) := by
  have ha1 : 1 - s + α < 1 := by linarith
  have ha0 : 0 ≤ 1 - s + α := by linarith
  obtain ⟨hC1, hC2, hC3, hC4⟩ := gradZTotalConst_facts (a := 1 - s + α) (s := s) ha1 hs1
  refine ⟨gradZTotalConst (1 - s + α) s, ?_, ?_⟩
  · have h0 := gradZConst_nonneg ha1 hs1
    have hpos : 0 < 1 / (1 - s) := div_pos one_pos (by linarith)
    unfold gradZTotalConst
    linarith
  intro N ℓ C0 ψ hN hℓ hℓ1 hK hC0 hψ hper hbd hbd2
  have hL : 0 < ℓ⁻¹ := inv_pos.mpr hℓ
  have hK0 : 0 < N * ℓ := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the antipodal bound
    intro u hu
    have h := gradSplit_antipode_bound (s := s) (a := 1 - s + α) (K := N * ℓ) (L := ℓ⁻¹)
      (C0 := C0) hs0 hs1 hL hC0 hψ hper hbd hu
    have e : (2 * ℓ)⁻¹ = ℓ⁻¹ / 2 := by ring
    rw [e]
    refine le_trans h ?_
    have hc : C0 / (1 - s) ≤ gradZTotalConst (1 - s + α) s * C0 := by
      calc C0 / (1 - s) = C0 * (1 / (1 - s)) := by ring
        _ ≤ C0 * gradZTotalConst (1 - s + α) s := mul_le_mul_of_nonneg_left hC3 hC0
        _ = gradZTotalConst (1 - s + α) s * C0 := mul_comm _ _
    exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (circDist_nonneg _ _) _)
  · -- the bound on `Z`
    intro x y
    rw [gradZ_eq_gradZavg]
    have h := gradZavg_abs_le (s := s) (a := 1 - s + α) (K := N * ℓ) hL hs0 hs1 ha0 ha1 hK hC0
      hψ hper hbd (x / ℓ) (y / ℓ)
    have hS : 0 ≤ gradWeightOne s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
        gradWeightOne s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ) :=
      add_nonneg (gradWeightOne_nonneg hK) (gradWeightOne_nonneg hK)
    exact le_trans h (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hC0) hS)
  · -- the bounds on `Z_x` and `Z_y`
    intro x y hd
    have h1 := gradZx_abs_le (s := s) (a := 1 - s + α) (K := N * ℓ) hℓ hs0 hs1 ha0 ha1 hK hC0
      hψ hper hbd hbd2 hd
    have h2 := gradZy_abs_le (s := s) (a := 1 - s + α) (K := N * ℓ) hℓ hs0 hs1 ha0 ha1 hK hC0
      hψ hper hbd hbd2 hd
    have hS : 0 ≤ gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
        gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ) :=
      add_nonneg (gradWeightTwo_nonneg hK) (gradWeightTwo_nonneg hK)
    calc |gradZx ψ ℓ x y| + |gradZy ψ ℓ x y|
        ≤ (gradZConst (1 - s + α) s + 1) * C0 * ℓ⁻¹ *
          (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ)) +
          (gradZConst (1 - s + α) s + 1) * C0 * ℓ⁻¹ *
          (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ)) := add_le_add h1 h2
      _ = 2 * (gradZConst (1 - s + α) s + 1) * C0 * ℓ⁻¹ *
          (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ)) := by ring
      _ ≤ gradZTotalConst (1 - s + α) s * C0 * ℓ⁻¹ *
          (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC2 hC0) hL.le) hS
  · -- the bound on `Z_xy`
    intro x y hd
    have h1 := gradZx_abs_le (s := s) (a := 1 - s + α) (K := N * ℓ) hℓ hs0 hs1 ha0 ha1 hK hC0
      hψ hper hbd hbd2 hd
    have h2 := gradZy_abs_le (s := s) (a := 1 - s + α) (K := N * ℓ) hℓ hs0 hs1 ha0 ha1 hK hC0
      hψ hper hbd hbd2 hd
    have hS : 0 ≤ gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
        gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ) :=
      add_nonneg (gradWeightTwo_nonneg hK) (gradWeightTwo_nonneg hK)
    have hnum : |gradZy ψ ℓ x y - gradZx ψ ℓ x y| ≤
        2 * ((gradZConst (1 - s + α) s + 1) * C0 * ℓ⁻¹ *
          (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ))) := by
      have := abs_sub (gradZy ψ ℓ x y) (gradZx ψ ℓ x y)
      linarith
    have hdiv : |gradZxy ψ ℓ x y| ≤ 2 * ((gradZConst (1 - s + α) s + 1) * C0 * ℓ⁻¹ *
          (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ))) / |y - x| := by
      unfold gradZxy
      rw [abs_div]
      exact div_le_div_of_nonneg_right hnum hd.le
    refine le_trans hdiv ?_
    rw [div_eq_mul_inv]
    have hinv : 0 ≤ |y - x|⁻¹ := inv_nonneg.mpr hd.le
    have hcoef : 2 * (gradZConst (1 - s + α) s + 1) ≤ gradZTotalConst (1 - s + α) s := hC2
    have hcs : 2 * ((gradZConst (1 - s + α) s + 1) * C0 * ℓ⁻¹ *
          (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ))) =
        2 * (gradZConst (1 - s + α) s + 1) * C0 * ℓ⁻¹ *
          (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ)) := by ring
    rw [hcs]
    have hbig : 2 * (gradZConst (1 - s + α) s + 1) * C0 * ℓ⁻¹ *
          (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ)) ≤
        gradZTotalConst (1 - s + α) s * C0 * ℓ⁻¹ *
          (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef hC0) hL.le) hS
    calc _ ≤ gradZTotalConst (1 - s + α) s * C0 * ℓ⁻¹ *
          (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ)) * |y - x|⁻¹ :=
          mul_le_mul_of_nonneg_right hbig hinv
      _ = _ := by ring

/-- The weight `w_2` on a lattice-free hull of three points is at most the largest of their values. -/
lemma gradWeightTwo_le_max_three {s a K L p P Q t : ℝ} (hL : 0 < L) (hs1 : s < 1) (ha : 0 ≤ a)
    (hK : 1 ≤ K) (hno : ∀ n : ℤ, ¬(n * L ∈ uIcc (min p (min P Q)) (max p (max P Q))))
    (ht : t ∈ uIcc (min p (min P Q)) (max p (max P Q))) :
    gradWeightTwo s a K L t ≤
      max (gradWeightTwo s a K L p) (max (gradWeightTwo s a K L P) (gradWeightTwo s a K L Q)) := by
  have hlo : gradWeightTwo s a K L (min p (min P Q)) ≤
      max (gradWeightTwo s a K L p) (max (gradWeightTwo s a K L P) (gradWeightTwo s a K L Q)) := by
    rcases min_choice p (min P Q) with h | h <;> rw [h]
    · exact le_max_left _ _
    · rcases min_choice P Q with h' | h' <;> rw [h']
      · exact le_trans (le_max_left _ _) (le_max_right _ _)
      · exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hhi : gradWeightTwo s a K L (max p (max P Q)) ≤
      max (gradWeightTwo s a K L p) (max (gradWeightTwo s a K L P) (gradWeightTwo s a K L Q)) := by
    rcases max_choice p (max P Q) with h | h <;> rw [h]
    · exact le_max_left _ _
    · rcases max_choice P Q with h' | h' <;> rw [h']
      · exact le_trans (le_max_left _ _) (le_max_right _ _)
      · exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hmax := gradWeightTwo_le_max_uIcc (s := s) (a := a) (K := K) (L := L)
    (p := min p (min P Q)) (q := max p (max P Q)) hL hs1 ha hK hno ht
  exact le_trans hmax (max_le hlo hhi)

/-- The differences part of Lemma 5.7, finite difference (iv), lattice-free case: if
the hull of `{p, P, Q}` contains no point of `Lℤ`, then `|Z(p,Q) - Z(p,P)| ≤ C_0 M |Q - P|`, where `M`
is the largest of `w_2(p)`, `w_2(P)`, `w_2(Q)`, and `Z(p,t) = gradZavg ψ p t`. The case in which the
hull contains a point of `Lℤ` is not proved here. -/
lemma gradZavg_sub_gradZavg_le_of_hull_no_lattice {s a K L C0 : ℝ} {ψ : ℝ → ℝ} (hL : 0 < L)
    (hs1 : s < 1) (ha : 0 ≤ a) (hK : 1 ≤ K) (hC0 : 0 ≤ C0) (hψ : ContDiff ℝ ∞ ψ)
    (hbd2 : ∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s a K L t) {p P Q : ℝ}
    (hno : ∀ n : ℤ, ¬(n * L ∈ uIcc (min p (min P Q)) (max p (max P Q)))) :
    |gradZavg ψ p Q - gradZavg ψ p P| ≤
      C0 * max (gradWeightTwo s a K L p) (max (gradWeightTwo s a K L P) (gradWeightTwo s a K L Q)) *
        |Q - P| := by
  have hpH : p ∈ uIcc (min p (min P Q)) (max p (max P Q)) :=
    Set.mem_uIcc.mpr (Or.inl ⟨min_le_left _ _, le_max_left _ _⟩)
  have hPH : P ∈ uIcc (min p (min P Q)) (max p (max P Q)) :=
    Set.mem_uIcc.mpr (Or.inl ⟨le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (le_max_left _ _) (le_max_right _ _)⟩)
  have hQH : Q ∈ uIcc (min p (min P Q)) (max p (max P Q)) :=
    Set.mem_uIcc.mpr (Or.inl ⟨le_trans (min_le_right _ _) (min_le_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩)
  have hcont : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hint1 : IntervalIntegrable (fun θ : ℝ => deriv ψ (p + θ * (Q - p))) volume 0 1 :=
    (hcont.comp (continuous_const.add (continuous_id.mul continuous_const))).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun θ : ℝ => deriv ψ (p + θ * (P - p))) volume 0 1 :=
    (hcont.comp (continuous_const.add (continuous_id.mul continuous_const))).intervalIntegrable _ _
  have hM0 : 0 ≤ max (gradWeightTwo s a K L p)
      (max (gradWeightTwo s a K L P) (gradWeightTwo s a K L Q)) :=
    le_trans (gradWeightTwo_nonneg (s := s) (a := a) (L := L) hK (u := p)) (le_max_left _ _)
  unfold gradZavg
  rw [← intervalIntegral.integral_sub hint1 hint2]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun θ : ℝ => deriv ψ (p + θ * (Q - p)) - deriv ψ (p + θ * (P - p)))
    (C := C0 * max (gradWeightTwo s a K L p)
      (max (gradWeightTwo s a K L P) (gradWeightTwo s a K L Q)) * |Q - P|)
    (fun θ hθ => by
      have hθ' : θ ∈ uIcc (0 : ℝ) 1 := Set.uIoc_subset_uIcc hθ
      rw [uIcc_of_le zero_le_one, Set.mem_Icc] at hθ'
      rw [Real.norm_eq_abs]
      have ht1 : p + θ * (Q - p) ∈ uIcc (min p (min P Q)) (max p (max P Q)) :=
        Set.uIcc_subset_uIcc hpH hQH (mem_uIcc_segment hθ'.1 hθ'.2)
      have ht2 : p + θ * (P - p) ∈ uIcc (min p (min P Q)) (max p (max P Q)) :=
        Set.uIcc_subset_uIcc hpH hPH (mem_uIcc_segment hθ'.1 hθ'.2)
      have hsub : uIcc (p + θ * (P - p)) (p + θ * (Q - p)) ⊆
          uIcc (min p (min P Q)) (max p (max P Q)) :=
        Set.uIcc_subset_uIcc ht2 ht1
      have h1 := gradDeriv_sub_le hψ (M := C0 * max (gradWeightTwo s a K L p)
          (max (gradWeightTwo s a K L P) (gradWeightTwo s a K L Q)))
        (p := p + θ * (P - p)) (t := p + θ * (Q - p))
        (fun τ hτ => by
          calc |deriv (deriv ψ) τ| ≤ C0 * gradWeightTwo s a K L τ := hbd2 τ
            _ ≤ C0 * max (gradWeightTwo s a K L p)
                (max (gradWeightTwo s a K L P) (gradWeightTwo s a K L Q)) :=
              mul_le_mul_of_nonneg_left (gradWeightTwo_le_max_three hL hs1 ha hK hno (hsub hτ))
                hC0)
      have hlen : |p + θ * (Q - p) - (p + θ * (P - p))| ≤ |Q - P| := by
        rw [show p + θ * (Q - p) - (p + θ * (P - p)) = θ * (Q - P) by ring, abs_mul,
          abs_of_nonneg hθ'.1]
        exact mul_le_of_le_one_left (abs_nonneg _) hθ'.2
      calc |deriv ψ (p + θ * (Q - p)) - deriv ψ (p + θ * (P - p))|
          ≤ C0 * max (gradWeightTwo s a K L p)
              (max (gradWeightTwo s a K L P) (gradWeightTwo s a K L Q)) *
            |p + θ * (Q - p) - (p + θ * (P - p))| := h1
        _ ≤ C0 * max (gradWeightTwo s a K L p)
              (max (gradWeightTwo s a K L P) (gradWeightTwo s a K L Q)) * |Q - P| :=
            mul_le_mul_of_nonneg_left hlen (mul_nonneg hC0 hM0))
  have e : |(1 : ℝ) - 0| = 1 := by norm_num
  rw [Real.norm_eq_abs] at hb
  rw [e, mul_one] at hb
  exact hb

end Riesz1

end
