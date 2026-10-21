/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodComparison
public import Riesz1.Variance.Window
public import Riesz1.ToMathlib.Calculus.PeriodicSegmentBound

/-!
# The translation error, term by term

Part of Lemma 5.2 (the rotation part), translation error. For an anchored vector `y`
with `y_0 = 0` and a shift `D`, the translation error is

`Δ_D(y) = ∑_{i ∈ I_γ} f((N y_i - D)/K) - ∑_{i ∈ I_γ} f(y_i/ℓ)`, with `K = N ℓ`,

where `I_γ` is the window centred at label `0`. This file proves the term-by-term
bound. Each term is an increment of the periodic kernel `f` over a segment of length `D/K`, and the
segment lemma bounds it by `D/K` times the derivative majorant at the circle distance of `y_i`,
shifted by `D/K`.

The derivative majorant is the bound of the derivative hypothesis of Lemma 5.2, read as a
function of the distance `|u|`. Its two indicators are replaced by their sum, which is antitone
and still dominates the hypothesis.
-/

@[expose] public section

open Finset Set

namespace Riesz1

/-- The translation error `Δ_D(y)`, with the window `I_γ` centred at
label `0`, the kernel `f`, the cell `ℓ`, and the shift `D`. -/
noncomputable def translationError (N : ℕ+) (ℓ γ : ℝ) (f : ℝ → ℝ) (D : ℝ)
    (y : Fin (N : ℕ) → ℝ) : ℝ :=
  ∑ i ∈ window N (((N : ℕ) : ℝ) * ℓ) γ, f ((((N : ℕ) : ℝ) * y i - D) / (((N : ℕ) : ℝ) * ℓ)) -
    ∑ i ∈ window N (((N : ℕ) : ℝ) * ℓ) γ, f (y i / ℓ)

/-- The derivative majorant at the distance `t = |u|`: the sum of the two indicator terms of the
derivative hypothesis of Lemma 5.2, with `K` the window scale. -/
noncomputable def derivMajorant (K lam s t : ℝ) : ℝ :=
  1 / (max t K⁻¹) ^ (1 + lam) + 1 / (max t 2) ^ (3 - s)

/-- A positive base raised to a nonnegative power has an antitone reciprocal. -/
theorem one_div_rpow_antitoneOn {a p : ℝ} (ha : 0 < a) (hp : 0 ≤ p) :
    AntitoneOn (fun t : ℝ => 1 / (max t a) ^ p) (Ici 0) := by
  intro t _ t' _ htt'
  have hmax : max t a ≤ max t' a := max_le_max htt' le_rfl
  have hpos : 0 < max t a := lt_of_lt_of_le ha (le_max_right _ _)
  have hp' : (max t a) ^ p ≤ (max t' a) ^ p := Real.rpow_le_rpow hpos.le hmax hp
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hpos p) hp'

/-- The derivative majorant is antitone on `[0, ∞)` for a positive window scale. -/
theorem derivMajorant_antitoneOn {K lam s : ℝ} (hK : 0 < K) (hlam : 0 ≤ lam) (hs : s < 3) :
    AntitoneOn (derivMajorant K lam s) (Ici 0) := by
  intro t ht t' ht' htt'
  have h1 := one_div_rpow_antitoneOn (a := K⁻¹) (p := 1 + lam) (inv_pos.2 hK) (by linarith)
    ht ht' htt'
  have h2 := one_div_rpow_antitoneOn (a := 2) (p := 3 - s) (by norm_num) (by linarith)
    ht ht' htt'
  unfold derivMajorant
  exact add_le_add h1 h2

/-- The derivative bound of Lemma 5.2, as stated with two indicators,
is dominated by the derivative majorant. -/
theorem abs_deriv_le_derivMajorant {K lam s : ℝ} (hK : 0 < K) {f : ℝ → ℝ} {u : ℝ}
    (hc : |deriv f u| ≤ (if |u| ≤ 2 then 1 / (max |u| K⁻¹) ^ (1 + lam) else 0) +
      (if 2 ≤ |u| then 1 / |u| ^ (3 - s) else 0)) :
    |deriv f u| ≤ derivMajorant K lam s |u| := by
  unfold derivMajorant
  have hA : (if |u| ≤ 2 then 1 / (max |u| K⁻¹) ^ (1 + lam) else 0) ≤
      1 / (max |u| K⁻¹) ^ (1 + lam) := by
    split_ifs
    · exact le_rfl
    · exact div_nonneg zero_le_one
        (Real.rpow_nonneg (le_max_of_le_right (inv_nonneg.2 hK.le)) _)
  have hB : (if 2 ≤ |u| then 1 / |u| ^ (3 - s) else 0) ≤ 1 / (max |u| 2) ^ (3 - s) := by
    split_ifs with h2
    · rw [max_eq_left h2]
    · exact div_nonneg zero_le_one (Real.rpow_nonneg (le_max_of_le_right (by norm_num)) _)
  linarith

/-- **Term-by-term translation bound.** Let `K = N ℓ > 0`, and let `f` be `C¹` with period `1/ℓ`
satisfying the derivative majorant on the half period. For an anchored position `v` with circle
distance `circDist 1 v` from the origin, and a shift `0 ≤ D ≤ N ℓ` with `D/K ≤ 1/ℓ`, the
increment `f((N v - D)/K) - f(v/ℓ)` is at most `(D/K)` times the derivative majorant at
`max(circDist 1 v / ℓ - D/K, 0)`. -/
theorem translation_term_le {N : ℕ+} {ℓ lam s : ℝ} (hℓ : 0 < ℓ)
    (hK : 0 < ((N : ℕ) : ℝ) * ℓ) (hs : s < 3) (hlam : 0 ≤ lam) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hper : Function.Periodic f (1 / ℓ))
    (hder : ∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
      |deriv f u| ≤ derivMajorant (((N : ℕ) : ℝ) * ℓ) lam s |u|)
    {D : ℝ} (hD0 : 0 ≤ D) (hDL : D / (((N : ℕ) : ℝ) * ℓ) ≤ 1 / ℓ) (v : ℝ) :
    |f ((((N : ℕ) : ℝ) * v - D) / (((N : ℕ) : ℝ) * ℓ)) - f (v / ℓ)| ≤
      D / (((N : ℕ) : ℝ) * ℓ) *
        derivMajorant (((N : ℕ) : ℝ) * ℓ) lam s
          (max (circDist 1 v / ℓ - D / (((N : ℕ) : ℝ) * ℓ)) 0) := by
  set K : ℝ := ((N : ℕ) : ℝ) * ℓ with hK_def
  set h : ℝ := D / K with hh_def
  set r : ℤ := round v with hr_def
  set u : ℝ := (v - (r : ℝ)) / ℓ with hu_def
  have hN : ((N : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ((N : ℕ) : ℝ) := by
      have hK' := hK
      rw [hK_def] at hK'
      exact pos_of_mul_pos_left hK' hℓ.le
    exact this.ne'
  -- The two arguments of `f` differ from `u` and `u - h` by the period `1 / ℓ`.
  have hv : v / ℓ = u + (r : ℝ) * (1 / ℓ) := by
    rw [hu_def]
    ring
  have hx0 : (((N : ℕ) : ℝ) * v - D) / K = v / ℓ - h := by
    rw [hh_def, hK_def, sub_div, mul_div_mul_left _ _ hN]
  have hx : (((N : ℕ) : ℝ) * v - D) / K = (u - h) + (r : ℝ) * (1 / ℓ) := by
    rw [hx0, hv]
    ring
  have hshift : ∀ y : ℝ, f (y + (r : ℝ) * (1 / ℓ)) = f y := by
    intro y
    rw [show y + (r : ℝ) * (1 / ℓ) = y - ((-r : ℤ) : ℝ) * (1 / ℓ) by push_cast; ring]
    exact hper.sub_int_mul_eq (-r)
  -- The point `u` lies in the half period, since `|v - round v| ≤ 1/2`.
  have hru : |u| ≤ 1 / ℓ / 2 := by
    have hround : |v - (r : ℝ)| ≤ 1 / 2 := abs_sub_round v
    rw [hu_def, abs_div, abs_of_pos hℓ, show 1 / ℓ / 2 = (1 / 2) / ℓ by ring]
    exact (div_le_div_iff_of_pos_right hℓ).2 hround
  have hcirc : |u| = circDist 1 v / ℓ := by
    rw [APG.circDist_one_eq_abs_sub_round, hu_def, abs_div, abs_of_pos hℓ]
  have hh0 : 0 ≤ h := div_nonneg hD0 hK.le
  have hseg := abs_sub_le_of_periodic_deriv_bound (L := 1 / ℓ) hf hper
    (derivMajorant_antitoneOn hK hlam hs) hder hru hh0 hDL
  rw [hx, hv, hshift, hshift, abs_sub_comm, ← hcirc]
  exact hseg

/-- **Translation error, term by term.** The translation error is at most the sum over the window
of the term bounds of `translation_term_le`. -/
theorem abs_translationError_le_sum (N : ℕ+) {ℓ γ lam s : ℝ} (hℓ : 0 < ℓ)
    (hK : 0 < ((N : ℕ) : ℝ) * ℓ) (hs : s < 3) (hlam : 0 ≤ lam) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hper : Function.Periodic f (1 / ℓ))
    (hder : ∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
      |deriv f u| ≤ derivMajorant (((N : ℕ) : ℝ) * ℓ) lam s |u|)
    {D : ℝ} (hD0 : 0 ≤ D) (hDL : D / (((N : ℕ) : ℝ) * ℓ) ≤ 1 / ℓ) (y : Fin (N : ℕ) → ℝ) :
    |translationError N ℓ γ f D y| ≤
      ∑ i ∈ window N (((N : ℕ) : ℝ) * ℓ) γ, D / (((N : ℕ) : ℝ) * ℓ) *
        derivMajorant (((N : ℕ) : ℝ) * ℓ) lam s
          (max (circDist 1 (y i) / ℓ - D / (((N : ℕ) : ℝ) * ℓ)) 0) := by
  unfold translationError
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact translation_term_le hℓ hK hs hlam hf hper hder hD0 hDL (y i)

end Riesz1
