/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.PSeries
public import Riesz1.Frozen.CircleSobolev

/-!
# Circle Sobolev membership from power-law decay of Fourier coefficients

A square integrable function on the unit circle whose Fourier coefficients decay like a power
`|k|^g` lies in `H^r(𝕋)` as soon as `2 r + 2 g < -1`. In the application the decay
exponent is `g = α - 1 + ε` and the Sobolev index is `r = (1 - s)/2`. The condition then reads
`α + ε < s / 2`, which is the admissibility range `α < s / 2`.

Theorem: `Riesz1.circleSobolev_of_coeff_decay`.
-/

public section

open MeasureTheory Filter

namespace Riesz1

/-- The power identity `(x ^ g) ^ 2 = x ^ (2 g)` for a positive real base `x`. -/
theorem rpow_sq_eq_rpow_two_mul {x : ℝ} (hx : 0 ≤ x) (g : ℝ) : (x ^ g) ^ 2 = x ^ (2 * g) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

/-- The summand bound: `|k|^{2r} (K |k|^g)^2 = K^2 |k|^{2r + 2g}` for a nonzero integer `k`. -/
theorem summand_le_majorant {r g K : ℝ} {k : ℤ} (hk : 0 < |(k : ℝ)|) {a : ℝ} (ha : 0 ≤ a)
    (hdec : a ≤ K * |(k : ℝ)| ^ g) :
    |(k : ℝ)| ^ (2 * r) * a ^ 2 ≤ K ^ 2 * |(k : ℝ)| ^ (2 * r + 2 * g) := by
  have hsq : a ^ 2 ≤ (K * |(k : ℝ)| ^ g) ^ 2 := pow_le_pow_left₀ ha hdec 2
  have hpos : 0 ≤ |(k : ℝ)| ^ (2 * r) := by positivity
  calc |(k : ℝ)| ^ (2 * r) * a ^ 2
      ≤ |(k : ℝ)| ^ (2 * r) * (K * |(k : ℝ)| ^ g) ^ 2 := mul_le_mul_of_nonneg_left hsq hpos
    _ = K ^ 2 * (|(k : ℝ)| ^ (2 * r) * (|(k : ℝ)| ^ g) ^ 2) := by ring
    _ = K ^ 2 * |(k : ℝ)| ^ (2 * r + 2 * g) := by
      rw [rpow_sq_eq_rpow_two_mul (abs_nonneg _), Real.rpow_add hk]

/-- **Sobolev membership from power decay.** Let `f : 𝕋 → ℂ` be square integrable, let
`r g K : ℝ` satisfy `2 r + 2 g < -1`, and let `1 ≤ k₀` be an integer. If every Fourier
coefficient of index `|k| ≥ k₀` satisfies `‖f̂(k)‖ ≤ K |k|^g`, then `f ∈ H^r(𝕋)`. Only the tail
of the coefficients is constrained. The finitely many remaining ones do not affect finiteness. -/
theorem circleSobolev_of_coeff_decay {r g K : ℝ} (hrg : 2 * r + 2 * g < -1)
    {f : UnitAddCircle → ℂ} (hf : MemLp f 2 volume) {k₀ : ℤ} (hk₀ : 1 ≤ k₀)
    (hdecay : ∀ k : ℤ, k₀ ≤ |k| → ‖fourierCoeff f k‖ ≤ K * |(k : ℝ)| ^ g) :
    CircleSobolev r f := by
  refine ⟨hf, ?_⟩
  -- The majorant `K² |k|^{2r + 2g}` is summable because `-(2r + 2g) > 1`.
  have hpow : Summable fun k : ℤ => |(k : ℝ)| ^ (-(-(2 * r + 2 * g))) :=
    Real.summable_abs_int_rpow (by linarith)
  rw [neg_neg] at hpow
  have hmajorant : Summable fun k : ℤ => K ^ 2 * |(k : ℝ)| ^ (2 * r + 2 * g) := hpow.mul_left _
  -- Indices with `k₀ ≤ |k|` form a cofinite set.
  have hcofinite : ∀ᶠ k : ℤ in cofinite, k₀ ≤ |k| := by
    rw [Filter.eventually_cofinite]
    refine (Set.finite_Icc (-k₀) k₀).subset ?_
    intro k hk
    simp only [Set.mem_ofPred_eq, not_le] at hk
    exact ⟨by linarith [neg_abs_le (k : ℤ)], by linarith [le_abs_self (k : ℤ)]⟩
  -- The real summand of `circleSobolevSq`, with the zero mode removed.
  have hu_summable : Summable fun k : ℤ =>
      if k = 0 then (0 : ℝ) else |(k : ℝ)| ^ (2 * r) * ‖fourierCoeff f k‖ ^ 2 := by
    refine Summable.of_norm_bounded_eventually hmajorant ?_
    filter_upwards [hcofinite] with k hk
    have hk1 : (1 : ℤ) ≤ |k| := le_trans hk₀ hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hk1
    have hkR : 0 < |(k : ℝ)| := by
      have h : (0 : ℤ) < |k| := by omega
      exact_mod_cast h
    have hdec : ‖fourierCoeff f k‖ ≤ K * |(k : ℝ)| ^ g := hdecay k hk
    simp only [hk0, ↓reduceIte]
    rw [Real.norm_of_nonneg (by positivity)]
    exact summand_le_majorant hkR (norm_nonneg _) hdec
  have hu_nonneg : ∀ k : ℤ, 0 ≤ (if k = 0 then (0 : ℝ) else
      |(k : ℝ)| ^ (2 * r) * ‖fourierCoeff f k‖ ^ 2) := by
    intro k
    split_ifs <;> positivity
  have hconv : circleSobolevSq r ⟨f, hf⟩ = ENNReal.ofReal (∑' k : ℤ, if k = 0 then (0 : ℝ) else
      |(k : ℝ)| ^ (2 * r) * ‖fourierCoeff f k‖ ^ 2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hu_nonneg hu_summable]
    unfold circleSobolevSq
    refine tsum_congr fun k => ?_
    split_ifs <;> simp
  rw [hconv]
  exact ENNReal.ofReal_lt_top

end Riesz1
