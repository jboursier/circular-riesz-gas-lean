/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PowerDecayGrid

/-!
# Uniform weighted Fourier sums

Low-frequency integral bounds and subcritical high-frequency power decay give
a bound independent of the circle length for a physically normalized Sobolev sum.
-/

public section

open MeasureTheory

namespace Riesz1.FourierGrid

/-- A bounded low-frequency envelope and an integrable power tail fit under a
single decreasing integrable envelope. -/
theorem power_envelope_le {u q : ℝ} (hu : 0 ≤ u) (hq : q ≤ 0) :
    (if u ≤ 1 then 1 else u ^ q) ≤ 2 ^ (-q) * (1 + u) ^ q := by
  have he : ((1 + u) / 2) ^ q = 2 ^ (-q) * (1 + u) ^ q := by
    rw [Real.div_rpow (by linarith : 0 ≤ 1 + u) (by norm_num : (0 : ℝ) ≤ 2),
      div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
  rw [← he]
  split_ifs with hu1
  · exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith) hq
  · exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) hq

/-- A physically weighted squared coefficient sum is bounded uniformly over
all positive circle lengths. No condition on an integer-frequency norm is used. -/
theorem weighted_coeff_mesh_bound {a g Z K : ℝ} (ha : 0 ≤ a)
    (hg : a + 2 * g < -1) :
    ∃ D : ℝ, 0 < D ∧ ∀ L : ℝ, 0 < L → ∀ c : ℤ → ℂ,
      (∀ k, L * ‖c k‖ ≤ Z) →
      (∀ k : ℤ, 1 ≤ |2 * Real.pi * (k : ℝ) / L| →
        L * ‖c k‖ ≤ K * |2 * Real.pi * (k : ℝ) / L| ^ g) →
      Summable (fun k : ℤ => if k = 0 then (0 : ℝ) else
        |2 * Real.pi * (k : ℝ) / L| ^ a * ‖c k‖ ^ 2) ∧
      L * (∑' k : ℤ, if k = 0 then (0 : ℝ) else
        |2 * Real.pi * (k : ℝ) / L| ^ a * ‖c k‖ ^ 2) ≤ D := by
  let q := a + 2 * g
  obtain ⟨C, hC, hmesh⟩ := power_decay_mesh_bound hg
  let B := (Z ^ 2 + K ^ 2) * 2 ^ (-q)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let D := B / (2 * Real.pi) * C + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, fun L hL c hlo hhi => ?_⟩
  let δ := 2 * Real.pi / L
  have hδ : 0 < δ := div_pos (by positivity) hL
  let A := fun k : ℤ => if k = 0 then (0 : ℝ) else (1 + δ * |(k : ℝ)|) ^ q
  let w := fun k : ℤ => if k = 0 then (0 : ℝ) else
    |2 * Real.pi * (k : ℝ) / L| ^ a * ‖c k‖ ^ 2
  obtain ⟨hAs, hAb⟩ := hmesh δ hδ
  have hw0 (k : ℤ) : 0 ≤ w k := by dsimp [w]; split_ifs <;> positivity
  have hbound (k : ℤ) : w k ≤ (B / L ^ 2) * A k := by
    by_cases hk : k = 0
    · simp only [w, A, hk, ite_true, mul_zero, le_refl]
    let u := |2 * Real.pi * (k : ℝ) / L|
    have hu : 0 < u := by
      dsimp [u]
      exact abs_pos.mpr (div_ne_zero (mul_ne_zero (by positivity) (by exact_mod_cast hk)) hL.ne')
    have huδ : u = δ * |(k : ℝ)| := by
      dsimp [u, δ]
      rw [abs_div, abs_mul, abs_of_pos hL, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      ring
    have hterm : u ^ a * (L * ‖c k‖) ^ 2 ≤
        (Z ^ 2 + K ^ 2) * (if u ≤ 1 then 1 else u ^ q) := by
      split_ifs with hu1
      · have hua : u ^ a ≤ 1 := Real.rpow_le_one hu.le hu1 ha
        have hs := pow_le_pow_left₀ (mul_nonneg hL.le (norm_nonneg _)) (hlo k) 2
        nlinarith [mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hu.le a), sq_nonneg K]
      · have hs := pow_le_pow_left₀ (mul_nonneg hL.le (norm_nonneg _))
          (hhi k (le_of_not_ge hu1)) 2
        have he : u ^ a * (K * u ^ g) ^ 2 = K ^ 2 * u ^ q := by
          rw [mul_pow, show (u ^ g) ^ 2 = u ^ (2 * g) by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]; congr 1; push_cast; ring]
          rw [show u ^ a * (K ^ 2 * u ^ (2 * g)) =
            K ^ 2 * (u ^ a * u ^ (2 * g)) by ring, ← Real.rpow_add hu]
        exact (mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hu.le a)).trans
          (he ▸ mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg Z]) (Real.rpow_nonneg hu.le q))
    have hm := hterm.trans (mul_le_mul_of_nonneg_left (power_envelope_le hu.le (by dsimp [q]; linarith))
      (by positivity : 0 ≤ Z ^ 2 + K ^ 2))
    have hw : L ^ 2 * w k ≤ B * A k := by
      simp only [w, A, hk, ite_false]
      rw [← huδ]
      dsimp only [B]
      nlinarith [hm]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (sq_pos_of_pos hL)).mpr (by simpa only [mul_comm] using hw)
  have hws : Summable w := Summable.of_norm_bounded (hAs.mul_left (B / L ^ 2))
    (fun k => by rw [Real.norm_of_nonneg (hw0 k)]; exact hbound k)
  refine ⟨hws, ?_⟩
  have hs := mul_le_mul_of_nonneg_left
    (hws.tsum_le_tsum hbound (hAs.mul_left (B / L ^ 2))) hL.le
  rw [tsum_mul_left] at hs
  have he : L * (B / L ^ 2 * ∑' k, A k) =
      (B / (2 * Real.pi)) * (δ * ∑' k, A k) := by dsimp [δ]; field_simp
  rw [he] at hs
  have ht := mul_le_mul_of_nonneg_left hAb
    (div_nonneg hB (by positivity : 0 ≤ 2 * Real.pi))
  exact hs.trans (ht.trans (by dsimp [D]; linarith))

end Riesz1.FourierGrid
