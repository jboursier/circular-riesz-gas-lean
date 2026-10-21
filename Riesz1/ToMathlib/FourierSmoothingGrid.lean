/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.SingularPowerGrid
public import Riesz1.ToMathlib.MollifierRapidDecay

/-!
# Absolute frequency moments after smoothing

Uniform absolute sums, retaining the correct power of the smoothing radius,
for the derivative estimates of Lemma 5.1.
-/

public section

open MeasureTheory

namespace Riesz1

/-- Polynomial decay with the shifted-power envelope used by the mesh bound. -/
theorem mollifierFT_shifted_decay {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (N : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ,
      |mollifierFT ρ t| ≤ A * (1 + |t|) ^ (-(N : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := mollifierFT_rapidDecay hρ N
  refine ⟨2 ^ N * C, by positivity, fun t => ?_⟩
  have hp : (1 + |t|) ^ N ≤ 2 ^ N * (1 + |t| ^ N) := by
    calc _ ≤ 2 ^ (N - 1) * (1 ^ N + |t| ^ N) := add_pow_le (by norm_num) (abs_nonneg t) N
      _ ≤ _ := by
        simp only [one_pow]
        gcongr <;> norm_num
  have hm := mul_le_mul_of_nonneg_right hp (abs_nonneg (mollifierFT ρ t))
  have ht := mul_le_mul_of_nonneg_left (hb t) (by positivity : 0 ≤ (2 : ℝ) ^ N)
  have hc : (1 + |t|) ^ N * |mollifierFT ρ t| ≤ 2 ^ N * C := by nlinarith
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |t|), Real.rpow_natCast]
  exact (le_mul_inv_iff₀ (by positivity : 0 < (1 + |t|) ^ N)).mpr (by nlinarith)

namespace FourierGrid

/-- A uniform bound for the absolute differentiated Fourier sum. The exponent
`q > -1` may be negative. Both constants precede the frequency mesh and radius. -/
theorem mollifier_moment_mesh_bound {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    {q : ℝ} (hq : -1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ h : ℝ, 0 < δ → 0 < h →
      Summable (fun k : ℤ => if k = 0 then (0 : ℝ) else
        (δ * |(k : ℝ)|) ^ q * |mollifierFT ρ (h * δ * k)|) ∧
      δ * (∑' k : ℤ, if k = 0 then (0 : ℝ) else
        (δ * |(k : ℝ)|) ^ q * |mollifierFT ρ (h * δ * k)|) ≤
          C * h ^ (-q - 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (q + 1)
  obtain ⟨A, hA, hdec⟩ := mollifierFT_shifted_decay hρ N
  obtain ⟨D, hD, hmesh⟩ := power_product_mesh_bound hq
    (neg_nonpos.mpr (Nat.cast_nonneg N)) (by linarith : q + -(N : ℝ) < -1)
  refine ⟨A * D, mul_pos hA hD, fun δ h hδ hh => ?_⟩
  obtain ⟨hs, hb⟩ := hmesh (h * δ) (mul_pos hh hδ)
  let B := fun k : ℤ => if k = 0 then (0 : ℝ) else
    (h * δ * |(k : ℝ)|) ^ q * (1 + h * δ * |(k : ℝ)|) ^ (-(N : ℝ))
  let W := fun k : ℤ => if k = 0 then (0 : ℝ) else
    (δ * |(k : ℝ)|) ^ q * |mollifierFT ρ (h * δ * k)|
  have hm (k : ℤ) : W k ≤ A * h ^ (-q) * B k := by
    dsimp only [W, B]
    split_ifs with hk
    · simp only [mul_zero, le_refl]
    have hu : 0 < δ * |(k : ℝ)| := mul_pos hδ (abs_pos.mpr (by exact_mod_cast hk))
    have he : (δ * |(k : ℝ)|) ^ q = h ^ (-q) * (h * δ * |(k : ℝ)|) ^ q := by
      rw [show h * δ * |(k : ℝ)| = h * (δ * |(k : ℝ)|) by ring,
        Real.mul_rpow hh.le hu.le, ← mul_assoc, ← Real.rpow_add hh, neg_add_cancel, Real.rpow_zero,
        one_mul]
    have hd := hdec (h * δ * k)
    rw [abs_mul, abs_mul, abs_of_pos hh, abs_of_pos hδ] at hd
    calc _ ≤ (δ * |(k : ℝ)|) ^ q * (A * (1 + h * δ * |(k : ℝ)|) ^ (-(N : ℝ))) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by rw [he]; ring
  have hn (k : ℤ) : 0 ≤ W k := by dsimp only [W]; split_ifs <;> positivity
  have hws : Summable W := Summable.of_norm_bounded (hs.mul_left (A * h ^ (-q)))
    (fun k => by rw [Real.norm_of_nonneg (hn k)]; exact hm k)
  refine ⟨hws, ?_⟩
  change δ * ∑' k, W k ≤ _
  have ht := mul_le_mul_of_nonneg_left (hws.tsum_le_tsum hm (hs.mul_left _)) hδ.le
  rw [tsum_mul_left] at ht
  have he : δ * (A * h ^ (-q) * ∑' k, B k) =
      A * h ^ (-q - 1) * ((h * δ) * ∑' k, B k) := by
    rw [Real.rpow_sub hh, Real.rpow_one]
    field_simp
  rw [he] at ht
  exact ht.trans (by
    have hb' := mul_le_mul_of_nonneg_left hb
      (by positivity : 0 ≤ A * h ^ (-q - 1))
    convert hb' using 1; ring)

/-- Multiplying coefficients by the actual mollifier multiplier gives absolute
moments at their correct scale. The coefficient normalization is `L⁻¹` and
frequencies here are `k/L`. Angular derivatives multiply by `(2*pi)^m`. -/
theorem smoothed_coeff_moment_bound {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (m : ℕ) {g K : ℝ} (hq : -1 < (m : ℝ) + g) :
    ∃ C : ℝ, 0 < C ∧ ∀ L h : ℝ, 0 < L → 0 < h → ∀ c : ℤ → ℂ,
      (∀ k : ℤ, k ≠ 0 → L * ‖c k‖ ≤ K * |(k : ℝ) / L| ^ g) →
      Summable (fun k : ℤ => if k = 0 then (0 : ℝ) else
        |(k : ℝ) / L| ^ m * ‖c k * (mollifierFT ρ (h * k / L) : ℂ)‖) ∧
      (∑' k : ℤ, if k = 0 then (0 : ℝ) else
        |(k : ℝ) / L| ^ m * ‖c k * (mollifierFT ρ (h * k / L) : ℂ)‖) ≤
          C * h ^ (-(m : ℝ) - g - 1) := by
  obtain ⟨D, hD, hmesh⟩ := mollifier_moment_mesh_bound hρ hq
  refine ⟨(|K| + 1) * D, by positivity, fun L h hL hh c hc => ?_⟩
  obtain ⟨hs, hb⟩ := hmesh L⁻¹ h (inv_pos.mpr hL) hh
  let B := fun k : ℤ => if k = 0 then (0 : ℝ) else
    (L⁻¹ * |(k : ℝ)|) ^ ((m : ℝ) + g) * |mollifierFT ρ (h * L⁻¹ * k)|
  let W := fun k : ℤ => if k = 0 then (0 : ℝ) else
    |(k : ℝ) / L| ^ m * ‖c k * (mollifierFT ρ (h * k / L) : ℂ)‖
  have hn (k : ℤ) : 0 ≤ W k := by dsimp only [W]; split_ifs <;> positivity
  have hm (k : ℤ) : W k ≤ (|K| + 1) * L⁻¹ * B k := by
    dsimp only [W, B]
    split_ifs with hk
    · simp only [mul_zero, le_refl]
    have hu : 0 < |(k : ℝ) / L| := abs_pos.mpr (div_ne_zero (by exact_mod_cast hk) hL.ne')
    have hu' : |(k : ℝ) / L| = L⁻¹ * |(k : ℝ)| := by
      rw [abs_div, abs_of_pos hL, div_eq_mul_inv, mul_comm]
    have he : h * (k : ℝ) / L = h * L⁻¹ * k := by ring
    have hcc : ‖c k‖ ≤ (|K| + 1) * L⁻¹ * |(k : ℝ) / L| ^ g := by
      apply (mul_le_mul_iff_right₀ hL).mp
      have hh := (hc k hk).trans (mul_le_mul_of_nonneg_right
        (show K ≤ |K| + 1 by linarith [le_abs_self K]) (by positivity))
      convert hh using 1; field_simp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc _ ≤ |(k : ℝ) / L| ^ m *
        (((|K| + 1) * L⁻¹ * |(k : ℝ) / L| ^ g) * |mollifierFT ρ (h * k / L)|) := by
          gcongr
      _ = _ := by
        rw [← Real.rpow_natCast, hu', Real.rpow_add (hu' ▸ hu), he]
        ring
  have hws : Summable W := Summable.of_norm_bounded (hs.mul_left ((|K| + 1) * L⁻¹))
    (fun k => by rw [Real.norm_of_nonneg (hn k)]; exact hm k)
  refine ⟨hws, ?_⟩
  have ht := hws.tsum_le_tsum hm (hs.mul_left _)
  rw [tsum_mul_left, mul_assoc] at ht
  have hb' := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ |K| + 1)
  have he : -((m : ℝ) + g) - 1 = -(m : ℝ) - g - 1 := by ring
  rw [he] at hb'
  exact ht.trans (by simpa only [mul_assoc, B] using hb')

end FourierGrid
end Riesz1
