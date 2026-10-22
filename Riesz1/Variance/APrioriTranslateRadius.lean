/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriConclusion

/-!
# Changing the envelope radius

The derivative envelope of the a priori lemma has radius two. The envelope of another radius
is reduced to it in three ways. A radius at most two is dominated by the radius-two envelope at
the same scale, with a constant depending on the radius. A radius `2a` is reduced to radius two
by the dilation `d ↦ a d`, which replaces the scale `K` by `aK`. The macroscopic case reduces the
dilation to scale one, by the dilation `x ↦ x / ℓ` onto the unit circle.
-/

@[expose] public section

noncomputable section

namespace Riesz1.Internal

/-- A radius `R` in `(0, 2]` gives an envelope dominated by the radius-two envelope at every
scale `K ≥ 1` and every distance `d ≥ 0`, with the factor `1 + 2^{1+λ} R^{s-3}`. -/
theorem aPrioriEnvelope_le_two_of_le {s lam R K d : ℝ} (hs : s < 3) (hlam : 0 ≤ lam)
    (hR : 0 < R) (hR2 : R ≤ 2) (hK : 1 ≤ K) (hd : 0 ≤ d) :
    aPrioriEnvelope s lam K R d ≤
      (1 + 2 ^ (1 + lam) * R ^ (s - 3)) * aPrioriEnvelope s lam K 2 d := by
  have hm : 0 < max d K⁻¹ := lt_of_lt_of_le (inv_pos.2 (by linarith)) (le_max_right _ _)
  have hm1 : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
  have hc0 : 0 ≤ 2 ^ (1 + lam) * R ^ (s - 3) :=
    mul_nonneg (Real.rpow_nonneg zero_le_two _) (Real.rpow_nonneg hR.le _)
  have hn0 : 0 ≤ ((max d K⁻¹) ^ (1 + lam))⁻¹ := inv_nonneg.2 (Real.rpow_nonneg hm.le _)
  have hf0 : 0 ≤ (d ^ (3 - s))⁻¹ := inv_nonneg.2 (Real.rpow_nonneg hd _)
  unfold aPrioriEnvelope
  rcases le_total d 2 with hd2 | hd2
  · -- Below distance two the radius-two envelope has its near term, which is at least
    -- `(2^{1+λ})⁻¹`. The far value at distance at least `R` is at most `R^{s-3}`.
    have hn2 : (2 ^ (1 + lam))⁻¹ ≤ ((max d K⁻¹) ^ (1 + lam))⁻¹ :=
      inv_anti₀ (Real.rpow_pos_of_pos hm _)
        (Real.rpow_le_rpow hm.le (max_le hd2 (by linarith)) (by linarith))
    have hsec0 : 0 ≤ (if 2 ≤ d then (d ^ (3 - s))⁻¹ else 0) := by
      by_cases h : 2 ≤ d
      · rw [ite_eq_left h]; exact hf0
      · rw [ite_eq_right h]
    rw [ite_eq_left hd2]
    set n := ((max d K⁻¹) ^ (1 + lam))⁻¹ with hn
    set c := 2 ^ (1 + lam) * R ^ (s - 3) with hc
    set sec := (if 2 ≤ d then (d ^ (3 - s))⁻¹ else 0) with hsec
    by_cases hRd : R ≤ d
    · rw [ite_eq_left hRd]
      have hfR : (d ^ (3 - s))⁻¹ ≤ R ^ (s - 3) := by
        have hRpos : 0 < R ^ (3 - s) := Real.rpow_pos_of_pos hR _
        have hle : R ^ (3 - s) ≤ d ^ (3 - s) := Real.rpow_le_rpow hR.le hRd (by linarith)
        calc (d ^ (3 - s))⁻¹ ≤ (R ^ (3 - s))⁻¹ := inv_anti₀ hRpos hle
          _ = R ^ (s - 3) := by rw [← Real.rpow_neg hR.le]; congr 1; ring
      have hRc : R ^ (s - 3) = (2 ^ (1 + lam))⁻¹ * c := by
        rw [hc, ← mul_assoc, inv_mul_cancel₀ (Real.rpow_pos_of_pos zero_lt_two _).ne', one_mul]
      have hfn : (d ^ (3 - s))⁻¹ ≤ c * n := by
        have h1 : (2 ^ (1 + lam))⁻¹ * c ≤ n * c := mul_le_mul_of_nonneg_right hn2 hc0
        nlinarith
      by_cases hdR : d ≤ R
      · rw [ite_eq_left hdR]
        nlinarith [mul_nonneg hc0 hsec0]
      · rw [ite_eq_right hdR]
        nlinarith [mul_nonneg hc0 hsec0]
    · rw [ite_eq_right hRd]
      by_cases hdR : d ≤ R
      · rw [ite_eq_left hdR]
        nlinarith [mul_nonneg hc0 hsec0, mul_nonneg hc0 hn0]
      · rw [ite_eq_right hdR]
        nlinarith [mul_nonneg hc0 hsec0, mul_nonneg hc0 hn0]
  · -- Above distance two both envelopes have only the far term, and the near term of
    -- the radius-`R` envelope at distance `d ≤ R` is dominated by the near term of radius two.
    have hRd : R ≤ d := hR2.trans hd2
    rw [ite_eq_left hRd, ite_eq_left hd2]
    have hnd0 : 0 ≤ (if d ≤ 2 then ((max d K⁻¹) ^ (1 + lam))⁻¹ else 0) := by
      by_cases h : d ≤ 2
      · rw [ite_eq_left h]; exact hn0
      · rw [ite_eq_right h]
    by_cases hdR : d ≤ R
    · rw [ite_eq_left hdR, ite_eq_left (hdR.trans hR2)]
      nlinarith [mul_nonneg hc0 (add_nonneg hn0 hf0)]
    · rw [ite_eq_right hdR]
      nlinarith [mul_nonneg hc0 (add_nonneg hnd0 hf0)]

/-- Dilation by `a > 0`: the envelope of radius `2a` at scale `K`, evaluated at `a d` and multiplied
by `a`, is at most `a^{-λ} + a^{s-2}` times the radius-two envelope at scale `aK`, evaluated at `d`. -/
theorem aPrioriEnvelope_dilate {s lam a K d : ℝ} (ha : 0 < a) (hK : 0 < K) :
    a * aPrioriEnvelope s lam K (2 * a) (a * d) ≤
      (a ^ (-lam) + a ^ (s - 2)) * aPrioriEnvelope s lam (a * K) 2 d := by
  have hm : 0 < max d (a * K)⁻¹ := lt_of_lt_of_le (inv_pos.2 (mul_pos ha hK)) (le_max_right _ _)
  have hmax : max (a * d) K⁻¹ = a * max d (a * K)⁻¹ := by
    rw [mul_max_of_nonneg _ _ ha.le, mul_inv, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  have hc1 : a * d ≤ 2 * a ↔ d ≤ 2 := by
    constructor <;> intro h <;> nlinarith
  have hc2 : 2 * a ≤ a * d ↔ 2 ≤ d := by
    constructor <;> intro h <;> nlinarith
  have key1 : ∀ m : ℝ, 0 < m → a * ((a * m) ^ (1 + lam))⁻¹ = a ^ (-lam) * (m ^ (1 + lam))⁻¹ := by
    intro m hm'
    rw [Real.mul_rpow ha.le hm'.le, Real.rpow_add ha, Real.rpow_one, Real.rpow_neg ha.le]
    have h1 : a ^ lam ≠ 0 := (Real.rpow_pos_of_pos ha lam).ne'
    have h2 : m ^ (1 + lam) ≠ 0 := (Real.rpow_pos_of_pos hm' _).ne'
    field_simp
  have key2 : ∀ d' : ℝ, 0 < d' →
      a * ((a * d') ^ (3 - s))⁻¹ = a ^ (s - 2) * (d' ^ (3 - s))⁻¹ := by
    intro d' hd'
    have hs2 : s - 2 = 1 + -(3 - s) := by ring
    rw [Real.mul_rpow ha.le hd'.le, hs2, Real.rpow_add ha, Real.rpow_one, Real.rpow_neg ha.le]
    have h1 : a ^ (3 - s) ≠ 0 := (Real.rpow_pos_of_pos ha _).ne'
    have h2 : d' ^ (3 - s) ≠ 0 := (Real.rpow_pos_of_pos hd' _).ne'
    field_simp
  unfold aPrioriEnvelope
  simp only [hc1, hc2, hmax]
  rw [mul_add]
  have eN : a * (if d ≤ 2 then ((a * max d (a * K)⁻¹) ^ (1 + lam))⁻¹ else 0) =
      a ^ (-lam) * (if d ≤ 2 then ((max d (a * K)⁻¹) ^ (1 + lam))⁻¹ else 0) := by
    by_cases h : d ≤ 2
    · rw [ite_eq_left h, ite_eq_left h]; exact key1 _ hm
    · rw [ite_eq_right h, ite_eq_right h, mul_zero, mul_zero]
  have eF : a * (if 2 ≤ d then ((a * d) ^ (3 - s))⁻¹ else 0) =
      a ^ (s - 2) * (if 2 ≤ d then (d ^ (3 - s))⁻¹ else 0) := by
    by_cases h : 2 ≤ d
    · rw [ite_eq_left h, ite_eq_left h]; exact key2 d (by linarith)
    · rw [ite_eq_right h, ite_eq_right h, mul_zero, mul_zero]
  have hX : 0 ≤ (if d ≤ 2 then ((max d (a * K)⁻¹) ^ (1 + lam))⁻¹ else 0) := by
    by_cases h : d ≤ 2
    · rw [ite_eq_left h]; exact inv_nonneg.2 (Real.rpow_nonneg hm.le _)
    · rw [ite_eq_right h]
  have hY : 0 ≤ (if 2 ≤ d then (d ^ (3 - s))⁻¹ else 0) := by
    by_cases h : 2 ≤ d
    · rw [ite_eq_left h]; exact inv_nonneg.2 (Real.rpow_nonneg (by linarith) _)
    · rw [ite_eq_right h]
  have hpa : 0 ≤ a ^ (-lam) := Real.rpow_nonneg ha.le _
  have hpb : 0 ≤ a ^ (s - 2) := Real.rpow_nonneg ha.le _
  rw [eN, eF]
  nlinarith [mul_nonneg hpa hY, mul_nonneg hpb hX]

/-- Macroscopic reduction: for `0 < ℓ ≤ 1` and a distance `d ≤ 2` with `d < ℓR`, the envelope of
radius `R` at scale `Nℓ`, evaluated at `d/ℓ` and multiplied by `1/ℓ`, is at most the radius-two
envelope at scale `N`, evaluated at `d`. The near term alone contributes, with the factor `ℓ^λ ≤ 1`. -/
theorem aPrioriEnvelope_unit {s lam ℓ R N d : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hlam : 0 ≤ lam)
    (hN : 0 < N) (hd2 : d ≤ 2) (hdR : d < ℓ * R) :
    ℓ⁻¹ * aPrioriEnvelope s lam (N * ℓ) R (ℓ⁻¹ * d) ≤ aPrioriEnvelope s lam N 2 d := by
  have hR' : ℓ⁻¹ * d < R := by
    rw [inv_mul_lt_iff₀ hℓ]; exact hdR
  have hm : 0 < max d N⁻¹ := lt_of_lt_of_le (inv_pos.2 hN) (le_max_right _ _)
  have hmax : max (ℓ⁻¹ * d) (N * ℓ)⁻¹ = ℓ⁻¹ * max d N⁻¹ := by
    rw [mul_max_of_nonneg _ _ (inv_nonneg.2 hℓ.le), mul_inv_rev]
  have hcalc : ℓ⁻¹ * ((ℓ⁻¹ * max d N⁻¹) ^ (1 + lam))⁻¹ =
      ℓ ^ lam * ((max d N⁻¹) ^ (1 + lam))⁻¹ := by
    rw [Real.mul_rpow (inv_nonneg.2 hℓ.le) hm.le, Real.inv_rpow hℓ.le, Real.rpow_add hℓ,
      Real.rpow_one]
    have h1 : ℓ ^ lam ≠ 0 := (Real.rpow_pos_of_pos hℓ lam).ne'
    have h2 : (max d N⁻¹) ^ (1 + lam) ≠ 0 := (Real.rpow_pos_of_pos hm _).ne'
    field_simp
  have hpow : ℓ ^ lam ≤ 1 := Real.rpow_le_one hℓ.le hℓ1 hlam
  have hX : 0 ≤ ((max d N⁻¹) ^ (1 + lam))⁻¹ := inv_nonneg.2 (Real.rpow_nonneg hm.le _)
  have hsec : 0 ≤ (if 2 ≤ d then (d ^ (3 - s))⁻¹ else 0) := by
    by_cases h : 2 ≤ d
    · rw [ite_eq_left h]; exact inv_nonneg.2 (Real.rpow_nonneg (by linarith) _)
    · rw [ite_eq_right h]
  unfold aPrioriEnvelope
  rw [ite_eq_left hR'.le, ite_eq_right (not_le.2 hR'), add_zero, hmax, ite_eq_left hd2, hcalc]
  nlinarith [mul_le_mul_of_nonneg_right hpow hX]

end Riesz1.Internal

end
