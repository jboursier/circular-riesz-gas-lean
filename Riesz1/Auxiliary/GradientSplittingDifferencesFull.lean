/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingCrossing

/-!
# The complete weighted divided-difference bounds

Claims (iv) and (v) of the differences part of Lemma 5.7, and
their assembly with the bounds. Both finite-difference estimates hold
for arbitrary real lifts: no hull-length or lattice-avoidance hypothesis is needed.
The derivative difference retains the required nonzero denominators.
-/

public section

open scoped ContDiff

namespace Riesz1

/-- Claim (iv) for arbitrary real lifts, including coincident endpoints. -/
theorem gradZ_sub_gradZ_le {s a K ℓ C0 : ℝ} {ψ : ℝ → ℝ}
    (hℓ : 0 < ℓ) (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hK : 1 ≤ K) (hC0 : 0 ≤ C0) (hψ : ContDiff ℝ ∞ ψ) (hper : Function.Periodic ψ ℓ⁻¹)
    (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K ℓ⁻¹ t)
    (hbd2 : ∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s a K ℓ⁻¹ t)
    (x y z : ℝ) :
    |gradZ ψ ℓ x z - gradZ ψ ℓ x y| ≤ (gradZConst a s + 1) * C0 * ℓ⁻¹ * |z - y| *
      (gradWeightTwo s a K ℓ⁻¹ (x / ℓ) + gradWeightTwo s a K ℓ⁻¹ (y / ℓ) +
        gradWeightTwo s a K ℓ⁻¹ (z / ℓ)) := by
  have h := gradZavg_sub_gradZavg_le (inv_pos.mpr hℓ) hs0 hs1 ha0 ha1 hK hC0 hψ hper
    hbd hbd2 (x / ℓ) (y / ℓ) (z / ℓ)
  have heq : |z / ℓ - y / ℓ| = ℓ⁻¹ * |z - y| := by
    rw [show z / ℓ - y / ℓ = ℓ⁻¹ * (z - y) by ring, abs_mul, abs_of_pos (inv_pos.mpr hℓ)]
  rw [heq] at h
  rw [gradZ_eq_gradZavg, gradZ_eq_gradZavg]
  convert h using 1
  ring

/-- Internal algebraic bound for the difference of two first-endpoint quotients. -/
lemma gradSplit_quotient_sub_le {U V d e D : ℝ} (hd : 0 < |d|) (he : 0 < |e|)
    (hD : 0 ≤ D) (hUV : |V - U| ≤ D * |e - d|) (hU : |U / d| ≤ D) :
    |V / e - U / d| ≤ 2 * D * |e - d| / min |d| |e| := by
  have hd0 : d ≠ 0 := abs_pos.mp hd
  have he0 : e ≠ 0 := abs_pos.mp he
  have hmin : 0 < min |d| |e| := lt_min hd he
  have hid : V / e - U / d = ((V - U) - (U / d) * (e - d)) / e := by
    field_simp
    ring
  have hnum : |(V - U) - U / d * (e - d)| ≤ 2 * D * |e - d| := by
    calc
      |(V - U) - U / d * (e - d)| ≤ |V - U| + |U / d * (e - d)| := abs_sub _ _
      _ = |V - U| + |U / d| * |e - d| := by rw [abs_mul]
      _ ≤ D * |e - d| + D * |e - d| :=
        add_le_add hUV (mul_le_mul_of_nonneg_right hU (abs_nonneg _))
      _ = 2 * D * |e - d| := by ring
  rw [hid, abs_div]
  exact (div_le_div_of_nonneg_right hnum he.le).trans
    (div_le_div_of_nonneg_left (by positivity) hmin (min_le_right _ _))

/-- Claim (v) for arbitrary real lifts with both denominators nonzero. -/
theorem gradZx_sub_gradZx_le {s a K ℓ C0 : ℝ} {ψ : ℝ → ℝ}
    (hℓ : 0 < ℓ) (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hK : 1 ≤ K) (hC0 : 0 ≤ C0) (hψ : ContDiff ℝ ∞ ψ) (hper : Function.Periodic ψ ℓ⁻¹)
    (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K ℓ⁻¹ t)
    (hbd2 : ∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s a K ℓ⁻¹ t)
    {x y z : ℝ} (hy : 0 < |y - x|) (hz : 0 < |z - x|) :
    |gradZx ψ ℓ x z - gradZx ψ ℓ x y| ≤
      2 * (gradZConst a s + 1) * C0 * ℓ⁻¹ * |z - y| / min |y - x| |z - x| *
        (gradWeightTwo s a K ℓ⁻¹ (x / ℓ) + gradWeightTwo s a K ℓ⁻¹ (y / ℓ) +
          gradWeightTwo s a K ℓ⁻¹ (z / ℓ)) := by
  let S := gradWeightTwo s a K ℓ⁻¹ (x / ℓ) + gradWeightTwo s a K ℓ⁻¹ (y / ℓ) +
    gradWeightTwo s a K ℓ⁻¹ (z / ℓ)
  let D := (gradZConst a s + 1) * C0 * ℓ⁻¹ * S
  have hcoef : 0 ≤ (gradZConst a s + 1) * C0 * ℓ⁻¹ :=
    mul_nonneg (mul_nonneg (by linarith [gradZConst_nonneg ha1 hs1]) hC0) (inv_nonneg.mpr hℓ.le)
  have hS : 0 ≤ S := add_nonneg
    (add_nonneg (gradWeightTwo_nonneg hK) (gradWeightTwo_nonneg hK)) (gradWeightTwo_nonneg hK)
  have hD : 0 ≤ D := mul_nonneg hcoef hS
  have hdiff : |(gradZ ψ ℓ x z - deriv ψ (x / ℓ)) -
      (gradZ ψ ℓ x y - deriv ψ (x / ℓ))| ≤ D * |(z - x) - (y - x)| := by
    have h := gradZ_sub_gradZ_le hℓ hs0 hs1 ha0 ha1 hK hC0 hψ hper hbd hbd2 x y z
    rw [show (gradZ ψ ℓ x z - deriv ψ (x / ℓ)) -
      (gradZ ψ ℓ x y - deriv ψ (x / ℓ)) = gradZ ψ ℓ x z - gradZ ψ ℓ x y by ring,
      show (z - x) - (y - x) = z - y by ring]
    dsimp [D, S]
    convert h using 1
    ring
  have hU : |(gradZ ψ ℓ x y - deriv ψ (x / ℓ)) / (y - x)| ≤ D := by
    have h := gradZx_abs_le hℓ hs0 hs1 ha0 ha1 hK hC0 hψ hper hbd hbd2 hy
    exact h.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (gradWeightTwo_nonneg hK)) hcoef)
  have h := gradSplit_quotient_sub_le hy hz hD hdiff hU
  rw [show (z - x) - (y - x) = z - y by ring] at h
  unfold gradZx
  convert h using 1
  dsimp [D, S]
  ring

/-- All bounds of the differences part of Lemma 5.7, with one
constant depending only on `s, α`. The real-lift length restrictions are dropped.
All endpoint coincidences without a zero denominator are included. -/
theorem gradient_splitting_differences {s α : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hα0 : s - 1 ≤ α)
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
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ))) ∧
      (∀ x y z : ℝ,
        |gradZ ψ ℓ x z - gradZ ψ ℓ x y| ≤ C * C0 * ℓ⁻¹ * |z - y| *
          (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (z / ℓ))) ∧
      (∀ x y z : ℝ, 0 < |y - x| → 0 < |z - x| →
        |gradZx ψ ℓ x z - gradZx ψ ℓ x y| ≤
          C * C0 * ℓ⁻¹ * |z - y| / min |y - x| |z - x| *
            (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
              gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ) +
              gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (z / ℓ))) := by
  obtain ⟨C, hC, hbase⟩ := gradSplit_differences_bounds hs0 hs1 hα0 hα1
  have ha0 : 0 ≤ 1 - s + α := by linarith
  have ha1 : 1 - s + α < 1 := by linarith
  let A := gradZConst (1 - s + α) s + 1
  have hA : 0 ≤ A := by dsimp [A]; linarith [gradZConst_nonneg ha1 hs1]
  have hCb : C ≤ max C (2 * A) := le_max_left _ _
  have hCv : 2 * A ≤ max C (2 * A) := le_max_right _ _
  have hCiv : A ≤ max C (2 * A) := le_trans (by linarith) hCv
  refine ⟨max C (2 * A), lt_of_lt_of_le hC hCb, ?_⟩
  intro N ℓ C0 ψ hN hℓ hℓ1 hK hC0 hψ hper hbd hbd2
  obtain ⟨hanti, hZ, hZxy, hZxy2⟩ := hbase N ℓ C0 ψ hN hℓ hℓ1 hK hC0 hψ hper hbd hbd2
  have hL : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr hℓ.le
  have hw1 (t : ℝ) : 0 ≤ gradWeightOne s (1 - s + α) (N * ℓ) ℓ⁻¹ t :=
    gradWeightOne_nonneg hK
  have hw2 (t : ℝ) : 0 ≤ gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ t :=
    gradWeightTwo_nonneg hK
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    refine (hanti u hu).trans ?_
    gcongr
  · intro x y
    have hW := add_nonneg (hw1 (x / ℓ)) (hw1 (y / ℓ))
    refine (hZ x y).trans ?_
    gcongr
  · intro x y hd
    have hW := add_nonneg (hw2 (x / ℓ)) (hw2 (y / ℓ))
    refine (hZxy x y hd).trans ?_
    gcongr
  · intro x y hd
    have hW := add_nonneg (hw2 (x / ℓ)) (hw2 (y / ℓ))
    refine (hZxy2 x y hd).trans ?_
    gcongr
  · intro x y z
    have hW := add_nonneg (add_nonneg (hw2 (x / ℓ)) (hw2 (y / ℓ))) (hw2 (z / ℓ))
    have h := gradZ_sub_gradZ_le hℓ hs0 hs1 ha0 ha1 hK hC0 hψ hper hbd hbd2 x y z
    change _ ≤ A * C0 * ℓ⁻¹ * |z - y| * _ at h
    refine h.trans ?_
    gcongr
  · intro x y z hy hz
    have hW := add_nonneg (add_nonneg (hw2 (x / ℓ)) (hw2 (y / ℓ))) (hw2 (z / ℓ))
    have h := gradZx_sub_gradZx_le hℓ hs0 hs1 ha0 ha1 hK hC0 hψ hper hbd hbd2 hy hz
    change _ ≤ 2 * A * C0 * ℓ⁻¹ * |z - y| / min |y - x| |z - x| * _ at h
    refine h.trans ?_
    gcongr

end Riesz1

end
