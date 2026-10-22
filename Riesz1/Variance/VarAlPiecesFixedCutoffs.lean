/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlPiecesEnvelopeCompact
public import Riesz1.Auxiliary.GradientSplittingZWeights

/-!
# Fixed cutoffs with a regular remainder

One radius, chosen from the separation of the marks, defines the
periodic cutoffs on every observation circle. The remainder has bounded
derivatives near the origin and the same tails as the transport.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1.Internal

/-- Increasing the singularity exponent increases the first derivative weight. -/
theorem fixedCutoff_weightOne_mono {s b c K L x : ℝ}
    (hK : 1 ≤ K) (hbc : b ≤ c) :
    gradWeightOne s b K L x ≤ gradWeightOne s c K L x := by
  unfold gradWeightOne
  split_ifs with hx
  · exact Real.rpow_le_rpow_of_exponent_ge
      (lt_max_of_lt_right (inv_pos.mpr (by linarith : 0 < K)))
      (max_le hx.le (inv_le_one_of_one_le₀ hK)) (by linarith)
  · exact le_rfl

/-- Increasing the singularity exponent increases the second derivative weight. -/
theorem fixedCutoff_weightTwo_mono {s b c K L x : ℝ}
    (hK : 1 ≤ K) (hbc : b ≤ c) :
    gradWeightTwo s b K L x ≤ gradWeightTwo s c K L x := by
  unfold gradWeightTwo
  split_ifs with hx
  · exact Real.rpow_le_rpow_of_exponent_ge
      (lt_max_of_lt_right (inv_pos.mpr (by linarith : 0 < K)))
      (max_le hx.le (inv_le_one_of_one_le₀ hK)) (by linarith)
  · exact le_rfl

/-- Fixed cutoffs give a single-center bound for each singular piece.
The last piece is the regular remainder and has singularity exponent zero.
The radius and the coefficient precede the period, both scales and the function. -/
theorem varAlPieces_fixed_cutoffs (n : ℕ) (a : Fin n → ℝ)
    {s b S A δ : ℝ} (hs : s < 1) (hb : 0 < b)
    (hS : 0 ≤ S) (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L K h : ℝ), 1 ≤ L →
      (∀ i k, i ≠ k → δ ≤ circDist L (a i - a k)) →
      1 ≤ K → K⁻¹ ≤ h → ∀ F : ℝ → ℝ,
      ContDiff ℝ ∞ F → Function.Periodic F L → (∀ x, |F x| ≤ S) →
      (∀ x, |deriv F x| ≤ A * (1 + ∑ k, max (circDist L (x - a k)) h ^ (-b))) →
      (∀ x, |deriv (deriv F) x| ≤ A * (1 + ∑ k,
        max (circDist L (x - a k)) h ^ (-1 - b))) →
      (∀ x, 4 ≤ circDist L x → |deriv F x| ≤ A * circDist L x ^ (s - 2) ∧
        |deriv (deriv F) x| ≤ A * circDist L x ^ (s - 3)) →
      ∃ φ : Fin (n + 1) → ℝ → ℝ,
        (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) L) ∧
        (∀ x, F x = ∑ j, φ j x) ∧
        (∀ j x,
          |deriv (φ j) x| ≤ C * gradWeightOne s
            (Fin.lastCases 0 (fun _ : Fin n => b) j) K L (x - Fin.lastCases 0 a j) ∧
          |deriv (deriv (φ j)) x| ≤ C * gradWeightTwo s
            (Fin.lastCases 0 (fun _ : Fin n => b) j) K L (x - Fin.lastCases 0 a j)) := by
  classical
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = min (δ / 6) (1 / 16) := ⟨_, rfl⟩
  have hr : 0 < r := by
    rw [hr_def]
    exact lt_min (by linarith) (by norm_num)
  have hr16 : r ≤ 1 / 16 := by
    rw [hr_def]
    exact min_le_right _ _
  have hδr : 6 * r ≤ δ := by
    have h1 := min_le_left (δ / 6) (1 / 16)
    rw [← hr_def] at h1
    linarith
  have hζ0 : ∀ s, 2 * r ≤ |s| → cutoffBump r s = 0 := fun s hs => cutoffBump_eq_zero hr hs
  obtain ⟨M1, M2, hM1, hM2⟩ := exists_bounds_deriv_bump (contDiff_cutoffBump r) hζ0
  have hM1nn : 0 ≤ M1 := (abs_nonneg _).trans (hM1 0)
  have hM2nn : 0 ≤ M2 := (abs_nonneg _).trans (hM2 0)
  -- The radius beyond which the tails apply.
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 4 + ∑ j, |a j| := ⟨_, rfl⟩
  have hR2 : 2 ≤ R := by
    have : 0 ≤ ∑ j, |a j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    linarith
  have hRa : ∀ i, |a i| ≤ R - 2 := by
    intro i
    have h1 : |a i| ≤ ∑ j, |a j| :=
      Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)
    linarith
  -- The constant of the envelopes, independent of `N`, `h` and the transport.
  obtain ⟨R1, hR1⟩ : ∃ R1 : ℝ, R1 = (n : ℝ) * M1 * S +
      (1 + (n : ℝ)) * (A * (1 + (n : ℝ) *
        r ^ (-b))) := ⟨_, rfl⟩
  obtain ⟨R2, hR2def⟩ : ∃ R2 : ℝ, R2 = (n : ℝ) * M2 * S +
      2 * ((n : ℝ) * M1) * (A * (1 + (n : ℝ) *
        r ^ (-b))) +
      (1 + (n : ℝ)) * (A * (1 + (n : ℝ) *
        r ^ (-1 - b))) := ⟨_, rfl⟩
  have hvc := varAlConst_bounds (p := n) hM1nn hM2nn hS hA hr b
  obtain ⟨Kc, hKc⟩ : ∃ K : ℝ, K = varAlConst M1 M2 S (A) r n
      b + A + |R1| * R ^ (2 - s) + |R2| * R ^ (3 - s) :=
    ⟨_, rfl⟩
  have hR1le : R1 ≤ varAlConst M1 M2 S (A) r n b := by
    have := hvc.2.2.1
    rw [hR1]
    exact this
  have hR2le : R2 ≤ varAlConst M1 M2 S (A) r n b := by
    have := hvc.2.2.2.1
    rw [hR2def]
    exact this
  have hRpow1 : 0 ≤ R ^ (2 - s) := Real.rpow_nonneg (by linarith) _
  have hRpow2 : 0 ≤ R ^ (3 - s) := Real.rpow_nonneg (by linarith) _
  have hvc1 : 1 ≤ varAlConst M1 M2 S (A) r n b := hvc.2.2.2.2
  have hK0 : 0 ≤ Kc := by
    rw [hKc]
    have := mul_nonneg (abs_nonneg R1) hRpow1
    have := mul_nonneg (abs_nonneg R2) hRpow2
    linarith
  have hKgeV : varAlConst M1 M2 S (A) r n b ≤ Kc := by
    rw [hKc]
    have := mul_nonneg (abs_nonneg R1) hRpow1
    have := mul_nonneg (abs_nonneg R2) hRpow2
    linarith
  have hKgeT : A ≤ Kc := by
    rw [hKc]
    have := mul_nonneg (abs_nonneg R1) hRpow1
    have := mul_nonneg (abs_nonneg R2) hRpow2
    have := hvc1
    linarith
  have hK1a : R1 * R ^ (2 - s) ≤ Kc := by
    rw [hKc]
    have h1 : R1 * R ^ (2 - s) ≤ |R1| * R ^ (2 - s) :=
      mul_le_mul_of_nonneg_right (le_abs_self R1) hRpow1
    have := mul_nonneg (abs_nonneg R2) hRpow2
    linarith [hvc.1, hvc1]
  have hK1b : R2 * R ^ (3 - s) ≤ Kc := by
    rw [hKc]
    have h1 : R2 * R ^ (3 - s) ≤ |R2| * R ^ (3 - s) :=
      mul_le_mul_of_nonneg_right (le_abs_self R2) hRpow2
    have := mul_nonneg (abs_nonneg R1) hRpow1
    linarith
  have hK2a : R1 ≤ Kc := le_trans hR1le hKgeV
  have hK2b : R2 ≤ Kc := le_trans hR2le hKgeV
  have hKcpos : 0 < Kc := lt_of_lt_of_le one_pos (le_trans hvc1 hKgeV)
  refine ⟨Kc, hKcpos, ?_⟩
  intro L K h hL hsep hK hh F hFC hFP hFS hD1 hD2 ht
  have hLpos : 0 < L := by linarith
  obtain ⟨hpc, hsum, hsing, hrem⟩ := pieces_envelope_general hL hr hr16 hδr hM1 hM2 a
    hsep hFC hFP hFS hA hb hK hh hD1 hD2
  have hR4 : 4 ≤ R := by
    rw [hRdef]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hfar (y : ℝ) (hy : R ≤ circDist L y) (i : Fin n) :
      2 * r < circDist L (y - a i) := by
    have h1 := circDist_add_le hLpos (y - a i) (a i)
    rw [sub_add_cancel] at h1
    have h2 := circDist_le_abs' hLpos (a i)
    linarith [hRa i]
  refine ⟨varAlPiece (cutoffBump r) L a F, hpc, hsum, fun j => ?_⟩
  refine Fin.lastCases ?_ (fun i => ?_) j
  · intro x
    simp only [Fin.lastCases_last, sub_zero]
    constructor
    · unfold gradWeightOne
      rw [neg_zero, Real.rpow_zero]
      exact weighted_remainder_bound (k := 2) (s := s) (A0 := R1) (Ct := A) (R := R)
        (K := Kc) (circDist_nonneg _ _) hR2 (by linarith) (fun _ => le_rfl)
        (by rw [hR1]; exact (hrem x).1)
        (fun hRd => by
          rw [(remainder_eq_near hLpos hζ0 a F (hfar x hRd)).1]
          exact (ht x (hR4.trans hRd)).1)
        hK1a hK2a hKgeT hK0
    · unfold gradWeightTwo
      rw [add_zero]
      exact weighted_remainder_bound (k := 3) (s := s) (A0 := R2) (Ct := A) (R := R)
        (K := Kc) (circDist_nonneg _ _) hR2 (by linarith)
        (fun hx => one_le_weight_of_lt hx hK (by norm_num))
        (by rw [hR2def]; exact (hrem x).2)
        (fun hRd => by
          rw [(remainder_eq_near hLpos hζ0 a F (hfar x hRd)).2]
          exact (ht x (hR4.trans hRd)).2)
        hK1b hK2b hKgeT hK0
  · intro x
    simp only [Fin.lastCases_castSucc]
    have ht' := hsing i (x - a i)
    rw [sub_add_cancel] at ht'
    constructor
    · unfold gradWeightOne
      split_ifs at ht' ⊢ with hd
      · exact ht'.1.trans (mul_le_mul_of_nonneg_right hKgeV (by positivity))
      · simp only [mul_zero] at ht'
        exact ht'.1.trans (mul_nonneg hK0 (Real.rpow_nonneg (circDist_nonneg _ _) _))
    · unfold gradWeightTwo
      rw [show -(1 + b) = -1 - b by ring]
      split_ifs at ht' ⊢ with hd
      · exact ht'.2.trans (mul_le_mul_of_nonneg_right hKgeV (by positivity))
      · simp only [mul_zero] at ht'
        exact ht'.2.trans (mul_nonneg hK0 (Real.rpow_nonneg (circDist_nonneg _ _) _))

/-- The same cutoffs satisfy the common singularity exponent for all pieces. -/
theorem varAlPieces_fixed_uniform (n : ℕ) (a : Fin n → ℝ)
    {s b S A δ : ℝ} (hs : s < 1) (hb : 0 < b)
    (hS : 0 ≤ S) (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L K h : ℝ), 1 ≤ L →
      (∀ i k, i ≠ k → δ ≤ circDist L (a i - a k)) →
      1 ≤ K → K⁻¹ ≤ h → ∀ F : ℝ → ℝ,
      ContDiff ℝ ∞ F → Function.Periodic F L → (∀ x, |F x| ≤ S) →
      (∀ x, |deriv F x| ≤ A * (1 + ∑ k, max (circDist L (x - a k)) h ^ (-b))) →
      (∀ x, |deriv (deriv F) x| ≤ A * (1 + ∑ k,
        max (circDist L (x - a k)) h ^ (-1 - b))) →
      (∀ x, 4 ≤ circDist L x → |deriv F x| ≤ A * circDist L x ^ (s - 2) ∧
        |deriv (deriv F) x| ≤ A * circDist L x ^ (s - 3)) →
      ∃ φ : Fin (n + 1) → ℝ → ℝ,
        (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) L) ∧
        (∀ x, F x = ∑ j, φ j x) ∧
        (∀ j x,
          |deriv (φ j) x| ≤ C * gradWeightOne s
            b K L (x - Fin.lastCases 0 a j) ∧
          |deriv (deriv (φ j)) x| ≤ C * gradWeightTwo s
            b K L (x - Fin.lastCases 0 a j)) := by
  obtain ⟨C, hC, hsplit⟩ := varAlPieces_fixed_cutoffs n a hs hb hS hA hδ
  refine ⟨C, hC, fun L K h hL hsep hK hh F hF hp hsup h1 h2 ht => ?_⟩
  obtain ⟨φ, hφ, hsum, hd⟩ := hsplit L K h hL hsep hK hh F hF hp hsup h1 h2 ht
  refine ⟨φ, hφ, hsum, fun j x => ?_⟩
  have hle : Fin.lastCases 0 (fun _ : Fin n => b) j ≤ b := by
    refine Fin.lastCases ?_ (fun _ => ?_) j
    · simpa only [Fin.lastCases_last] using hb.le
    · simp only [Fin.lastCases_castSucc]
      exact le_rfl
  exact ⟨(hd j x).1.trans (mul_le_mul_of_nonneg_left
      (fixedCutoff_weightOne_mono hK hle) hC.le),
    (hd j x).2.trans (mul_le_mul_of_nonneg_left
      (fixedCutoff_weightTwo_mono hK hle) hC.le)⟩

end Riesz1.Internal
