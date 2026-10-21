/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.RigidityConclusion
public import Riesz1.Rigidity.BlockMoments
public import Riesz1.ToMathlib.LogConcave.GapIBP
public import Riesz1.ToMathlib.FourthMomentTail

/-!
# A centered block second moment for the averaged energy

The probabilistic input to the random-sum part of Lemma B.1. A fourth moment
and the rigidity tail give a second moment of order `k^(3s/2)`. The exponent
is deliberately weaker than the near-optimal one and still makes the later
kernel comparison summable.
-/

public section

noncomputable section

open MeasureTheory

namespace Riesz1

/-- A scalar fourth-power estimate. -/
lemma bell_sub_fourth_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x - y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  have hab : |x - y| ≤ x + y := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have h1 := pow_le_pow_left₀ (abs_nonneg _) hab 4
  have h2 := add_pow_le hx hy 4
  rw [show |x - y| ^ 4 = (x - y) ^ 4 from pow_abs_two_mul (x - y) (n := 2)] at h1
  norm_num at h2
  exact h1.trans h2

/-- A uniform fourth moment of a centered block. No rigidity is needed. -/
theorem bell_centered_fourth_moment :
    ∃ D4 : ℝ, 0 < D4 ∧ ∀ (_hPL : External.PrekopaLeindler) (P : Parameters)
      (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (j : ℤ) (k : ℕ), 1 ≤ k →
      Integrable (fun X : Configuration N => (blockLength X j k - k) ^ 4) (gibbsMeasure P N) ∧
      (∫ X : Configuration N, (blockLength X j k - k) ^ 4 ∂gibbsMeasure P N) ≤
        D4 * (k : ℝ) ^ 4 := by
  obtain ⟨C4, hC4, hmom⟩ := blockLength_moments 4 (by norm_num)
  let D4 := 8 * (C4 + 1)
  refine ⟨D4, by dsimp [D4]; positivity, ?_⟩
  intro hPL P N hN j k hk
  have := (modelWellDefined P N).2.2
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hZ : Measurable (fun X : Configuration N => blockLength X j k - k) :=
    (measurable_blockLength _ _).sub_const _
  obtain ⟨hi4, hb4⟩ := hmom hPL P N hN j k hk
  norm_num [Real.rpow_natCast] at hi4 hb4
  have hb4r : (∫ X : Configuration N, blockLength X j k ^ 4 ∂gibbsMeasure P N) ≤
      C4 * (k : ℝ) ^ 4 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi4 (ae_of_all _ fun X => pow_nonneg (blockLength_pos X j hk).le 4)] at hb4
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb4
  have hpt (X : Configuration N) : (blockLength X j k - k) ^ 4 ≤
      8 * (blockLength X j k ^ 4 + (k : ℝ) ^ 4) :=
    bell_sub_fourth_le (blockLength_pos X j hk).le hk0.le
  have hiB : Integrable (fun X : Configuration N =>
      8 * (blockLength X j k ^ 4 + (k : ℝ) ^ 4)) (gibbsMeasure P N) :=
    (hi4.add (integrable_const ((k : ℝ) ^ 4))).const_mul 8
  have hiZ4 : Integrable (fun X : Configuration N => (blockLength X j k - k) ^ 4)
      (gibbsMeasure P N) := by
    apply hiB.mono'
      (hZ.pow_const 4).aestronglyMeasurable
    exact ae_of_all _ fun X => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ (blockLength X j k - k) ^ 4), Pi.add_apply] using hpt X
  have hfour : (∫ X : Configuration N, (blockLength X j k - k) ^ 4
      ∂gibbsMeasure P N) ≤ D4 * (k : ℝ) ^ 4 := by
    calc _ ≤ ∫ X : Configuration N, 8 *
          (blockLength X j k ^ 4 + (k : ℝ) ^ 4) ∂gibbsMeasure P N :=
            integral_mono hiZ4 hiB hpt
      _ = 8 * ((∫ X : Configuration N, blockLength X j k ^ 4 ∂gibbsMeasure P N) +
          (k : ℝ) ^ 4) := by rw [integral_const_mul, integral_add hi4 (integrable_const _)]; simp
      _ ≤ 8 * (C4 * (k : ℝ) ^ 4 + (k : ℝ) ^ 4) := by gcongr
      _ = _ := by dsimp [D4]; ring
  exact ⟨hiZ4, hfour⟩

namespace Internal

/-- A centered block second moment, conditional on rigidity. The same constant
works for all external inputs, particle numbers and short blocks. -/
theorem bell_block_second_moment_of_rigidity (beta s : ℝ) (hbeta : 0 < beta)
    (hs : 0 < s) (hs1 : s < 1) (hRig : RigidityConclusion beta s hbeta hs hs1) :
    ∃ D : ℝ, 0 < D ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+),
      2 ≤ (N : ℕ) → ∀ (i : Fin (N : ℕ)) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
      Integrable (fun X : Configuration N => (blockLength X (i : ℕ) k - k) ^ 2)
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ∧
      (∫ X : Configuration N, (blockLength X (i : ℕ) k - k) ^ 2
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
          D * (k : ℝ) ^ (3 * s / 2) := by
  obtain ⟨eps0, heps0, htail⟩ := hRig
  let eps := min (eps0 / 2) (s / 8)
  have heps : 0 < eps := lt_min (by positivity) (by positivity)
  have heps0' : eps < eps0 := (min_le_left _ _).trans_lt (by linarith)
  have hepss : eps ≤ s / 8 := min_le_right _ _
  obtain ⟨c, C, hc, hC, htail⟩ := htail eps heps heps0'
  obtain ⟨D4, hD4, hfour⟩ := bell_centered_fourth_moment
  let a := eps / (4 * (s + 2))
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨B, hB, hdec⟩ := gap_exp_neg_mul_le (half_pos hc)
    (p := (2 - 3 * s / 2) / a) (div_nonneg (by linarith) ha.le)
  refine ⟨1 + Real.sqrt D4 * Real.sqrt C * B, by positivity, ?_⟩
  intro hPL N hN i k hk hkN
  let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
  have := (modelWellDefined P N).2.2
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hZ : Measurable (fun X : Configuration N => blockLength X (i : ℕ) k - k) :=
    (measurable_blockLength _ _).sub_const _
  obtain ⟨hiZ4, hfour⟩ := hfour hPL P N hN (i : ℕ) k hk
  have hprob : (gibbsMeasure P N).real
      {X | (k : ℝ) ^ (s / 2 + eps) ≤ |blockLength X (i : ℕ) k - k|} ≤
        C * Real.exp (-c * (k : ℝ) ^ a) := by
    have hh := (htail N).1 i k hk hkN
    have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    rw [ENNReal.toReal_ofReal (by positivity)] at hh'
    exact hh'
  obtain ⟨hi2, hb2⟩ := second_moment_le_cutoff_add_sqrt hZ hiZ4
    (by positivity : 0 ≤ (k : ℝ) ^ (s / 2 + eps)) hfour hprob
  refine ⟨hi2, hb2.trans ?_⟩
  have hsqrtD : Real.sqrt (D4 * (k : ℝ) ^ 4) = Real.sqrt D4 * (k : ℝ) ^ 2 := by
    rw [Real.sqrt_mul hD4.le, show (k : ℝ) ^ 4 = ((k : ℝ) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg _)]
  have hsqrtC : Real.sqrt (C * Real.exp (-c * (k : ℝ) ^ a)) =
      Real.sqrt C * Real.exp (-(c / 2) * (k : ℝ) ^ a) := by
    rw [Real.sqrt_mul hC.le]
    congr 1
    rw [show Real.exp (-c * (k : ℝ) ^ a) =
        Real.exp (-(c / 2) * (k : ℝ) ^ a) ^ 2 by
      rw [← Real.exp_nat_mul]; congr 1; ring, Real.sqrt_sq (Real.exp_nonneg _)]
  have hsmall : ((k : ℝ) ^ (s / 2 + eps)) ^ 2 ≤ (k : ℝ) ^ (3 * s / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hk0.le]
    apply Real.rpow_le_rpow_of_exponent_le hk1
    norm_num
    linarith
  have hexp : Real.exp (-(c / 2) * (k : ℝ) ^ a) ≤ B * (k : ℝ) ^ (3 * s / 2 - 2) := by
    convert hdec ((k : ℝ) ^ a) (by positivity) using 1
    rw [← Real.rpow_mul hk0.le]
    congr 2
    field_simp
    ring
  have hpower : (k : ℝ) ^ 2 * (k : ℝ) ^ (3 * s / 2 - 2) = (k : ℝ) ^ (3 * s / 2) := by
    rw [← Real.rpow_natCast (k : ℝ) 2, ← Real.rpow_add hk0]
    congr 1
    push_cast
    ring
  rw [hsqrtD, hsqrtC]
  calc _ ≤ (k : ℝ) ^ (3 * s / 2) +
        Real.sqrt D4 * (k : ℝ) ^ 2 * (Real.sqrt C * (B * (k : ℝ) ^ (3 * s / 2 - 2))) := by
          gcongr
    _ = _ := by
        calc _ = (k : ℝ) ^ (3 * s / 2) + (Real.sqrt D4 * Real.sqrt C * B) *
            ((k : ℝ) ^ 2 * (k : ℝ) ^ (3 * s / 2 - 2)) := by ring
          _ = _ := by rw [hpower]; ring

end Internal

end Riesz1

end
