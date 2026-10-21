/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.BellRandomSumComparison
public import Riesz1.ToMathlib.LogConcave.EventSecondMoment

/-!
# Inverse moments for the bad event

The values of the averaged kernel at a block and at its lattice length are
controlled by inverse powers. Their second moment uses inverse block moments
of order twice the Riesz exponent.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

/-- Inverse powers controlling the two kernel values. -/
def bellValueWeight (s : ℝ) {N : ℕ+} (j : ℤ) (k : ℕ) (X : Configuration N) : ℝ :=
  blockLength X j k ^ (-s) +
    blockLength X (j + k) ((N : ℕ) - k) ^ (-s) +
      (k : ℝ) ^ (-s) + (((N : ℕ) - k : ℕ) : ℝ) ^ (-s)

lemma bellValueWeight_nonneg (s : ℝ) {N : ℕ+} (j : ℤ) {k : ℕ}
    (hk : 0 < k) (hkN : k < (N : ℕ)) (X : Configuration N) :
    0 ≤ bellValueWeight s j k X := by
  unfold bellValueWeight
  have h1 := (blockLength_pos X j hk).le
  have h2 := (blockLength_pos X (j + k) (show 0 < (N : ℕ) - k by omega)).le
  positivity

lemma measurable_bellValueWeight (s : ℝ) (N : ℕ+) (j : ℤ) (k : ℕ) :
    Measurable (@bellValueWeight s N j k) := by
  exact ((((measurable_blockLength j k).pow_const _).add
    ((measurable_blockLength (j + k) ((N : ℕ) - k)).pow_const _)).add_const _).add_const _

/-- Four real squares control the square of their sum. -/
lemma bell_four_sum_sq_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

/-- The second moment of the value bound is of order `k^(-2s)`
for every short block. -/
theorem bell_value_weight_second_moment (P : Parameters) :
    ∃ M : ℝ, 0 < M ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (j : ℤ)
      (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
      Integrable (fun X : Configuration N => bellValueWeight P.1.2 j k X ^ 2)
        (gibbsMeasure P N) ∧
      (∫ X : Configuration N, bellValueWeight P.1.2 j k X ^ 2 ∂gibbsMeasure P N) ≤
        M * (k : ℝ) ^ (-2 * P.1.2) := by
  let p := 2 * P.1.2
  have hp : 0 < p := by dsimp [p]; linarith [P.2.2.1]
  obtain ⟨Cm, hCm, hm⟩ := inverse_blocks_uniform P hp
  refine ⟨8 * (Cm + 1), by positivity, ?_⟩
  intro hPL N j k hk hkN
  have := (modelWellDefined P N).2.2
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hkN' : k < (N : ℕ) := by omega
  have hkcomp : 0 < (N : ℕ) - k := by omega
  have hcomp : (k : ℝ) ≤ (((N : ℕ) - k : ℕ) : ℝ) := by exact_mod_cast (show k ≤ (N : ℕ) - k by omega)
  have he : (-P.1.2) * 2 = -p := by dsimp [p]; ring
  have he' : -p = -2 * P.1.2 := by dsimp [p]; ring
  obtain ⟨hi, hb⟩ := hm hPL N j k hk
  obtain ⟨hi', hb'⟩ := hm hPL N (j + k) ((N : ℕ) - k) hkcomp
  have hbi : (∫ X : Configuration N, blockLength X j k ^ (-p) ∂gibbsMeasure P N) ≤
      Cm * (k : ℝ) ^ (-p) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun X => Real.rpow_nonneg (blockLength_pos X j hk).le _)] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
  have hbi' : (∫ X : Configuration N, blockLength X (j + k) ((N : ℕ) - k) ^ (-p)
      ∂gibbsMeasure P N) ≤ Cm * (k : ℝ) ^ (-p) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi'
      (ae_of_all _ fun X => Real.rpow_nonneg (blockLength_pos X (j + k) hkcomp).le _)] at hb'
    have hbr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb'
    exact hbr.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hk0 hcomp (by linarith)) hCm.le)
  have hc : (((N : ℕ) - k : ℕ) : ℝ) ^ (-p) ≤ (k : ℝ) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hk0 hcomp (by linarith)
  let B : Configuration N → ℝ := fun X => 4 *
    (blockLength X j k ^ (-p) + blockLength X (j + k) ((N : ℕ) - k) ^ (-p) +
      (k : ℝ) ^ (-p) + (((N : ℕ) - k : ℕ) : ℝ) ^ (-p))
  have hiB : Integrable B (gibbsMeasure P N) :=
    ((((hi.add hi').add (integrable_const _)).add (integrable_const _)).const_mul 4)
  have hbd (X : Configuration N) : bellValueWeight P.1.2 j k X ^ 2 ≤ B X := by
    have hh := bell_four_sum_sq_le (blockLength X j k ^ (-P.1.2))
      (blockLength X (j + k) ((N : ℕ) - k) ^ (-P.1.2))
      ((k : ℝ) ^ (-P.1.2)) ((((N : ℕ) - k : ℕ) : ℝ) ^ (-P.1.2))
    have hpow (z : ℝ) (hz : 0 ≤ z) : (z ^ (-P.1.2)) ^ 2 = z ^ (-p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz]
      norm_num only [Nat.cast_ofNat]
      rw [he]
    rw [hpow _ (blockLength_pos X j hk).le,
      hpow _ (blockLength_pos X (j + k) hkcomp).le,
      hpow _ hk0.le, hpow _ (by positivity)] at hh
    exact hh
  have hiW : Integrable (fun X : Configuration N => bellValueWeight P.1.2 j k X ^ 2)
      (gibbsMeasure P N) := by
    apply hiB.mono' ((measurable_bellValueWeight _ _ _ _).pow_const 2).aestronglyMeasurable
    exact ae_of_all _ fun X => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hbd X
  refine ⟨hiW, ?_⟩
  calc _ ≤ ∫ X : Configuration N, B X ∂gibbsMeasure P N := integral_mono hiW hiB hbd
    _ = 4 * ((∫ X : Configuration N, blockLength X j k ^ (-p) ∂gibbsMeasure P N) +
        (∫ X : Configuration N, blockLength X (j + k) ((N : ℕ) - k) ^ (-p)
          ∂gibbsMeasure P N) + (k : ℝ) ^ (-p) + (((N : ℕ) - k : ℕ) : ℝ) ^ (-p)) := by
        dsimp [B]
        rw [integral_const_mul]
        have hiSum : Integrable (fun X : Configuration N => blockLength X j k ^ (-p) +
            blockLength X (j + k) ((N : ℕ) - k) ^ (-p)) (gibbsMeasure P N) := hi.add hi'
        have hiSum2 : Integrable (fun X : Configuration N => blockLength X j k ^ (-p) +
            blockLength X (j + k) ((N : ℕ) - k) ^ (-p) + (k : ℝ) ^ (-p))
            (gibbsMeasure P N) := hiSum.add (integrable_const _)
        rw [integral_add hiSum2 (integrable_const _),
          integral_add hiSum (integrable_const _), integral_add hi hi']
        simp
    _ ≤ 4 * (Cm * (k : ℝ) ^ (-p) + Cm * (k : ℝ) ^ (-p) +
        (k : ℝ) ^ (-p) + (k : ℝ) ^ (-p)) := by gcongr
    _ = _ := by rw [← he']; ring

end Riesz1

end
