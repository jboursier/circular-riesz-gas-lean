/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscDefs
public import Riesz1.Auxiliary.RigidityConclusion
public import Riesz1.ToMathlib.Inversion.SecondMoment

/-!
# Centered block second moments conditional on rigidity

The second-moment assertion in the proof of Corollary 1.
The external Prékopa--Leindler statement is passed explicitly, as required by
the fourth-moment estimate. Constants are chosen before the particle
number and both block indices.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

private lemma centeredBlock_fourth (hPL : External.PrekopaLeindler) :
    ∃ D : ℝ, 0 < D ∧ ∀ (P : Parameters) (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (i : ℤ) (r : ℕ), 1 ≤ r →
        (∫⁻ X : Configuration N, ENNReal.ofReal ((blockLength X i r - r) ^ 4)
          ∂gibbsMeasure P N) ≤ ENNReal.ofReal (D * (r : ℝ) ^ 4) := by
  obtain ⟨C, hC, hb⟩ := blockLength_moments 4 (by norm_num)
  refine ⟨8 * (C + 1), by positivity, fun P N hN i r hr => ?_⟩
  have := (modelWellDefined P N).2.2
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hpt (X : Configuration N) : (blockLength X i r - r) ^ 4 ≤
      8 * blockLength X i r ^ 4 + 8 * (r : ℝ) ^ 4 := by
    have hS := (blockLength_pos X i hr).le
    have hab : |blockLength X i r - r| ≤ blockLength X i r + r := by
      rw [abs_le]
      constructor <;> linarith
    have hpow := pow_le_pow_left₀ (abs_nonneg _) hab 4
    have hadd := add_pow_le hS hr0 4
    rw [show |blockLength X i r - r| ^ 4 = (blockLength X i r - r) ^ 4 from
      pow_abs_two_mul (n := 2) _] at hpow
    norm_num at hadd
    nlinarith
  have hraw := (hb hPL P N hN i r hr).2
  norm_num [Real.rpow_natCast] at hraw
  calc (∫⁻ X : Configuration N, ENNReal.ofReal ((blockLength X i r - r) ^ 4)
        ∂gibbsMeasure P N)
      ≤ ∫⁻ X : Configuration N, ENNReal.ofReal (8 : ℝ) *
          ENNReal.ofReal (blockLength X i r ^ 4) + ENNReal.ofReal (8 * (r : ℝ) ^ 4)
            ∂gibbsMeasure P N := by
        apply lintegral_mono
        intro X
        dsimp only
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hpt X)
    _ = ENNReal.ofReal (8 : ℝ) *
          (∫⁻ X : Configuration N, ENNReal.ofReal (blockLength X i r ^ 4)
            ∂gibbsMeasure P N) + ENNReal.ofReal (8 * (r : ℝ) ^ 4) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ ((measurable_blockLength i r).pow_const 4).ennreal_ofReal]
    _ ≤ ENNReal.ofReal (8 : ℝ) * ENNReal.ofReal (C * (r : ℝ) ^ 4) +
          ENNReal.ofReal (8 * (r : ℝ) ^ 4) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        ring

namespace Internal

/-- The squared `L²` bound in the proof of Corollary 1.
The nonnegative integral prevents any totalized-integral ambiguity. -/
theorem gapsDisc_secondMoment_of_rigidity (beta s : ℝ) (hbeta : 0 < beta)
    (hs : 0 < s) (hs1 : s < 1) (hPL : External.PrekopaLeindler)
    (hRig : RigidityConclusion beta s hbeta hs hs1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (i : ℤ) (r : ℕ),
      1 ≤ r → r ≤ (N : ℕ) / 2 →
      (∫⁻ X : Configuration N, ENNReal.ofReal ((blockLength X i r - r) ^ 2)
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
          ENNReal.ofReal (K * (r : ℝ) ^ (3 * s / 2)) := by
  obtain ⟨eps0, heps0, hRig⟩ := hRig
  let eps := min (eps0 / 2) (s / 8)
  have heps : 0 < eps := lt_min (by positivity) (by positivity)
  have heps0' : eps < eps0 := (min_le_left _ _).trans_lt (by linarith)
  have hepss : eps ≤ s / 8 := min_le_right _ _
  obtain ⟨c, C, hc, hC, htail⟩ := hRig eps heps heps0'
  obtain ⟨D, hD, hfour⟩ := centeredBlock_fourth hPL
  let a := eps / (4 * (s + 2))
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨B, hB, hdec⟩ := inversion_power_exp_bounded (2 - 3 * s / 2) ha (half_pos hc)
  let K := 1 + Real.sqrt D * Real.sqrt C * B
  refine ⟨K, by dsimp [K]; positivity, fun N hN i r hr hrN => ?_⟩
  let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
  have := (modelWellDefined P N).2.2
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  obtain ⟨j, hj, q, hi⟩ := exists_nat_add_mul (N := N) i
  have hperiod (X : Configuration N) : blockLength X i r = blockLength X j r := by
    rw [hi, blockLength_add_period_mul]
  have hprob : gibbsMeasure P N
      {X | (r : ℝ) ^ (s / 2 + eps) ≤ |blockLength X i r - r|} ≤
        ENNReal.ofReal (C * Real.exp (-c * (r : ℝ) ^ a)) := by
    simp_rw [hperiod]
    exact (htail N).1 ⟨j, hj⟩ r hr hrN
  have hsplit := inversion_secondMoment_split ((measurable_blockLength i r).sub_const r)
    (t := (r : ℝ) ^ (s / 2 + eps)) (D := D * (r : ℝ) ^ 4)
    (q := C * Real.exp (-c * (r : ℝ) ^ a)) (by positivity) (by positivity)
    (by positivity) (hfour P N hN i r hr) hprob
  have hsqrtD : Real.sqrt (D * (r : ℝ) ^ 4) = Real.sqrt D * (r : ℝ) ^ 2 := by
    rw [Real.sqrt_mul hD.le, show (r : ℝ) ^ 4 = ((r : ℝ) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg _)]
  have hsqrtC : Real.sqrt (C * Real.exp (-c * (r : ℝ) ^ a)) =
      Real.sqrt C * Real.exp (-(c / 2) * (r : ℝ) ^ a) := by
    rw [Real.sqrt_mul hC.le]
    congr 1
    rw [show Real.exp (-c * (r : ℝ) ^ a) =
        Real.exp (-(c / 2) * (r : ℝ) ^ a) ^ 2 by
      rw [← Real.exp_nat_mul]
      congr 1
      ring, Real.sqrt_sq (Real.exp_nonneg _)]
  have hsmall : ((r : ℝ) ^ (s / 2 + eps)) ^ 2 ≤ (r : ℝ) ^ (3 * s / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
    exact Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num; linarith)
  have hfactor : (r : ℝ) ^ 2 = (r : ℝ) ^ (3 * s / 2) *
      (r : ℝ) ^ (2 - 3 * s / 2) := by
    rw [← Real.rpow_add hr0]
    norm_num
  apply hsplit.trans
  apply ENNReal.ofReal_le_ofReal
  rw [hsqrtD, hsqrtC]
  have hb := hdec (r : ℝ) hr1
  have hlarge : Real.sqrt D * (r : ℝ) ^ 2 *
      (Real.sqrt C * Real.exp (-(c / 2) * (r : ℝ) ^ a)) ≤
        Real.sqrt D * Real.sqrt C * B * (r : ℝ) ^ (3 * s / 2) := by
    rw [hfactor]
    calc _ = (Real.sqrt D * Real.sqrt C * (r : ℝ) ^ (3 * s / 2)) *
        ((r : ℝ) ^ (2 - 3 * s / 2) * Real.exp (-(c / 2) * (r : ℝ) ^ a)) := by ring
      _ ≤ (Real.sqrt D * Real.sqrt C * (r : ℝ) ^ (3 * s / 2)) * B :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  dsimp [K]
  nlinarith

/-- Integrability is a consequence of the nonnegative second-moment estimate. -/
theorem gapsDisc_integrable_square_of_rigidity (beta s : ℝ) (hbeta : 0 < beta)
    (hs : 0 < s) (hs1 : s < 1) (hPL : External.PrekopaLeindler)
    (hRig : RigidityConclusion beta s hbeta hs hs1) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (i : ℤ) (r : ℕ) (hr : 1 ≤ r) (hrN : r ≤ (N : ℕ) / 2) :
    Integrable (fun X : Configuration N => (blockLength X i r - r) ^ 2)
      (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) := by
  obtain ⟨K, -, hb⟩ := gapsDisc_secondMoment_of_rigidity beta s hbeta hs hs1 hPL hRig
  refine ⟨(((measurable_blockLength i r).sub_const r).pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun X => sq_nonneg _)]
  exact (hb N hN i r hr hrN).trans_lt ENNReal.ofReal_lt_top

end Internal

end Riesz1

end
end
