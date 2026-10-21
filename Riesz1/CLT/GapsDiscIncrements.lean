/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscMoments
public import Riesz1.CLT.GapsDiscInversion

/-!
# First moments at the selected particle

The selection-law and Cauchy--Schwarz step in
the inversion argument for Corollary 1. The bound is uniform in the
offset from the selected particle, before introducing any sequence of scales.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped ENNReal

namespace Riesz1

private def shiftedBlockAbs (N : ℕ+) (i : ℤ) (r : ℕ) (g : Fin (N : ℕ) → ℝ) : ℝ :=
  |(∑ a ∈ range r, gapOf g (i + a)) - r|

private lemma shiftedBlockAbs_measurable (N : ℕ+) (i : ℤ) (r : ℕ) :
    Measurable (shiftedBlockAbs N i r) := by
  apply continuous_abs.measurable.comp
  apply Measurable.sub_const
  apply Finset.measurable_sum
  intro a _
  exact measurable_pi_apply _

private lemma shiftedBlockAbs_eval {N : ℕ+} (X : Configuration N) (i j : ℤ) (r : ℕ) :
    shiftedBlockAbs N i r (gapFrom X j) = |blockLength X (j + i) r - r| := by
  have heq (a : ℕ) : gapOf (gapFrom X j) (i + a) = gap X (j + i + a) := by
    rw [gapFrom_eq_shiftFin, gapOf_shiftFin, ← gap_eq_gapOf_gapVector]
    rw [add_assoc]
  simp only [shiftedBlockAbs, heq, blockLength_eq_sum]

namespace Internal

theorem gapsDisc_selectedBlock_firstMoment_of_rigidity (beta s : ℝ) (hbeta : 0 < beta)
    (hs : 0 < s) (hs1 : s < 1) (hPL : External.PrekopaLeindler)
    (hRig : RigidityConclusion beta s hbeta hs hs1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (i : ℤ) (r : ℕ),
      1 ≤ r → r ≤ (N : ℕ) / 2 →
      (∫⁻ X : Configuration N,
        ENNReal.ofReal |blockLength X (nearestLabel X + i) r - r|
          ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
            ENNReal.ofReal (C * (r : ℝ) ^ (3 * s / 4)) := by
  obtain ⟨K, hK, hb⟩ := gapsDisc_secondMoment_of_rigidity beta s hbeta hs hs1 hPL hRig
  obtain ⟨W, hW, hw⟩ := nearest_selection_moments hPL
  refine ⟨W * Real.sqrt K, by positivity, fun N hN i r hr hrN => ?_⟩
  let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
  let G := shiftedBlockAbs N i r
  have hG : Measurable G := shiftedBlockAbs_measurable N i r
  have hsel := nearest_selection_nonneg P N hN G hG (fun _ => abs_nonneg _)
  simp only [G, shiftedBlockAbs_eval, zero_add] at hsel
  rw [hsel]
  have hmW : Measurable (fun X : Configuration N => ENNReal.ofReal (selectionWeight X 0)) :=
    (measurable_selectionWeight 0).ennreal_ofReal
  have hmB : Measurable (fun X : Configuration N =>
      ENNReal.ofReal |blockLength X i r - r|) :=
    (continuous_abs.measurable.comp ((measurable_blockLength i r).sub_const r)).ennreal_ofReal
  have hpq : Real.HolderConjugate 2 2 :=
    (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).mpr (by norm_num)
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (gibbsMeasure P N) hpq
    hmW.aemeasurable hmB.aemeasurable
  have hwp (X : Configuration N) : ENNReal.ofReal (selectionWeight X 0) ^ (2 : ℝ) =
      ENNReal.ofReal (selectionWeight X 0 ^ 2) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (selectionWeight_nonneg X 0) (by norm_num), Real.rpow_two]
  have hbp (X : Configuration N) : ENNReal.ofReal |blockLength X i r - r| ^ (2 : ℝ) =
      ENNReal.ofReal ((blockLength X i r - r) ^ 2) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), Real.rpow_two, sq_abs]
  simp only [hwp, hbp] at hcs
  simp_rw [ENNReal.ofReal_mul (selectionWeight_nonneg _ 0)]
  apply hcs.trans
  have hbound := mul_le_mul' (ENNReal.rpow_le_rpow (hw P N hN).1
      (show (0 : ℝ) ≤ 1 / 2 by norm_num))
    (ENNReal.rpow_le_rpow (hb N hN i r hr hrN) (show (0 : ℝ) ≤ 1 / 2 by norm_num))
  apply hbound.trans_eq
  have hr0 : (0 : ℝ) ≤ r := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg W) (by norm_num),
    ← Real.sqrt_eq_rpow, Real.sqrt_sq hW.le,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ← Real.sqrt_eq_rpow, Real.sqrt_mul hK.le]
  simp only [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul hr0, ← ENNReal.ofReal_mul hW.le]
  congr 1
  have he : 3 * s / 2 * (1 / 2) = 3 * s / 4 := by ring
  rw [he]
  ring

/-- The short-increment first moment, uniformly for every `|r| ≤ N/2` and every `k`.
This strengthens the finite-`N` estimate used in the inversion argument for Corollary 1. -/
theorem gapsDisc_increment_firstMoment_of_rigidity (beta s : ℝ) (hbeta : 0 < beta)
    (hs : 0 < s) (hs1 : s < 1) (hPL : External.PrekopaLeindler)
    (hRig : RigidityConclusion beta s hbeta hs hs1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (k : ℕ) (r : ℤ),
      r.natAbs ≤ (N : ℕ) / 2 →
      (∫⁻ X : Configuration N, ENNReal.ofReal |selectedIncrement X k r|
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
          ENNReal.ofReal (C * (r.natAbs : ℝ) ^ (3 * s / 4)) := by
  obtain ⟨C, hC, hb⟩ :=
    gapsDisc_selectedBlock_firstMoment_of_rigidity beta s hbeta hs hs1 hPL hRig
  refine ⟨C, hC, fun N hN k r hr => ?_⟩
  cases r with
  | ofNat n =>
    cases n with
    | zero => simp [selectedIncrement_zero, Real.zero_rpow (show 3 * s / 4 ≠ 0 by positivity)]
    | succ n =>
      simpa only [Int.ofNat_eq_natCast, Int.natAbs_natCast, selectedIncrement_nonneg_index] using
        hb N hN (k : ℤ) (n + 1) (by omega) hr
  | negSucc n =>
    have heq : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
    rw [heq] at hr ⊢
    simp only [Int.natAbs_neg, Int.natAbs_natCast, selectedIncrement_neg_index, abs_neg] at hr ⊢
    have hb' := hb N hN ((k : ℤ) - (n + 1 : ℕ)) (n + 1) (by omega) hr
    simpa only [add_sub_assoc] using hb'

/-- Integrability and the ordinary expectation form of the short-increment bound. -/
theorem gapsDisc_increment_expectation_of_rigidity (beta s : ℝ) (hbeta : 0 < beta)
    (hs : 0 < s) (hs1 : s < 1) (hPL : External.PrekopaLeindler)
    (hRig : RigidityConclusion beta s hbeta hs hs1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (k : ℕ) (r : ℤ),
      r.natAbs ≤ (N : ℕ) / 2 →
      Integrable (fun X : Configuration N => selectedIncrement X k r)
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ∧
      (∫ X : Configuration N, |selectedIncrement X k r|
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
          C * (r.natAbs : ℝ) ^ (3 * s / 4) := by
  obtain ⟨C, hC, hb⟩ :=
    gapsDisc_increment_firstMoment_of_rigidity beta s hbeta hs hs1 hPL hRig
  refine ⟨C, hC, fun N hN k r hr => ?_⟩
  have hm := measurable_selectedIncrement (N := N) k r
  have hi : Integrable (fun X : Configuration N => |selectedIncrement X k r|)
      (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) := by
    refine ⟨(continuous_abs.measurable.comp hm).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun X => abs_nonneg _)]
    exact (hb N hN k r hr).trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi.mono' hm.aestronglyMeasurable (ae_of_all _ fun X => by
    simp only [Real.norm_eq_abs, le_refl]), ?_⟩
  have h := hb N hN k r hr
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun X => abs_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

end Internal

end Riesz1

end
end
