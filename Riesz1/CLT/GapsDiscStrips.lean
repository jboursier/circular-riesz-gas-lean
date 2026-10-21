/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscRotation
public import Riesz1.CLT.GapsDiscStripsVariance
public import Riesz1.Gibbs.FluctuationMoments
public import Riesz1.Bridges.FluctuationSquare

/-!
# Small boundary strips

Part of the proof of Corollary 1, first assertion. For every deterministic open
arc `I` of length `0 < t ≤ 1/4`, the centred count `#{i : x_i ∈ I} - Nt` has `L¹` norm at most
`2Nt` when `Nt < 1`, and at most `C (Nt)^{s/2}` when `Nt ≥ 1`, with `C` depending only on `s, β`.

The second moment for `Nt ≥ 1` comes from `gapsArc_integral_sq_le` at the centre `0`. The
rotation lemma `integral_rotate_linearStatistic` transfers it to every centre. The conditional
input is the variance conclusion `Internal.QuantitativeVarianceConclusion`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace Riesz1

/-- The arc count is the linear statistic of the indicator of the open arc. -/
lemma arcCount_eq_linearStatistic {N : ℕ+} (c : UnitAddCircle) (a : ℝ) (X : Configuration N) :
    arcCount c a X = linearStatistic (arcIndicator c a) X := rfl

/-- An arc about `c` is the translate of the arc about `0`: `1_{B(c,a)}(x) = 1_{B(0,a)}(x - c)`. -/
lemma arcIndicator_eq_arcIndicator_zero_add_neg (c : UnitAddCircle) (a : ℝ) (x : UnitAddCircle) :
    arcIndicator c a x = arcIndicator 0 a (x + -c) := by
  unfold arcIndicator
  rw [dist_zero_right, ← sub_eq_add_neg, ← dist_eq_norm]

/-- The second central moment of the arc count is the same at every centre. -/
lemma integral_arcCount_sq_centre (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (N : ℕ+) (c : UnitAddCircle) (a m : ℝ) (_ha0 : 0 ≤ a) (_ha1 : a ≤ 1 / 2) :
    ∫ X, (arcCount c a X - m) ^ 2 ∂(gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N) =
      ∫ X, (arcCount 0 a X - m) ^ 2 ∂(gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N) := by
  have hmeas : Measurable (fun y : ℝ => (y - m) ^ 2) := by fun_prop
  have hg : Measurable (arcIndicator 0 a) := measurable_arcIndicator 0 a
  have key := integral_rotate_linearStatistic ⟨(beta, s), hbeta, hs, hs1⟩ N (arcIndicator 0 a)
    (-c) (fun y => (y - m) ^ 2) hmeas hg
  simp only [arcCount_eq_linearStatistic]
  have hc : ∀ x, arcIndicator c a x = arcIndicator 0 a (x + -c) :=
    fun x => arcIndicator_eq_arcIndicator_zero_add_neg c a x
  have hlin : ∀ X : Configuration N, linearStatistic (arcIndicator c a) X =
      linearStatistic (fun x => arcIndicator 0 a (x + -c)) X := by
    intro X
    unfold linearStatistic
    simp only [hc]
  simp only [hlin]
  exact key

/-- Cauchy–Schwarz for a probability measure: the first absolute moment of an `L²` function is at
most the square root of its second moment. -/
lemma gapsDisc_integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Ω → ℝ) (hF : MemLp F 2 μ) :
    ∫ ω, |F ω| ∂μ ≤ Real.sqrt (∫ ω, F ω ^ 2 ∂μ) := by
  have hA : MemLp (fun ω => |F ω|) 2 μ := by
    simpa [Real.norm_eq_abs] using hF.norm
  have hvar := ProbabilityTheory.variance_eq_sub hA
  have hnn := ProbabilityTheory.variance_nonneg (fun ω => |F ω|) μ
  have hsq : ∫ ω, |F ω| ^ 2 ∂μ = ∫ ω, F ω ^ 2 ∂μ := by
    congr 1
    funext ω
    rw [sq_abs]
  have hvar' : ProbabilityTheory.variance (fun ω => |F ω|) μ =
      ∫ ω, |F ω| ^ 2 ∂μ - (∫ ω, |F ω| ∂μ) ^ 2 := by
    rw [hvar]
    simp only [Pi.pow_apply]
  have key : (∫ ω, |F ω| ∂μ) ^ 2 ≤ ∫ ω, F ω ^ 2 ∂μ := by
    rw [← hsq]
    linarith
  exact (le_abs_self _).trans (Real.abs_le_sqrt key)

/-- **Boundary strips, first assertion.** Let `0 < s < 1` and `β > 0`. The constant `C` depends only
on `s, β` (through the variance conclusion of Theorem 2), and for every
open arc of length `0 < t ≤ 1/4`, the centred count obeys the stated `L¹` bound. -/
theorem gapsDisc_strips_arc (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hQV : Internal.QuantitativeVarianceConclusion beta s hbeta hs hs1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (c : UnitAddCircle) (t : ℝ), 0 < t → t ≤ 1 / 4 →
      ∫ X, |arcCount c (t / 2) X - (N : ℝ) * t|
        ∂(gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N) ≤
          if (N : ℝ) * t < 1 then 2 * ((N : ℝ) * t) else C * ((N : ℝ) * t) ^ (s / 2) := by
  obtain ⟨K, hK, hKbound⟩ := gapsArc_integral_sq_le beta s hbeta hs hs1 hQV
  refine ⟨Real.sqrt K, Real.sqrt_pos.mpr hK, fun N c t ht0 ht1 => ?_⟩
  set P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩ with hPdef
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hmemR : MemLp (arcIndicator c (t / 2)) 2 volume := by
    simpa using (memLp_arcIndicator c (t / 2)).re
  obtain ⟨hmem0, hpt0⟩ := gapsArc_fluctuation_eq N ht0 ht1
  have hF_L2 : MemLp (fun X => arcCount c (t / 2) X - (N : ℝ) * t) 2 (gibbsMeasure P N) := by
    have h := memLp_fluctuation P N hmemR
    have hfun : (fun X : Configuration N => arcCount c (t / 2) X - (N : ℝ) * t) =
        fun X => fluctuation ⟨arcIndicator c (t / 2), hmemR.integrable one_le_two⟩ X := by
      funext X
      rw [← arcCount_sub_eq_fluctuation c (by linarith) (by linarith) _ X]
      congr 1
      ring
    rw [hfun]
    exact h
  have hmean : ∫ X, (arcCount c (t / 2) X - (N : ℝ) * t) ∂(gibbsMeasure P N) = 0 := by
    have hfun : (fun X : Configuration N => arcCount c (t / 2) X - (N : ℝ) * t) =
        fun X => fluctuation ⟨arcIndicator c (t / 2), hmemR.integrable one_le_two⟩ X := by
      funext X
      rw [← arcCount_sub_eq_fluctuation c (by linarith) (by linarith) _ X]
      congr 1
      ring
    rw [hfun]
    exact integral_fluctuation_eq_zero P N hmemR
  by_cases hNt : (N : ℝ) * t < 1
  · simp only [hNt, ↓reduceIte]
    have hint : Integrable (fun X : Configuration N => arcCount c (t / 2) X) (gibbsMeasure P N) := by
      have h := memLp_linearStatistic P N hmemR
      exact h.integrable one_le_two
    have hFint : Integrable (fun X : Configuration N => arcCount c (t / 2) X - (N : ℝ) * t)
        (gibbsMeasure P N) := hint.sub (integrable_const _)
    have hmono : ∫ X, |arcCount c (t / 2) X - (N : ℝ) * t| ∂(gibbsMeasure P N) ≤
        ∫ X, (arcCount c (t / 2) X + (N : ℝ) * t) ∂(gibbsMeasure P N) := by
      refine integral_mono hFint.abs (hint.add (integrable_const _)) fun X => ?_
      have hcount : 0 ≤ arcCount c (t / 2) X := by
        unfold arcCount
        exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
      have hNt0 : 0 ≤ (N : ℝ) * t := by positivity
      rw [abs_le]
      constructor <;> linarith
    have hC : ∫ X, arcCount c (t / 2) X ∂(gibbsMeasure P N) = (N : ℝ) * t := by
      have h1 := hmean
      rw [integral_sub hint (integrable_const _), integral_const] at h1
      simp only [probReal_univ, one_smul] at h1
      linarith
    have hsum : ∫ X, (arcCount c (t / 2) X + (N : ℝ) * t) ∂(gibbsMeasure P N) =
        2 * ((N : ℝ) * t) := by
      rw [integral_add hint (integrable_const _), integral_const, hC]
      simp only [probReal_univ, one_smul]
      ring
    linarith
  · simp only [hNt, ↓reduceIte]
    have hcs := gapsDisc_integral_abs_le_sqrt_integral_sq (gibbsMeasure P N)
      (fun X => arcCount c (t / 2) X - (N : ℝ) * t) hF_L2
    have hsq : ∫ X, (arcCount c (t / 2) X - (N : ℝ) * t) ^ 2 ∂(gibbsMeasure P N) ≤
        K * ((N : ℝ) * t) ^ s := by
      have hrot := integral_arcCount_sq_centre beta s hbeta hs hs1 N c (t / 2) ((N : ℝ) * t)
        (by linarith) (by linarith)
      rw [hrot]
      exact hKbound N t ht0 ht1 (not_lt.mp hNt)
    calc ∫ X, |arcCount c (t / 2) X - (N : ℝ) * t| ∂(gibbsMeasure P N)
        ≤ Real.sqrt (∫ X, (arcCount c (t / 2) X - (N : ℝ) * t) ^ 2 ∂(gibbsMeasure P N)) := hcs
      _ ≤ Real.sqrt (K * ((N : ℝ) * t) ^ s) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt K * ((N : ℝ) * t) ^ (s / 2) := by
        have hx : 0 ≤ (N : ℝ) * t := by positivity
        rw [Real.sqrt_mul hK.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx,
          show s / 2 = s * (1 / 2) by ring]

end Riesz1

end
end
