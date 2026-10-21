/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscBias
public import Riesz1.CLT.GapsDiscMoments
public import Riesz1.CLT.GapsDiscScale
public import Riesz1.ToMathlib.Inversion.IntegralBounds
public import Riesz1.ToMathlib.Inversion.BiasAveraging

/-!
# Averaging bounds for the nearest-particle bias

The finite-particle estimate of Corollary 1.
The averaging window may be any positive block length at most half the period.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped ENNReal

namespace Riesz1

variable {N : ℕ+}

private lemma block_sum_shift (X : Configuration N) (j : ℤ) (k : ℕ) :
    ∑ a ∈ range k, gapOf (shiftFin N j (gapVector X)) a = blockLength X j k := by
  simp only [gapOf_shiftFin, ← gap_eq_gapOf_gapVector, blockLength_eq_sum]

private lemma integral_gap_shift (P : Parameters) (hN : 2 ≤ (N : ℕ))
    (G : (Fin (N : ℕ) → ℝ) → ℝ) (hG : Measurable G) (j : ℕ) :
    (∫ X, G (shiftFin N (j : ℤ) (gapVector X)) ∂gibbsMeasure P N) =
      ∫ X, G (gapVector X) ∂gibbsMeasure P N := by
  have hm := (measurable_shiftFin (j : ℤ)).comp (measurable_gapVector N)
  change (∫ X, G ((shiftFin N (j : ℤ) ∘ gapVector) X) ∂gibbsMeasure P N) = _
  have hmap := map_shiftFin_gibbsMeasure P hN j
  change Measure.map (shiftFin N (j : ℤ) ∘ gapVector) (gibbsMeasure P N) = _ at hmap
  rw [← integral_map hm.aemeasurable hG.aestronglyMeasurable, hmap,
    integral_map (measurable_gapVector N).aemeasurable hG.aestronglyMeasurable]

/-- The weighted normalized block functional has the same expectation at every
nonnegative label. The proof uses cyclic invariance of the full gap vector. -/
lemma gapsDisc_weighted_integral_shift (P : Parameters) (hN : 2 ≤ (N : ℕ))
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ (N : ℕ) / 2) (f : ℝ → ℝ) (hf : Measurable f)
    (j : ℕ) :
    (∫ X, selectionWeight X j * f (centeredGap (parametersExponent P) X j k hk)
      ∂gibbsMeasure P N) =
      ∫ X, selectionWeight X 0 * f (centeredGap (parametersExponent P) X 0 k hk)
        ∂gibbsMeasure P N := by
  let G := fun g : Fin (N : ℕ) → ℝ =>
    ((gapOf g (-1) + gapOf g 0) / 2) *
      f (((∑ a ∈ range k, gapOf g a) - k) / gapScale (parametersExponent P) N k)
  have hsum : Measurable (fun g : Fin (N : ℕ) → ℝ => ∑ a ∈ range k, gapOf g a) :=
    Finset.measurable_sum _ fun a _ => measurable_pi_apply _
  have hw : Measurable (fun g : Fin (N : ℕ) → ℝ =>
      (gapOf g (-1) + gapOf g 0) / 2) := by
    unfold gapOf
    fun_prop
  have hG : Measurable G := by
    dsimp only [G]
    exact hw.mul (hf.comp ((hsum.sub_const (k : ℝ)).div_const _))
  have heval (X : Configuration N) (i : ℤ) :
      G (shiftFin N i (gapVector X)) =
        selectionWeight X i * f (centeredGap (parametersExponent P) X i k hk) := by
    dsimp only [G]
    rw [gapOf_shiftFin_selectionWeight, block_sum_shift]
    rfl
  have h := integral_gap_shift P hN G hG j
  have hzero (X : Configuration N) : G (gapVector X) =
      selectionWeight X 0 * f (centeredGap (parametersExponent P) X 0 k hk) := by
    simpa only [shiftFin_zero] using heval X 0
  simpa only [heval, hzero] using h

private lemma weight_sq_shift (P : Parameters) (hN : 2 ≤ (N : ℕ)) (j : ℕ) :
    (∫⁻ X, ENNReal.ofReal (selectionWeight X j ^ 2) ∂gibbsMeasure P N) =
      ∫⁻ X, ENNReal.ofReal (selectionWeight X 0 ^ 2) ∂gibbsMeasure P N := by
  let G := fun g : Fin (N : ℕ) → ℝ =>
    ENNReal.ofReal (((gapOf g (-1) + gapOf g 0) / 2) ^ 2)
  have hG : Measurable G := by
    dsimp only [G, gapOf]
    fun_prop
  have h := lintegral_shiftFin_gapVector P hN G hG j
  have heval (X : Configuration N) (i : ℤ) :
      G (shiftFin N i (gapVector X)) = ENNReal.ofReal (selectionWeight X i ^ 2) := by
    dsimp only [G]
    rw [gapOf_shiftFin_selectionWeight]
  have hzero (X : Configuration N) : G (gapVector X) = ENNReal.ofReal (selectionWeight X 0 ^ 2) := by
    simpa only [shiftFin_zero] using heval X 0
  simpa only [heval, hzero] using h

namespace Internal

/-- The two first-moment estimates used in the averaging proof, with one constant
for all particle numbers, labels and block lengths, including the zero block. -/
theorem gapsDisc_bias_block_bounds_of_rigidity (beta s : ℝ) (hbeta : 0 < beta)
    (hs : 0 < s) (hs1 : s < 1) (hPL : External.PrekopaLeindler)
    (hRig : RigidityConclusion beta s hbeta hs hs1) :
    ∃ D W : ℝ, 0 < D ∧ 0 < W ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (i : ℤ) (j r : ℕ), r ≤ (N : ℕ) / 2 →
      Integrable (fun X : Configuration N => blockLength X i r - r)
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ∧
      (∫ X, |blockLength X i r - r|
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤ D * (r : ℝ) ^ (3 * s / 4) ∧
      Integrable (fun X : Configuration N => selectionWeight X j * |blockLength X i r - r|)
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ∧
      (∫ X, selectionWeight X j * |blockLength X i r - r|
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
          W * D * (r : ℝ) ^ (3 * s / 4) := by
  obtain ⟨K, hK, hb⟩ := gapsDisc_secondMoment_of_rigidity beta s hbeta hs hs1 hPL hRig
  obtain ⟨W, hW, hw⟩ := nearest_selection_moments hPL
  refine ⟨Real.sqrt K, W, Real.sqrt_pos.mpr hK, hW, fun N hN i j r hr => ?_⟩
  let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
  have := (modelWellDefined P N).2.2
  by_cases hr0 : r = 0
  · subst r
    simp only [blockLength_zero, Nat.cast_zero, sub_zero, abs_zero, mul_zero,
      Real.zero_rpow (show 3 * s / 4 ≠ 0 by positivity)]
    exact ⟨integrable_zero _ _ _, by simp, integrable_zero _ _ _, by simp⟩
  have hbr := hb N hN i r (by omega) hr
  have hm := (measurable_blockLength (N := N) i r).sub_const r
  obtain ⟨hi, hf⟩ := inversion_integral_abs_le hm (by positivity) hbr
  have hwr : (∫⁻ X : Configuration N, ENNReal.ofReal (selectionWeight X j ^ 2)
      ∂gibbsMeasure P N) ≤ ENNReal.ofReal (W ^ 2) := by
    rw [weight_sq_shift P hN j]
    exact (hw P N hN).1
  obtain ⟨hiw, hfw⟩ := inversion_integral_abs_mul_le (measurable_selectionWeight j) hm
    (sq_nonneg W) (by positivity) hwr hbr
  have heq : (fun X : Configuration N => |selectionWeight X j| * |blockLength X i r - r|) =
      (fun X => selectionWeight X j * |blockLength X i r - r|) := by
    funext X
    rw [abs_of_nonneg (selectionWeight_nonneg X j)]
  rw [heq] at hiw hfw
  have hroot : Real.sqrt (K * (r : ℝ) ^ (3 * s / 2)) =
      Real.sqrt K * (r : ℝ) ^ (3 * s / 4) := by
    rw [Real.sqrt_mul hK.le]
    simp only [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul (Nat.cast_nonneg r)]
    congr 2
    ring
  rw [hroot] at hf hfw
  rw [Real.sqrt_sq hW.le] at hfw
  exact ⟨hi, hf, hiw, by simpa only [mul_assoc] using hfw⟩


/-- Bias removal for every positive averaging window of at most half a period.
Taking `m = gapBiasWindow k` is the finite-particle assertion of
Corollary 1. -/
theorem gapsDisc_bias_average_of_rigidity (beta s : ℝ) (hbeta : 0 < beta)
    (hs : 0 < s) (hs1 : s < 1) (hPL : External.PrekopaLeindler)
    (hRig : RigidityConclusion beta s hbeta hs hs1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (k : ℕ) (hk : 1 ≤ k ∧ k ≤ (N : ℕ) / 2) (m : ℕ),
      1 ≤ m → m ≤ (N : ℕ) / 2 → ∀ (f : ℝ → ℝ),
      LipschitzWith 1 f → (∀ t, |f t| ≤ 1) →
      |(∫ X, selectionWeight X 0 * f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0 k hk)
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) -
        ∫ X, f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0 k hk)
          ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N| ≤
      C * ((m : ℝ) ^ (3 * s / 4 - 1) + (m : ℝ) ^ (3 * s / 4) / (k : ℝ) ^ (s / 2)) := by
  obtain ⟨D, W, hD, hW, hb⟩ := gapsDisc_bias_block_bounds_of_rigidity
    beta s hbeta hs hs1 hPL hRig
  let σ : RieszExponent := ⟨s, hs, hs1⟩
  obtain ⟨c, _, hc, _, hscale⟩ := gapsDisc_gapScale_comparison σ
  let L := 2 * W * D / c
  refine ⟨D + L, by dsimp [L]; positivity, fun N hN k hk m hm hmN f hf hfb => ?_⟩
  let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
  have := (modelWellDefined P N).2.2
  let b := gapScale σ N k
  let a := 3 * s / 4
  have ha : 0 < a := by dsimp [a]; positivity
  have hbp : 0 < b := gapsDisc_gapScale_pos σ N k hk.1 hk.2
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk.1
  have hbl : c * (k : ℝ) ^ (s / 2) ≤ b := (hscale N k hk.1 hk.2).1
  have hwi (j : ℕ) : Integrable (fun X : Configuration N => selectionWeight X j)
      (gibbsMeasure P N) := by
    apply integrable_of_abs_le P _ (measurable_selectionWeight j) (N : ℝ)
    intro X
    rw [abs_of_nonneg (selectionWeight_nonneg X j)]
    have hlo := gap_le_N X ((j : ℤ) - 1)
    have hhi := gap_le_N X (j : ℤ)
    unfold selectionWeight
    linarith
  have hdiff (j : ℕ) (hj : j ∈ range m) :
      Integrable (fun X : Configuration N => selectionWeight X j *
        |centeredGap σ X j k hk - centeredGap σ X 0 k hk|) (gibbsMeasure P N) ∧
      (∫ X, selectionWeight X j * |centeredGap σ X j k hk - centeredGap σ X 0 k hk|
        ∂gibbsMeasure P N) ≤ 2 * W * D * (j : ℝ) ^ a / b := by
    have hjN : j ≤ (N : ℕ) / 2 := (le_of_lt (mem_range.mp hj)).trans hmN
    obtain ⟨_, _, hi1, hb1⟩ := hb N hN (k : ℤ) j j hjN
    obtain ⟨_, _, hi0, hb0⟩ := hb N hN 0 j j hjN
    let E := fun X : Configuration N =>
      (selectionWeight X j * |blockLength X (k : ℤ) j - j| +
        selectionWeight X j * |blockLength X 0 j - j|) / b
    have hiE : Integrable E (gibbsMeasure P N) := (hi1.add hi0).div_const b
    have hpt (X : Configuration N) : selectionWeight X j *
        |centeredGap σ X j k hk - centeredGap σ X 0 k hk| ≤ E X := by
      have heq := centeredGap_shift_sub σ X 0 j k hk
      simp only [zero_add] at heq
      rw [heq, abs_div, abs_of_pos hbp]
      dsimp only [E]
      rw [← mul_div_assoc, ← mul_add]
      apply div_le_div_of_nonneg_right _ hbp.le
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) (selectionWeight_nonneg X j)
    have hi : Integrable (fun X : Configuration N => selectionWeight X j *
        |centeredGap σ X j k hk - centeredGap σ X 0 k hk|) (gibbsMeasure P N) := by
      refine hiE.mono' (((measurable_selectionWeight j).mul
        (continuous_abs.measurable.comp ((measurable_centeredGap σ j k hk).sub
          (measurable_centeredGap σ 0 k hk)))).aestronglyMeasurable) (ae_of_all _ fun X => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (selectionWeight_nonneg X j) (abs_nonneg _))]
      exact hpt X
    refine ⟨hi, (integral_mono hi hiE hpt).trans ?_⟩
    dsimp only [E]
    rw [integral_div, integral_add hi1 hi0]
    apply (div_le_div_of_nonneg_right (add_le_add hb1 hb0) hbp.le).trans_eq
    dsimp only [a]
    ring
  have hsumw : Integrable (fun X : Configuration N => ∑ j ∈ range m, selectionWeight X j)
      (gibbsMeasure P N) := integrable_finsetSum _ fun j _ => hwi j
  have hierr : Integrable (fun X : Configuration N => |(∑ j ∈ range m, selectionWeight X j) - m|)
      (gibbsMeasure P N) := (hsumw.sub (integrable_const _)).abs
  obtain ⟨hi1, hb1, _, _⟩ := hb N hN (-1) 0 m hmN
  obtain ⟨hi0, hb0, _, _⟩ := hb N hN 0 0 m hmN
  have hpt (X : Configuration N) : |(∑ j ∈ range m, selectionWeight X j) - m| ≤
      (|blockLength X (-1) m - m| + |blockLength X 0 m - m|) / 2 := by
    have heq := sum_selectionWeight_blockLength X 0 m
    simp only [zero_add, zero_sub] at heq
    rw [heq, show (blockLength X (-1) m + blockLength X 0 m) / 2 - m =
      ((blockLength X (-1) m - m) + (blockLength X 0 m - m)) / 2 by ring, abs_div]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  have herr : (∫ X, |(∑ j ∈ range m, selectionWeight X j) - m| ∂gibbsMeasure P N) ≤
      D * (m : ℝ) ^ a := by
    apply (integral_mono hierr ((hi1.abs.add hi0.abs).div_const 2) hpt).trans
    rw [integral_div]
    simp only [Pi.add_apply]
    rw [integral_add hi1.abs hi0.abs]
    dsimp only [a]
    linarith
  have hsumdiff : (∑ j ∈ range m, ∫ X, selectionWeight X j *
      |centeredGap σ X j k hk - centeredGap σ X 0 k hk| ∂gibbsMeasure P N) ≤
      (m : ℝ) * (2 * W * D * (m : ℝ) ^ a / b) := by
    calc _ ≤ ∑ _j ∈ range m, 2 * W * D * (m : ℝ) ^ a / b := by
          apply sum_le_sum
          intro j hj
          apply (hdiff j hj).2.trans
          apply div_le_div_of_nonneg_right _ hbp.le
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg j)
            (by exact_mod_cast (le_of_lt (mem_range.mp hj))) ha.le) (by positivity)
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
  have havg := inversion_bias_averaging_bound
    (μ := gibbsMeasure P N) (fun j X => selectionWeight X j)
    (fun j X => centeredGap σ X j k hk) m hm
    (fun j => measurable_selectionWeight j) (fun j => measurable_centeredGap σ j k hk)
    (fun j X => selectionWeight_nonneg X j) hwi (fun j hj => (hdiff j hj).1) f hf hfb
    (fun j => gapsDisc_weighted_integral_shift P hN k hk f hf.continuous.measurable j)
  apply havg.trans
  apply (div_le_div_of_nonneg_right (add_le_add herr hsumdiff) hmp.le).trans
  have hid : (D * (m : ℝ) ^ a + (m : ℝ) * (2 * W * D * (m : ℝ) ^ a / b)) / m =
      D * (m : ℝ) ^ (a - 1) + 2 * W * D * (m : ℝ) ^ a / b := by
    rw [Real.rpow_sub hmp, Real.rpow_one]
    field_simp
  rw [hid]
  have hden : 2 * W * D * (m : ℝ) ^ a / b ≤
      L * ((m : ℝ) ^ a / (k : ℝ) ^ (s / 2)) := by
    have h := div_le_div_of_nonneg_left (show 0 ≤ 2 * W * D * (m : ℝ) ^ a by positivity)
      (mul_pos hc (Real.rpow_pos_of_pos hkp _)) hbl
    apply h.trans_eq
    dsimp only [L]
    field_simp
  have hx0 : 0 ≤ (m : ℝ) ^ (a - 1) := by positivity
  have hy0 : 0 ≤ (m : ℝ) ^ a / (k : ℝ) ^ (s / 2) := by positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  dsimp only [a] at *
  nlinarith [mul_nonneg hD.le hy0, mul_nonneg hL hx0]

end Internal

end Riesz1

end
end
