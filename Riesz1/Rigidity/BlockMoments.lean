/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.GapLawMarginal
public import Riesz1.ToMathlib.LogConcave.ExpMoment
public import Riesz1.ToMathlib.LogConcave.Moments
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Jensen

/-!
# Uniform moments of block lengths

This is part of Lemma 4.2. Marginal log-concavity gives
the one-gap exponential moment. Finite Jensen, without independence,
then gives the same bound for every average of consecutive gaps.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The numerical exponent in the initial block estimate. -/
def blockMomentExponent : ℝ := Real.log 2 / 4

lemma blockMomentExponent_pos : 0 < blockMomentExponent :=
  div_pos (Real.log_pos one_lt_two) (by norm_num)

/-- Every exponential of a gap is integrable, before using a uniform bound. -/
lemma integrable_exp_gap (P : Parameters) (N : ℕ+) (j : ℤ) (c : ℝ) :
    Integrable (fun X : Configuration N => Real.exp (c * gap X j)) (gibbsMeasure P N) := by
  have := (modelWellDefined P N).2.2
  apply Integrable.of_bound ((measurable_const.mul (measurable_gap j)).exp).aestronglyMeasurable
    (Real.exp (|c| * (N : ℕ)))
  exact ae_of_all _ fun X => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc c * gap X j ≤ |c| * gap X j :=
          mul_le_mul_of_nonneg_right (le_abs_self c) (gap_pos X j).le
      _ ≤ |c| * (N : ℕ) := mul_le_mul_of_nonneg_left (gap_le_N X j) (abs_nonneg c)

/-- The explicit exponential moment bound for every nearest gap. -/
theorem integral_exp_gap_le (hPL : External.PrekopaLeindler) (P : Parameters)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (j : ℤ) :
    (∫ X : Configuration N, Real.exp (blockMomentExponent * gap X j) ∂gibbsMeasure P N) ≤ 3 := by
  have := (modelWellDefined P N).2.2
  obtain ⟨f, hlaw, hfc, hfp, hlog, -⟩ := exists_gap_density hPL P N hN j
  let b : ℝ := (N : ℕ)
  let f₀ : ℝ → ℝ := (Ioo 0 b).indicator f
  have hfm : Measurable f₀ := by
    have hm := hfc.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) measurableSet_Ioo
    convert hm using 1
    ext t
    by_cases ht : t ∈ Ioo 0 b <;> simp [f₀, ht, b]
  have hfn (t : ℝ) : 0 ≤ f₀ t := by
    by_cases ht : t ∈ Ioo 0 b
    · simpa only [f₀, Set.indicator_of_mem ht] using (hfp t ht).le
    · simp only [f₀, Set.indicator_of_notMem ht, le_refl]
  have hlaw₀ : (gibbsMeasure P N).map (fun X => gap X j) =
      volume.withDensity (fun t => ENNReal.ofReal (f₀ t)) := by
    rw [hlaw, ← withDensity_indicator measurableSet_Ioo]
    congr 1
    ext t
    change (Ioo 0 b).indicator (fun t => ENNReal.ofReal (f t)) t =
      ENNReal.ofReal ((Ioo 0 b).indicator f t)
    by_cases ht : t ∈ Ioo 0 b
    · simp [ht]
    · simp [ht]
  have htransfer (g : ℝ → ℝ) (hg : Measurable g) :
      (∫ X : Configuration N, g (gap X j) ∂gibbsMeasure P N) = ∫ t, g t * f₀ t := by
    rw [← integral_map (measurable_gap j).aemeasurable hg.aestronglyMeasurable, hlaw₀,
      integral_withDensity_eq_integral_toReal_smul hfm.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hfn _), smul_eq_mul, mul_comm]
  have hmass : ∫ t, f₀ t = 1 := by
    have ht := htransfer (fun _ => 1) measurable_const
    simpa using ht.symm
  have hmean : ∫ t, t * f₀ t = 1 := by
    exact (htransfer (fun t => t) measurable_id).symm.trans
      (integral_gap_gibbsMeasure P N hN j)
  have hpos : ∀ t ∈ Ioo 0 b, 0 < f₀ t := by
    intro t ht
    simpa only [f₀, Set.indicator_of_mem ht] using hfp t ht
  have hconc : ConcaveOn ℝ (Ioo 0 b) (fun t => Real.log (f₀ t)) := by
    apply hlog.congr
    intro t ht
    change Real.log (f t) = Real.log ((Ioo 0 b).indicator f t)
    rw [Set.indicator_of_mem ht]
  have hexp := logConcave_exp_moment_le (by dsimp [b]; positivity) f₀ hpos
    (fun t ht => Set.indicator_of_notMem ht _) hconc hmass hmean
  exact (htransfer (fun t => Real.exp (blockMomentExponent * t))
    (measurable_const.mul measurable_id).exp).le.trans hexp.2

/-- Pointwise finite Jensen for the normalized sum of gaps. -/
lemma exp_blockLength_div_le_average {N : ℕ+} (X : Configuration N) (j : ℤ)
    {L : ℕ} (hL : 0 < L) (c : ℝ) :
    Real.exp (c * (blockLength X j L / L)) ≤
      (L : ℝ)⁻¹ * ∑ r ∈ Finset.range L, Real.exp (c * gap X (j + r)) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have h := convexOn_exp.map_sum_le (t := Finset.range L)
    (w := fun _ => (L : ℝ)⁻¹) (p := fun r : ℕ => c * gap X (j + r))
    (fun _ _ => inv_nonneg.mpr hLr.le) (by simp [hLr.ne']) (fun _ _ => mem_univ _)
  simp only [smul_eq_mul, ← Finset.mul_sum] at h
  have heq : c * (blockLength X j L / L) =
      (L : ℝ)⁻¹ * (c * ∑ r ∈ Finset.range L, gap X (j + r)) := by
    rw [blockLength_eq_sum, div_eq_mul_inv]
    ring
  rw [heq]
  exact h

/-- **Exponential block estimate**, part of Lemma 4.2.
The statement holds for every positive block length, including lengths exceeding `N`. -/
theorem blockLength_exp_moment (hPL : External.PrekopaLeindler) (P : Parameters)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (j : ℤ) (L : ℕ) (hL : 0 < L) :
    Integrable (fun X : Configuration N =>
      Real.exp (blockMomentExponent * (blockLength X j L / L))) (gibbsMeasure P N) ∧
    (∫ X : Configuration N,
      Real.exp (blockMomentExponent * (blockLength X j L / L)) ∂gibbsMeasure P N) ≤ 3 := by
  have := (modelWellDefined P N).2.2
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hs : Integrable (fun X : Configuration N =>
      ∑ r ∈ Finset.range L, Real.exp (blockMomentExponent * gap X (j + r)))
      (gibbsMeasure P N) :=
    integrable_finsetSum (Finset.range L) (fun (r : ℕ) _ =>
      integrable_exp_gap P N (j + r) blockMomentExponent)
  have hi : Integrable (fun X : Configuration N =>
      (L : ℝ)⁻¹ * ∑ r ∈ Finset.range L, Real.exp (blockMomentExponent * gap X (j + r)))
      (gibbsMeasure P N) :=
    hs.const_mul (L : ℝ)⁻¹
  have hb := fun X : Configuration N => exp_blockLength_div_le_average X j hL blockMomentExponent
  have hm : Measurable (fun X : Configuration N =>
      Real.exp (blockMomentExponent * (blockLength X j L / L))) :=
    ((measurable_const.mul ((measurable_blockLength j L).div_const (L : ℝ))).exp)
  have he : Integrable (fun X : Configuration N =>
      Real.exp (blockMomentExponent * (blockLength X j L / L))) (gibbsMeasure P N) := by
    refine hi.mono' hm.aestronglyMeasurable (ae_of_all _ fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hb X
  refine ⟨he, ?_⟩
  calc (∫ X : Configuration N,
        Real.exp (blockMomentExponent * (blockLength X j L / L)) ∂gibbsMeasure P N)
      ≤ ∫ X : Configuration N,
        (L : ℝ)⁻¹ * ∑ r ∈ Finset.range L, Real.exp (blockMomentExponent * gap X (j + r))
          ∂gibbsMeasure P N := integral_mono he hi hb
    _ = (L : ℝ)⁻¹ * ∑ r ∈ Finset.range L,
        ∫ X : Configuration N, Real.exp (blockMomentExponent * gap X (j + r))
          ∂gibbsMeasure P N := by
      rw [integral_const_mul,
        integral_finsetSum (Finset.range L) (fun (r : ℕ) _ =>
          integrable_exp_gap P N (j + r) blockMomentExponent)]
    _ ≤ (L : ℝ)⁻¹ * ∑ _r ∈ Finset.range L, (3 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => integral_exp_gap_le hPL P N hN _)
        (inv_nonneg.mpr hLr.le)
    _ = 3 := by simp [hLr.ne']

/-- Every block length is positive when it contains at least one gap. -/
lemma blockLength_pos {N : ℕ+} (X : Configuration N) (j : ℤ) {L : ℕ} (hL : 0 < L) :
    0 < blockLength X j L := by
  unfold blockLength
  exact mul_pos (by exact_mod_cast N.pos)
    (sub_pos.mpr (cyclicLift_strictMono X (by omega)))

/-- **Exponential upper tail**, part of Lemma 4.2.
In fact the bound holds for every real threshold. -/
theorem blockLength_upper_tail (hPL : External.PrekopaLeindler) (P : Parameters)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (j : ℤ) (L : ℕ) (hL : 0 < L) (u : ℝ) :
    (gibbsMeasure P N).real {X | (L : ℝ) * u < blockLength X j L} ≤
      3 * Real.exp (-blockMomentExponent * u) := by
  have := (modelWellDefined P N).2.2
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  obtain ⟨hi, hb⟩ := blockLength_exp_moment hPL P N hN j L hL
  have ht := tail_le_of_exp_moment_le blockMomentExponent_pos
    (fun X : Configuration N => blockLength X j L / L)
    ((measurable_blockLength j L).div_const _)
    (fun X => div_nonneg (blockLength_pos X j hL).le hLr.le) hi hb u
  have he : {X : Configuration N | u < blockLength X j L / L} =
      {X | (L : ℝ) * u < blockLength X j L} := by
    ext X
    simp only [mem_ofPred_eq, lt_div_iff₀ hLr, mul_comm u (L : ℝ)]
  rwa [he] at ht

/-- **Numerical polynomial moments**, part of Lemma 4.2.
The constant is chosen before all model parameters and block indices. -/
theorem blockLength_moments (p : ℝ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (P : Parameters)
      (N : ℕ+) (_hN : 2 ≤ (N : ℕ)) (j : ℤ) (L : ℕ), 0 < L →
      Integrable (fun X : Configuration N => blockLength X j L ^ p) (gibbsMeasure P N) ∧
      (∫⁻ X : Configuration N, ENNReal.ofReal (blockLength X j L ^ p) ∂gibbsMeasure P N) ≤
        ENNReal.ofReal (C * (L : ℝ) ^ p) := by
  let C : ℝ := 3 * (p / Real.exp 1) ^ p / blockMomentExponent ^ p
  have hC : 0 < C :=
    div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (div_pos hp (Real.exp_pos 1)) p))
      (Real.rpow_pos_of_pos blockMomentExponent_pos p)
  refine ⟨C, hC, ?_⟩
  intro hPL P N hN j L hL
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  obtain ⟨hi, hb⟩ := blockLength_exp_moment hPL P N hN j L hL
  obtain ⟨hm, hmb⟩ := moment_le_of_exp_moment_le blockMomentExponent_pos
    (fun X : Configuration N => blockLength X j L / L)
    ((measurable_blockLength j L).div_const _)
    (fun X => div_nonneg (blockLength_pos X j hL).le hLr.le) hi hb p hp
  have hscale (X : Configuration N) : blockLength X j L ^ p =
      (L : ℝ) ^ p * (blockLength X j L / L) ^ p := by
    rw [Real.div_rpow (blockLength_pos X j hL).le hLr.le]
    exact (mul_div_cancel₀ _ (Real.rpow_pos_of_pos hLr p).ne').symm
  have hmi : Integrable (fun X : Configuration N => blockLength X j L ^ p)
      (gibbsMeasure P N) := by
    simp_rw [hscale]
    exact hm.const_mul _
  refine ⟨hmi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hmi
    (ae_of_all _ fun X => Real.rpow_nonneg (blockLength_pos X j hL).le p)]
  apply ENNReal.ofReal_le_ofReal
  calc (∫ X : Configuration N, blockLength X j L ^ p ∂gibbsMeasure P N)
      = (L : ℝ) ^ p * ∫ X : Configuration N, (blockLength X j L / L) ^ p
          ∂gibbsMeasure P N := by simp_rw [hscale]; rw [integral_const_mul]
    _ ≤ (L : ℝ) ^ p * C :=
      mul_le_mul_of_nonneg_left hmb (Real.rpow_nonneg hLr.le p)
    _ = C * (L : ℝ) ^ p := mul_comm _ _

/-- The exponential estimate as a nonnegative integral, with no totalized-integral ambiguity. -/
theorem blockLength_exp_lintegral_le (hPL : External.PrekopaLeindler) (P : Parameters)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (j : ℤ) (L : ℕ) (hL : 0 < L) :
    (∫⁻ X : Configuration N, ENNReal.ofReal
      (Real.exp (blockMomentExponent * (blockLength X j L / L))) ∂gibbsMeasure P N) ≤ 3 := by
  obtain ⟨hi, hb⟩ := blockLength_exp_moment hPL P N hN j L hL
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  exact_mod_cast ENNReal.ofReal_le_ofReal hb

end Riesz1

end
end
