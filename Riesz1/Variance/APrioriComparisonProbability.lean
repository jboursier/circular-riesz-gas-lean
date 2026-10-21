/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriCutoffProbability
public import Riesz1.Variance.APrioriGoodProbabilityGap
public import Riesz1.Variance.APrioriGoodProbabilityBlock
public import Riesz1.Variance.APrioriGoodProbabilityPairs
public import Riesz1.Auxiliary.RigidityConclusion
public import Riesz1.ToMathlib.Moments.Decay

/-!
# Cutoff probabilities at arbitrary scales

The union bound uses the number and lengths of selected pairs, each
bounded by a power of the scale. It therefore holds for every scale at
least one, including scales greater than the particle number.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Riesz1.APrioriProb

namespace Riesz1.APrioriComparison

theorem comparison_cutoff_probability_gibbs (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hRig : Riesz1.Internal.RigidityConclusion beta s hbeta hs hs1)
    (γ ε : ℝ) (hγ : 1 < γ) (hε : 0 < ε) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ K : ℝ, 1 ≤ K →
        gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N
            {X | goodCutoff N s K γ ε X ≠ 1} ≤
          ENNReal.ofReal (C * K ^ (-B)) := by
  obtain ⟨eps0, heps0, hbound⟩ := hRig
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min (min (ε / (2 * γ)) (eps0 / 2)) 1 := ⟨_, rfl⟩
  have hγ0 : 0 < γ := by linarith
  have hδ0 : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min (by positivity) (by positivity)) one_pos
  have hδ1 : δ ≤ 1 := by
    rw [hδdef]
    exact min_le_right _ _
  have hδlt : δ < eps0 := by
    have h1 : δ ≤ eps0 / 2 := by
      rw [hδdef]
      exact (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hγδ : γ * δ ≤ ε / 2 := by
    have h1 : δ ≤ ε / (2 * γ) := by
      rw [hδdef]
      exact (min_le_left _ _).trans (min_le_left _ _)
    have h2 : γ * δ ≤ γ * (ε / (2 * γ)) := mul_le_mul_of_nonneg_left h1 hγ0.le
    have h3 : γ * (ε / (2 * γ)) = ε / 2 := by
      field_simp
    linarith
  obtain ⟨c, C, hc, hC, hgap0⟩ := hbound δ hδ0 hδlt
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = min c (blockMomentExponent / 2) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = ε * δ / (8 * (s + 2)) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by
    rw [hθ]
    exact lt_min hc (by have := blockMomentExponent_pos; positivity)
  have hθm : θ ≤ blockMomentExponent / 2 := by
    rw [hθ]
    exact min_le_right _ _
  have he0 : 0 < e := by
    rw [he]
    positivity
  have he_le : e ≤ ε := by
    rw [he, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨K1, hK1, hK1prop⟩ := APrioriProb.exists_threshold ε hε
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (B + γ + 1) / ε := ⟨_, rfl⟩
  have hp0 : 0 < p := by
    rw [hp]
    positivity
  have hεp : ε * p = B + γ + 1 := by
    rw [hp]
    field_simp
  obtain ⟨Cp, hCp0, hCp⟩ := no_explosion_uniform (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) hp0
  obtain ⟨Kb, hKb0, hKb⟩ := rpow_mul_exp_neg_bounded (β := 2 * γ + B) (a := e) (c := θ) he0 hθ0
  have hCmain : 0 < 80 * (C + 3) * Kb + 8 * Cp * (2 : ℝ) ^ p := by
    have h1 : 0 ≤ 80 * (C + 3) * Kb :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hKb0
    have h2 : 0 < 8 * Cp * (2 : ℝ) ^ p :=
      mul_pos (mul_pos (by norm_num) hCp0) (Real.rpow_pos_of_pos (by norm_num) p)
    linarith
  obtain ⟨Cf, hCfdef⟩ : ∃ Cf : ℝ, Cf = max (80 * (C + 3) * Kb + 8 * Cp * (2 : ℝ) ^ p) (K1 ^ B) :=
    ⟨_, rfl⟩
  have hCf_main : 80 * (C + 3) * Kb + 8 * Cp * (2 : ℝ) ^ p ≤ Cf := by
    rw [hCfdef]
    exact le_max_left _ _
  have hCf_K1 : K1 ^ B ≤ Cf := by
    rw [hCfdef]
    exact le_max_right _ _
  have hCf0 : 0 < Cf := lt_of_lt_of_le hCmain hCf_main
  refine ⟨Cf, hCf0, fun hPL N hN K hK => ?_⟩
  have : IsProbabilityMeasure (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) :=
    (modelWellDefined _ N).2.2
  have hK0 : 0 < K := by linarith
  by_cases hKK1 : K1 ≤ K
  · -- The main case `K ≥ K1`: the union bound.
    have hQ : 8 ≤ K ^ (ε / 2) := hK1prop K hKK1
    have hA0 : 0 ≤ (C + 3) * Real.exp (-θ * K ^ e) :=
      mul_nonneg (by linarith) (Real.exp_pos _).le
    have hsub : {X : Configuration N | goodCutoff N s K γ ε X ≠ 1} ⊆
        ((⋃ p ∈ cutoffPairs N (window N K γ),
            {X : Configuration N | 1 < 2 * |pairDev N X p| / pairScale s K ε p}) ∪
          ⋃ i ∈ nearestPairs N (window N K γ),
            {X : Configuration N | 1 < 2 * gap X ((i : ℕ) : ℤ) / K ^ ε}) ∪
        ⋃ i ∈ nearestPairs N (window N K γ),
          {X : Configuration N | 1 < 2 / (K ^ ε * gap X ((i : ℕ) : ℤ))} := by
      intro X hX
      rcases exists_failure_of_goodCutoff_ne_one N s K γ ε X hX with
        ⟨p, hp', h⟩ | ⟨i, hi, h⟩ | ⟨i, hi, h⟩
      · exact Or.inl (Or.inl (Set.mem_iUnion₂.2 ⟨p, hp', h⟩))
      · exact Or.inl (Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, h⟩))
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, h⟩)
    have hE : ∑ p ∈ cutoffPairs N (window N K γ),
        gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N
          {X : Configuration N | 1 < 2 * |pairDev N X p| / pairScale s K ε p} ≤
        ENNReal.ofReal (72 * K ^ (2 * γ) * ((C + 3) * Real.exp (-θ * K ^ e))) :=
      sum_measure_le_ofReal_of_card_le _ _ _ hA0 (card_cutoffPairs_le K γ hK (by linarith))
        (fun p hp' => pair_prob_le beta s hbeta hs hs1 γ ε δ c C θ e (by linarith) hε hδ0 hδ1
          hγδ hc hC hθ he (fun N' => (hgap0 N').1) hPL K hK hQ N hN p.1 p.2 hp')
    have hF : ∑ i ∈ nearestPairs N (window N K γ),
        gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N
          {X : Configuration N | 1 < 2 * gap X ((i : ℕ) : ℤ) / K ^ ε} ≤
        ENNReal.ofReal (8 * K ^ γ * ((C + 3) * Real.exp (-θ * K ^ e))) :=
      sum_measure_le_ofReal_of_card_le _ _ _ hA0 (card_nearestPairs_window_le hK (by linarith))
        (fun i _ => (nearest_upper_prob (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) hPL N hN
          ((i : ℕ) : ℤ) hK0).trans (ENNReal.ofReal_le_ofReal
            (exp_upper_le hK he_le hθm hC.le)))
    have hG : ∑ i ∈ nearestPairs N (window N K γ),
        gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N
          {X : Configuration N | 1 < 2 / (K ^ ε * gap X ((i : ℕ) : ℤ))} ≤
        ENNReal.ofReal (8 * K ^ γ * (Cp * (2 / K ^ ε) ^ p)) :=
      sum_measure_le_ofReal_of_card_le _ _ _
        (mul_nonneg hCp0.le (Real.rpow_nonneg (div_nonneg two_pos.le
          (Real.rpow_pos_of_pos hK0 ε).le) p))
        (card_nearestPairs_window_le hK (by linarith))
        (fun i _ => by
          obtain ⟨_, hint⟩ := hCp hPL N ((i : ℕ) : ℤ)
          exact nearest_lower_prob (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N
            ((i : ℕ) : ℤ) hK0 hp0 hint)
    have hnn1 : 0 ≤ 72 * K ^ (2 * γ) * ((C + 3) * Real.exp (-θ * K ^ e)) :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hK0.le _)) hA0
    have hnn2 : 0 ≤ 8 * K ^ γ * ((C + 3) * Real.exp (-θ * K ^ e)) :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hK0.le _)) hA0
    have hnn3 : 0 ≤ 8 * K ^ γ * (Cp * (2 / K ^ ε) ^ p) :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hK0.le _))
        (mul_nonneg hCp0.le (Real.rpow_nonneg (div_nonneg two_pos.le
          (Real.rpow_pos_of_pos hK0 ε).le) p))
    have hR := sum_real_le (K := K) (γ := γ) (ε := ε) (B := B) (p := p) (Cp := Cp) (C := C)
      (θ := θ) (e := e) (Kb := Kb) hK (by linarith) hCp0.le hC.le hεp (hKb K hK)
    have hY : 0 ≤ K ^ (-B) := Real.rpow_nonneg hK0.le _
    refine (measure_mono hsub).trans ?_
    refine ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)).trans ?_
    refine (add_le_add (add_le_add (measure_biUnion_finset_le _ _)
      (measure_biUnion_finset_le _ _)) (measure_biUnion_finset_le _ _)).trans ?_
    refine (add_le_add (add_le_add hE hF) hG).trans ?_
    rw [← ENNReal.ofReal_add hnn1 hnn2, ← ENNReal.ofReal_add (add_nonneg hnn1 hnn2) hnn3]
    exact ENNReal.ofReal_le_ofReal (hR.trans (mul_le_mul_of_nonneg_right hCf_main hY))
  · -- The case `K < K1`: the trivial bound by one, with `C ≥ K1^B ≥ K^B`.
    have hKK1' : K < K1 := not_le.1 hKK1
    have hKB : 0 < K ^ B := Real.rpow_pos_of_pos hK0 B
    have hKB1 : K ^ B ≤ K1 ^ B := Real.rpow_le_rpow hK0.le hKK1'.le hB.le
    have h1 : (1 : ℝ) ≤ Cf * K ^ (-B) := by
      rw [Real.rpow_neg hK0.le, ← div_eq_mul_inv, le_div_iff₀ hKB, one_mul]
      linarith
    refine le_trans prob_le_one ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal h1

/-- The same cutoff probability bound under the forced anchored law. -/
theorem comparison_cutoff_probability (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (P : Parameters) (γ ε : ℝ) (hγ : 1 < γ)
    (hε : 0 < ε) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (θ : ℝ → ℝ), IsForcingCutoff θ →
      ∀ K : ℝ, 1 ≤ K →
        nearestAnchoredLaw P θ N K γ ε {y | anchoredCutoff N P.val.2 K γ ε y ≠ 1} ≤
          ENNReal.ofReal (C * K ^ (-B)) := by
  obtain ⟨z, hz, hZ⟩ := nearestNormalizer_uniform hPL P γ ε (by linarith) hε
  obtain ⟨C, hC, hprob⟩ := comparison_cutoff_probability_gibbs P.val.1 P.val.2 P.2.1 P.2.2.1 P.2.2.2
    (Internal.rigidityConclusion_of_externals hBE hPL _ _ _ _ _) γ ε hγ hε B hB
  refine ⟨z⁻¹ * C, mul_pos (inv_pos.mpr hz) hC, fun N hN θ hθ K hK => ?_⟩
  have hset : MeasurableSet {y | anchoredCutoff N P.val.2 K γ ε y ≠ 1} :=
    (measurable_anchoredCutoff _ _ _ _) (measurableSet_singleton 1) |>.compl
  rw [nearestAnchoredLaw, Measure.map_apply (measurable_anchorMap N) hset]
  have hpre : anchorMap N ⁻¹' {y | anchoredCutoff N P.val.2 K γ ε y ≠ 1} =
      {X | goodCutoff N P.val.2 K γ ε X ≠ 1} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, anchoredCutoff_anchorMap]
  rw [hpre]
  calc nearestLaw P θ N K γ ε {X | goodCutoff N P.val.2 K γ ε X ≠ 1}
      ≤ (ENNReal.ofReal z⁻¹ • gibbsMeasure P N) {X | goodCutoff N P.val.2 K γ ε X ≠ 1} :=
        Measure.le_iff'.mp (Internal.nearestLaw_le_of_normalizer_lower P hθ (by linarith) hz
          (hZ N hN θ hθ K hK)) _
    _ ≤ ENNReal.ofReal z⁻¹ * ENNReal.ofReal (C * K ^ (-B)) := by
      rw [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul_right (hprob hPL N hN K hK) _
    _ = ENNReal.ofReal (z⁻¹ * C * K ^ (-B)) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hz.le), mul_assoc]


end Riesz1.APrioriComparison

end
