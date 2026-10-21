/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodProbabilityGap
public import Riesz1.Variance.APrioriGoodProbabilityBlock
public import Riesz1.Variance.APrioriGoodProbabilityPairs
public import Riesz1.Auxiliary.RigidityConclusion
public import Riesz1.ToMathlib.Moments.Decay

/-!
# The probability estimate of the good-event cutoff

Part of Lemma 5.2 (the good-event part), probability claim: for every `B > 0` there is `C > 0`
such that `P(η_{ε,γ} ≠ 1) ≤ C K^{-B}` for all `N ≥ 2` and `1 ≤ K ≤ N`.

The rigidity hypothesis is `Riesz1.Internal.RigidityConclusion`. The Prékopa–Leindler inequality
`External.PrekopaLeindler` is an explicit hypothesis, as in the rigidity lemmas.

The proof is a union bound over the failure events of `exists_failure_of_goodCutoff_ne_one`:

* a pair `(i, k)` of the window fails when its block deviation exceeds `K^ε |k|^{s/2} / 2`. There
  are at most `72 K^{2γ}` pairs, each with a block of length `|k| ≤ 4 K^γ`
  (`APrioriProb.natAbs_le_of_mem_cutoffPairs`), and each fails with probability at most
  `(C + 3) exp(-θ K^e)` (`APrioriProb.block_dev_prob_le`).
* a nearest-neighbour gap exceeds `K^ε / 2`, with probability at most `3 exp(-m K^ε/2)`.
* a nearest-neighbour gap lies below `2 K^{-ε}`, with probability at most `C_p (2 K^{-ε})^p`,
  where `p ε = B + γ + 1`.

There are at most `8 K^γ` nearest pairs. The sum of the bounds is at most `C K^{-B}` for
`K ≥ K1`, where `K1` is the threshold of `APrioriProb.exists_threshold`. For `K < K1` the bound
`1 ≤ C K^{-B}` holds with `C ≥ K1^B`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

namespace APrioriProb

/-- **Event of one pair.** For `K > 0` and a pair `(i, k)` with `k ≠ 0`, the failure event of the
pair is contained in the block deviation event of the block of length `|k|` starting at
`i + min(k, 0)`. -/
theorem pair_event_subset (N : ℕ+) (s K ε : ℝ) (hK : 0 < K) (i : Fin (N : ℕ)) (k : ℤ)
    (hk : k ≠ 0) :
    {X : Configuration N | 1 < 2 * |pairDev N X (i, k)| / pairScale s K ε (i, k)} ⊆
      {X : Configuration N | K ^ ε * ((k.natAbs : ℕ) : ℝ) ^ (s / 2) / 2 <
        |blockLength X (((i : ℕ) : ℤ) + min k 0) k.natAbs - ((k.natAbs : ℕ) : ℝ)|} := by
  intro X hX
  change 1 < 2 * |pairDev N X (i, k)| / pairScale s K ε (i, k) at hX
  have hnat : 1 ≤ k.natAbs := Int.natAbs_pos.2 hk
  have hnatR : (1 : ℝ) ≤ ((k.natAbs : ℕ) : ℝ) := by exact_mod_cast hnat
  have hσ : 0 < K ^ ε * ((k.natAbs : ℕ) : ℝ) ^ (s / 2) :=
    mul_pos (Real.rpow_pos_of_pos hK ε) (Real.rpow_pos_of_pos (by linarith) _)
  have hσ' : pairScale s K ε (i, k) = K ^ ε * ((k.natAbs : ℕ) : ℝ) ^ (s / 2) := rfl
  rw [hσ', one_lt_div hσ, abs_pairDev_eq X i k hk] at hX
  change K ^ ε * ((k.natAbs : ℕ) : ℝ) ^ (s / 2) / 2 <
    |blockLength X (((i : ℕ) : ℤ) + min k 0) k.natAbs - ((k.natAbs : ℕ) : ℝ)|
  linarith

/-- **Probability of one pair.** Under the hypotheses of `block_dev_prob_le`, every cutoff pair
`(i, k)` of the window fails with probability at most `(C + 3) exp(-θ K^e)`. -/
theorem pair_prob_le (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (γ ε δ c C θ e : ℝ) (hγ : 0 ≤ γ) (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hγδ : γ * δ ≤ ε / 2) (hc : 0 < c) (hC : 0 < C)
    (hθ : θ = min c (blockMomentExponent / 2)) (he : e = ε * δ / (8 * (s + 2)))
    (hgap : ∀ (N : ℕ+) (i : Fin (N : ℕ)) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
      gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N {X |
        |(N : ℝ) * (cyclicLift X ((i.val : ℤ) + k) - cyclicLift X i.val) - k| ≥
          (k : ℝ) ^ (s / 2 + δ)} ≤
        ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (δ / (4 * (s + 2))))))
    (hPL : External.PrekopaLeindler) (K : ℝ) (hK : 1 ≤ K) (hQ : 8 ≤ K ^ (ε / 2))
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i : Fin (N : ℕ)) (k : ℤ)
    (hmem : (i, k) ∈ cutoffPairs N (window N K γ)) :
    gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N
        {X | 1 < 2 * |pairDev N X (i, k)| / pairScale s K ε (i, k)} ≤
      ENNReal.ofReal ((C + 3) * Real.exp (-θ * K ^ e)) := by
  have hL4 : ((k.natAbs : ℕ) : ℝ) ≤ 4 * K ^ γ :=
    natAbs_le_of_mem_cutoffPairs K γ hK hγ hmem
  have hmem' := hmem
  rw [mem_cutoffPairs_iff] at hmem'
  obtain ⟨-, -, hk0, hk1, hk2⟩ := hmem'
  have hk0' : k ≠ 0 := hk0
  have hLN : k.natAbs ≤ (N : ℕ) / 2 := by omega
  have hL1 : 1 ≤ k.natAbs := Int.natAbs_pos.2 hk0'
  refine (measure_mono (pair_event_subset N s K ε (by linarith) i k hk0')).trans ?_
  exact block_dev_prob_le beta s hbeta hs hs1 γ ε δ c C θ e hε hδ0 hδ1 hγδ hc hC hθ he hgap
    hPL K hK hQ N hN (((i : ℕ) : ℤ) + min k 0) k.natAbs hL1 hL4 hLN

end APrioriProb

namespace Internal

open APrioriProb

/-- **Probability estimate of the good-event cutoff** (part of Lemma 5.2).
Conditionally on the rigidity conclusion at `(β, s)`, for every `B > 0` there is `C > 0`, such
that under the hypothesis `External.PrekopaLeindler`, for every `N ≥ 2` and every `1 ≤ K ≤ N`, the
Gibbs probability of `η_{ε,γ} ≠ 1` is at most `C K^{-B}`. -/
theorem goodCutoff_prob_le_of_rigidity (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hRig : Riesz1.Internal.RigidityConclusion beta s hbeta hs hs1)
    (γ ε : ℝ) (hγ : 1 < γ) (hε : 0 < ε) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ K : ℝ, 1 ≤ K → K ≤ (N : ℕ) →
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
  -- Coefficients: `Cmain` is the coefficient of `K^{-B}`, and `Cf` dominates it and `K1^B`.
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
  refine ⟨Cf, hCf0, fun hPL N hN K hK hKN => ?_⟩
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

end Internal

end Riesz1

end
end
