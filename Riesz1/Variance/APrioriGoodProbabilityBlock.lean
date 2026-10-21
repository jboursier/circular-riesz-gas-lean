/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodProbabilityPairs
public import Riesz1.Rigidity.BlockMoments
public import Riesz1.ToMathlib.Packing.ProbabilityTail

/-!
# Deviation of one block from its lattice value

This is a step in the proof of Lemma 5.2. For a block of `L` gaps with `1 ≤ L ≤ 4 K^γ`, the
event that the block length deviates from `L` by more than `K^ε L^{s/2} / 2` has probability
at most `(C + 3) exp(-θ K^e)`, for every `K` with `8 ≤ K^{ε/2}`. Here `θ = min(c,
blockMomentExponent / 2)` and `e = ε δ / (8 (s + 2))`.

Write `Q = K^{ε/2}`, so that `K^ε = Q²`.

* Large block, `Q ≤ L` (`block_large_prob`): the deviation exceeds `L^{s/2+δ}`, because
  `L^δ ≤ 4 K^{γδ} ≤ 4 Q`. The rigidity bound at the label of the start then applies.
* Small block, `L < Q` (`block_small_prob`): the lower deviation is impossible, since the block
  length is positive and the threshold is at least `L`. The upper deviation has the tail bound of
  `blockLength_upper_tail` at the shift `u = 1 + thr / L ≥ 1 + Q / 2`.

The rigidity hypothesis enters only through the bound `hgap`, the rigidity conclusion at the
fixed exponent `δ` with numbers `c` and `C`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

namespace APrioriProb

/-- For every `ε > 0` there is a threshold `K1 ≥ 1` such that `8 ≤ K^{ε/2}` for all `K ≥ K1`. -/
theorem exists_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ K1 : ℝ, 1 ≤ K1 ∧ ∀ K : ℝ, K1 ≤ K → 8 ≤ K ^ (ε / 2) := by
  have ht := tendsto_rpow_atTop (show (0 : ℝ) < ε / 2 by positivity)
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.1 (ht.eventually_ge_atTop 8)
  exact ⟨max K0 1, le_max_right _ _, fun K hK => hK0 K ((le_max_left _ _).trans hK)⟩

/-- The exponent identity `(ε/2) (δ/(4(s+2))) = ε δ/(8(s+2))`. -/
theorem exponent_identity (ε δ s : ℝ) :
    ε / 2 * (δ / (4 * (s + 2))) = ε * δ / (8 * (s + 2)) := by
  rw [div_mul_div_comm]
  congr 1
  ring

/-- **Large blocks.** If `K^{ε/2} ≤ L`, then the deviation of the block of `L` gaps beyond
`K^ε L^{s/2} / 2` has probability at most `C exp(-c L^{δ/(4(s+2))})`, by the rigidity bound at the
exponent `δ`. -/
theorem block_large_prob (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (γ ε δ c C : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hγδ : γ * δ ≤ ε / 2)
    (hgap : ∀ (N : ℕ+) (i : Fin (N : ℕ)) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
      gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N {X |
        |(N : ℝ) * (cyclicLift X ((i.val : ℤ) + k) - cyclicLift X i.val) - k| ≥
          (k : ℝ) ^ (s / 2 + δ)} ≤
        ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (δ / (4 * (s + 2))))))
    (K : ℝ) (hK : 1 ≤ K) (hQ : 8 ≤ K ^ (ε / 2))
    (N : ℕ+) (j : ℤ) (L : ℕ) (hL : 1 ≤ L) (hLK : (L : ℝ) ≤ 4 * K ^ γ)
    (hLN : L ≤ (N : ℕ) / 2) (hbig : K ^ (ε / 2) ≤ (L : ℝ)) :
    gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N
        {X | K ^ ε * (L : ℝ) ^ (s / 2) / 2 < |blockLength X j L - L|} ≤
      ENNReal.ofReal (C * Real.exp (-c * (L : ℝ) ^ (δ / (4 * (s + 2))))) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hK0 : 0 < K := by linarith
  have hLs0 : 0 ≤ (L : ℝ) ^ (s / 2) := Real.rpow_nonneg hLpos.le _
  have hKe : K ^ ε = K ^ (ε / 2) * K ^ (ε / 2) := by
    rw [← Real.rpow_add hK0]
    congr 1
    ring
  have h4δ : (4 : ℝ) ^ δ ≤ 4 := by
    calc (4 : ℝ) ^ δ ≤ (4 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
      _ = 4 := Real.rpow_one 4
  have hδL : (L : ℝ) ^ δ ≤ 4 * K ^ (ε / 2) := by
    calc (L : ℝ) ^ δ ≤ (4 * K ^ γ) ^ δ := Real.rpow_le_rpow hLpos.le hLK hδ0.le
      _ = (4 : ℝ) ^ δ * K ^ (γ * δ) := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hK0.le γ), ← Real.rpow_mul hK0.le]
      _ ≤ 4 * K ^ (ε / 2) :=
          mul_le_mul h4δ (Real.rpow_le_rpow_of_exponent_le hK hγδ)
            (Real.rpow_nonneg hK0.le _) (by norm_num)
  have hthr_big : (L : ℝ) ^ (s / 2 + δ) ≤ K ^ ε * (L : ℝ) ^ (s / 2) / 2 := by
    rw [Real.rpow_add hLpos, hKe]
    have key : 0 ≤ (L : ℝ) ^ (s / 2) * K ^ (ε / 2) * (K ^ (ε / 2) / 2 - 4) :=
      mul_nonneg (mul_nonneg hLs0 (Real.rpow_nonneg hK0.le _)) (by linarith)
    have hm := mul_le_mul_of_nonneg_left hδL hLs0
    linarith
  have hsub : {X : Configuration N | K ^ ε * (L : ℝ) ^ (s / 2) / 2 < |blockLength X j L - L|} ⊆
      {X : Configuration N | |(N : ℝ) * (cyclicLift X (((labelOf N j : ℕ) : ℤ) + L) -
        cyclicLift X ((labelOf N j : ℕ) : ℤ)) - L| ≥ (L : ℝ) ^ (s / 2 + δ)} := by
    intro X hX
    change K ^ ε * (L : ℝ) ^ (s / 2) / 2 < |blockLength X j L - L| at hX
    rw [blockLength_eq_labelOf X j L] at hX
    exact hthr_big.trans hX.le
  calc gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N
        {X | K ^ ε * (L : ℝ) ^ (s / 2) / 2 < |blockLength X j L - L|}
      ≤ gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N
        {X : Configuration N | |(N : ℝ) * (cyclicLift X (((labelOf N j : ℕ) : ℤ) + L) -
          cyclicLift X ((labelOf N j : ℕ) : ℤ)) - L| ≥ (L : ℝ) ^ (s / 2 + δ)} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (C * Real.exp (-c * (L : ℝ) ^ (δ / (4 * (s + 2))))) :=
        hgap N (labelOf N j) L hL hLN

/-- **Small blocks.** If `L < K^{ε/2}` and `8 ≤ K^{ε/2}`, then the deviation of the block of `L`
gaps beyond `K^ε L^{s/2} / 2` has probability at most `3 exp(-(m/2) K^{ε/2})`, where
`m = blockMomentExponent`. -/
theorem block_small_prob (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (ε : ℝ) (hPL : External.PrekopaLeindler) (K : ℝ) (hK : 1 ≤ K)
    (hQ : 8 ≤ K ^ (ε / 2)) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (j : ℤ) (L : ℕ) (hL : 1 ≤ L)
    (hbig : (L : ℝ) < K ^ (ε / 2)) :
    gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N
        {X | K ^ ε * (L : ℝ) ^ (s / 2) / 2 < |blockLength X j L - L|} ≤
      ENNReal.ofReal (3 * Real.exp (-(blockMomentExponent / 2) * K ^ (ε / 2))) := by
  have : IsProbabilityMeasure (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) :=
    (modelWellDefined _ N).2.2
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hLne : (L : ℝ) ≠ 0 := hLpos.ne'
  have hK0 : 0 < K := by linarith
  have hLs0 : 0 ≤ (L : ℝ) ^ (s / 2) := Real.rpow_nonneg hLpos.le _
  have hLs1 : 1 ≤ (L : ℝ) ^ (s / 2) := Real.one_le_rpow hL1 (by linarith)
  have hKe : K ^ ε = K ^ (ε / 2) * K ^ (ε / 2) := by
    rw [← Real.rpow_add hK0]
    congr 1
    ring
  have hm0 : 0 < blockMomentExponent := blockMomentExponent_pos
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = K ^ (ε / 2) := ⟨_, rfl⟩
  rw [← hQdef] at hKe hQ hbig ⊢
  have hQ0 : 0 ≤ Q := by linarith
  have hLQ : (L : ℝ) ≤ Q := hbig.le
  obtain ⟨thr, hthr⟩ : ∃ t : ℝ, t = K ^ ε * (L : ℝ) ^ (s / 2) / 2 := ⟨_, rfl⟩
  rw [← hthr]
  have hthr_eq : thr = Q * Q * (L : ℝ) ^ (s / 2) / 2 := by rw [hthr, hKe]
  have hsplit : (L : ℝ) ^ (s / 2) * (L : ℝ) ^ (1 - s / 2) = L := by
    rw [← Real.rpow_add hLpos, show s / 2 + (1 - s / 2) = (1 : ℝ) by ring, Real.rpow_one]
  have hLe : (L : ℝ) ^ (1 - s / 2) ≤ L := by
    calc (L : ℝ) ^ (1 - s / 2) ≤ (L : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = L := Real.rpow_one _
  -- The threshold dominates the block length: the lower deviation is impossible.
  have hthrL : (L : ℝ) ≤ thr := by
    have h1 : (L : ℝ) ≤ (L : ℝ) ^ (s / 2) * Q := by
      calc (L : ℝ) = (L : ℝ) ^ (s / 2) * (L : ℝ) ^ (1 - s / 2) := hsplit.symm
        _ ≤ (L : ℝ) ^ (s / 2) * Q := mul_le_mul_of_nonneg_left (hLe.trans hLQ) hLs0
    have key : 0 ≤ (L : ℝ) ^ (s / 2) * Q * (Q / 2 - 1) :=
      mul_nonneg (mul_nonneg hLs0 hQ0) (by linarith)
    rw [hthr_eq]
    linarith
  have hsub : {X : Configuration N | thr < |blockLength X j L - L|} ⊆
      {X : Configuration N | (L : ℝ) * (1 + thr / L) < blockLength X j L} := by
    intro X hX
    change thr < |blockLength X j L - L| at hX
    have hS : 0 < blockLength X j L := blockLength_pos X j (by omega)
    change (L : ℝ) * (1 + thr / L) < blockLength X j L
    have hLu : (L : ℝ) * (1 + thr / L) = L + thr := by
      field_simp
    rw [hLu]
    rcases lt_abs.1 hX with h | h
    · linarith
    · linarith
  have hup := blockLength_upper_tail hPL (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N hN j L
    (by omega) (1 + thr / L)
  -- The shift is at least `Q / 2`.
  have hthr_L : Q / 2 ≤ thr / L := by
    have hQLs : Q ≤ Q * (L : ℝ) ^ (s / 2) := le_mul_of_one_le_right hQ0 hLs1
    rw [le_div_iff₀ hLpos, hthr_eq]
    have key : 0 ≤ Q * (Q * (L : ℝ) ^ (s / 2) - L) := mul_nonneg hQ0 (by linarith)
    linarith
  have hm_exp : Real.exp (-blockMomentExponent * (1 + thr / L)) ≤
      Real.exp (-(blockMomentExponent / 2) * Q) := by
    apply Real.exp_le_exp.2
    have h2 := mul_le_mul_of_nonneg_left hthr_L hm0.le
    linarith
  calc gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N {X | thr < |blockLength X j L - L|}
      ≤ gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N
        {X | (L : ℝ) * (1 + thr / L) < blockLength X j L} := measure_mono hsub
    _ ≤ ENNReal.ofReal (3 * Real.exp (-blockMomentExponent * (1 + thr / L))) :=
        measure_le_ofReal_of_real_le _ _ hup
    _ ≤ ENNReal.ofReal (3 * Real.exp (-(blockMomentExponent / 2) * Q)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hm_exp (by norm_num))

/-- **Block deviation.** Let `θ, e` satisfy `θ = min(c, blockMomentExponent / 2)` and
`e = ε δ / (8 (s + 2))`. Assume `0 ≤ γ`, `ε > 0`, `0 < δ ≤ 1`, `γ δ ≤ ε / 2`, `c, C > 0`, and
the rigidity bound `hgap` at the exponent `δ`. Then for `K ≥ 1` with `8 ≤ K^{ε/2}`, `N ≥ 2`,
`j ∈ ℤ`, and `1 ≤ L ≤ min(4 K^γ, N / 2)`, the block deviation exceeds `K^ε L^{s/2} / 2` with
probability at most `(C + 3) exp(-θ K^e)`. -/
theorem block_dev_prob_le (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (γ ε δ c C θ e : ℝ) (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hγδ : γ * δ ≤ ε / 2) (hc : 0 < c) (hC : 0 < C)
    (hθ : θ = min c (blockMomentExponent / 2)) (he : e = ε * δ / (8 * (s + 2)))
    (hgap : ∀ (N : ℕ+) (i : Fin (N : ℕ)) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
      gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N {X |
        |(N : ℝ) * (cyclicLift X ((i.val : ℤ) + k) - cyclicLift X i.val) - k| ≥
          (k : ℝ) ^ (s / 2 + δ)} ≤
        ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (δ / (4 * (s + 2)))))) :
    ∀ (_hPL : External.PrekopaLeindler) (K : ℝ), 1 ≤ K → 8 ≤ K ^ (ε / 2) →
    ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (j : ℤ) (L : ℕ), 1 ≤ L → (L : ℝ) ≤ 4 * K ^ γ →
      L ≤ (N : ℕ) / 2 →
      gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N
          {X | K ^ ε * (L : ℝ) ^ (s / 2) / 2 < |blockLength X j L - L|} ≤
        ENNReal.ofReal ((C + 3) * Real.exp (-θ * K ^ e)) := by
  intro hPL K hK hQ N hN j L hL hLK hLN
  have hK0 : 0 < K := by linarith
  have hm0 : 0 < blockMomentExponent := blockMomentExponent_pos
  have hθ0 : 0 < θ := by
    rw [hθ]
    exact lt_min hc (by positivity)
  have hθc : θ ≤ c := by
    rw [hθ]
    exact min_le_left _ _
  have hθm : θ ≤ blockMomentExponent / 2 := by
    rw [hθ]
    exact min_le_right _ _
  have he_le : e ≤ ε / 2 := by
    rw [he, div_le_iff₀ (by positivity)]
    nlinarith
  have hKe0 : 0 ≤ K ^ e := Real.rpow_nonneg hK0.le e
  have hKe_le : K ^ e ≤ K ^ (ε / 2) := Real.rpow_le_rpow_of_exponent_le hK he_le
  have hE0 : 0 < Real.exp (-θ * K ^ e) := Real.exp_pos _
  have hexp_id : K ^ e = (K ^ (ε / 2)) ^ (δ / (4 * (s + 2))) := by
    rw [← Real.rpow_mul hK0.le, exponent_identity, he]
  rcases le_or_gt (K ^ (ε / 2)) (L : ℝ) with hbig | hsmall
  · have hLp : K ^ e ≤ (L : ℝ) ^ (δ / (4 * (s + 2))) := by
      rw [hexp_id]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hK0.le _) hbig (by positivity)
    refine (block_large_prob beta s hbeta hs hs1 γ ε δ c C hδ0 hδ1 hγδ hgap K hK hQ N j L
      hL hLK hLN hbig).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : Real.exp (-c * (L : ℝ) ^ (δ / (4 * (s + 2)))) ≤ Real.exp (-θ * K ^ e) := by
      apply Real.exp_le_exp.2
      have h2 : c * K ^ e ≤ c * (L : ℝ) ^ (δ / (4 * (s + 2))) :=
        mul_le_mul_of_nonneg_left hLp hc.le
      have h3 : θ * K ^ e ≤ c * K ^ e := mul_le_mul_of_nonneg_right hθc hKe0
      rw [neg_mul, neg_mul]
      linarith
    have h4 := mul_le_mul_of_nonneg_left h1 hC.le
    have h5 : (C + 3) * Real.exp (-θ * K ^ e) =
        C * Real.exp (-θ * K ^ e) + 3 * Real.exp (-θ * K ^ e) := by ring
    have h6 : 0 ≤ 3 * Real.exp (-θ * K ^ e) := by positivity
    linarith
  · refine (block_small_prob beta s hbeta hs hs1 ε hPL K hK hQ N hN j L hL hsmall).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have h1 : Real.exp (-(blockMomentExponent / 2) * K ^ (ε / 2)) ≤ Real.exp (-θ * K ^ e) := by
      apply Real.exp_le_exp.2
      have h2 : θ * K ^ e ≤ (blockMomentExponent / 2) * K ^ e :=
        mul_le_mul_of_nonneg_right hθm hKe0
      have h3 : (blockMomentExponent / 2) * K ^ e ≤ (blockMomentExponent / 2) * K ^ (ε / 2) :=
        mul_le_mul_of_nonneg_left hKe_le (by positivity)
      rw [neg_mul, neg_mul]
      linarith
    have h4 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3)
    have h5 : (C + 3) * Real.exp (-θ * K ^ e) =
        C * Real.exp (-θ * K ^ e) + 3 * Real.exp (-θ * K ^ e) := by ring
    have h6 : 0 ≤ C * Real.exp (-θ * K ^ e) := by positivity
    linarith

end APrioriProb

end Riesz1

end
end
