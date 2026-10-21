/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ReductionAverage
public import Riesz1.Rigidity.RigidityBlocks
public import Riesz1.Rigidity.RigidityGapsSplit

/-!
# Stronger gap estimate

Part of Theorem 1. Let `s = P.val.2 ∈ (0,1)`, `β = P.val.1 > 0`, and
`0 < ε < min(1, 1 - s/2)`. The constants `c, C` depend only on `s, β, ε`, and for every `N ≥ 2` and
`i ∈ ℤ`:

* for `1 ≤ k ≤ N/2`, `P(|S_{i,k} - k| ≥ k^{s/2+ε}) ≤ C exp(-c k^{ε/(2(s+2))})`.
* for `1 ≤ k < N`, the same bound holds with `k` on both sides replaced by `r = min(k, N-k)`.

The block length is `S_{i,k} = blockLength X i k`. The proof splits `S_{i,k} - k` into two
comparisons with block averages (Lemma 4.4, at scale `ε/2`) and the centered block
difference (`almost_optimal_rigidity_blocks`). The reflection of `blockLength_reflect` gives the
range `N/2 < k < N`. The Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler
inequality `External.PrekopaLeindler` enter as explicit hypotheses.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

/-- **Stronger gap estimate**, part of Theorem 1. The hypothesis
`ε < min(1, 1 - s/2)` is not used by the proof. The bounds hold for every `ε > 0`. -/
theorem almost_optimal_rigidity_gaps (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) {ε : ℝ} (hε : 0 < ε) (_hεs : ε < min 1 (1 - (parametersExponent P).val / 2)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ+) (_hN : 2 ≤ (N : ℕ)) (i : ℤ),
      (∀ k : ℕ, 1 ≤ k → 2 * k ≤ (N : ℕ) →
        (gibbsMeasure P N).real {X | (k : ℝ) ^ ((parametersExponent P).val / 2 + ε) ≤
            |blockLength X i k - k|} ≤
          C * Real.exp (-c * (k : ℝ) ^ (ε / (2 * ((parametersExponent P).val + 2))))) ∧
      (∀ k : ℕ, 1 ≤ k → k < (N : ℕ) →
        (gibbsMeasure P N).real {X | ((min k ((N : ℕ) - k) : ℕ) : ℝ) ^
            ((parametersExponent P).val / 2 + ε) ≤ |blockLength X i k - k|} ≤
          C * Real.exp (-c * ((min k ((N : ℕ) - k) : ℕ) : ℝ) ^
            (ε / (2 * ((parametersExponent P).val + 2))))) := by
  classical
  rw [show (parametersExponent P).val = P.val.2 from rfl]
  have hs : 0 < P.val.2 := P.property.2.1
  obtain ⟨c₁, C₁, hc₁, hC₁, hred⟩ := reduction_av hBE hPL P (half_pos hε)
  obtain ⟨c₂, C₂, hc₂, hC₂, hblk⟩ := almost_optimal_rigidity_blocks P hε
  rw [show (parametersExponent P).val = P.val.2 from rfl] at hred hblk
  set c : ℝ := min c₁ c₂ with hcdef
  have hc : 0 < c := lt_min hc₁ hc₂
  have hcc₁ : c ≤ c₁ := min_le_left _ _
  have hcc₂ : c ≤ c₂ := min_le_right _ _
  refine ⟨c, 2 * C₁ + C₂ + Real.exp (3 * c), hc, by linarith [Real.exp_pos (3 * c)], ?_⟩
  intro N hN i
  have := isProbabilityMeasure_gibbsMeasure P N
  -- The two-sided bound for `1 ≤ k ≤ N/2` and every label `j`.
  have key : ∀ (j : ℤ) (k : ℕ), 1 ≤ k → 2 * k ≤ (N : ℕ) →
      (gibbsMeasure P N).real {X | (k : ℝ) ^ (P.val.2 / 2 + ε) ≤ |blockLength X j k - k|} ≤
        (2 * C₁ + C₂ + Real.exp (3 * c)) * Real.exp (-c * (k : ℝ) ^ (ε / (2 * (P.val.2 + 2)))) := by
    intro j k hk hkN
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (0 : ℝ) < k := by linarith
    have hkN2 : k ≤ (N : ℕ) / 2 := by omega
    have hdiv : ε / 2 / (P.val.2 + 2) = ε / (2 * (P.val.2 + 2)) := div_div ε 2 _
    have hαk : 0 ≤ (k : ℝ) ^ (ε / (2 * (P.val.2 + 2))) := Real.rpow_nonneg hk0.le _
    have hαle : ε / (2 * (P.val.2 + 2)) ≤ ε / 2 :=
      div_le_div_of_nonneg_left hε.le (by norm_num) (by linarith)
    have hE : ∀ c' : ℝ, c ≤ c' →
        Real.exp (-c' * (k : ℝ) ^ (ε / (2 * (P.val.2 + 2)))) ≤
          Real.exp (-c * (k : ℝ) ^ (ε / (2 * (P.val.2 + 2)))) := by
      intro c' hc'
      refine Real.exp_le_exp.mpr ?_
      have := mul_le_mul_of_nonneg_right hc' hαk
      linarith
    by_cases hgood : (3 : ℝ) ≤ (k : ℝ) ^ (ε / 2)
    · -- Here the threshold `k^{s/2+ε}/3` dominates `k^{s/2+ε/2}`, so each of the three
      -- summands of equation (4.7) is controlled at the scale `ε/2`.
      have hT : (k : ℝ) ^ (P.val.2 / 2 + ε / 2) ≤ (k : ℝ) ^ (P.val.2 / 2 + ε) / 3 := by
        have hsplit : (k : ℝ) ^ (P.val.2 / 2 + ε) =
            (k : ℝ) ^ (P.val.2 / 2 + ε / 2) * (k : ℝ) ^ (ε / 2) := by
          rw [← Real.rpow_add hk0]
          congr 1
          ring
        rw [hsplit, le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
        exact mul_le_mul_of_nonneg_left hgood (Real.rpow_nonneg hk0.le _)
      have hA := hred N hN (j + k) hk hkN
      have hB := hred N hN j hk hkN
      have hC := hblk hBE hPL N hN j k hk hkN2
      rw [hdiv] at hA hB
      have hsub : {X : Configuration N | (k : ℝ) ^ (P.val.2 / 2 + ε) ≤ |blockLength X j k - k|} ⊆
          {X : Configuration N | (k : ℝ) ^ (P.val.2 / 2 + ε / 2) ≤
              |((N : ℕ) : ℝ) * (cyclicLift X (j + k) - blockAverage X (j + k) k)|} ∪
            ({X : Configuration N | (k : ℝ) ^ (P.val.2 / 2 + ε / 2) ≤
                |((N : ℕ) : ℝ) * (cyclicLift X j - blockAverage X j k)|} ∪
              {X : Configuration N | (k : ℝ) ^ (P.val.2 / 2 + ε) / 3 ≤
                |centeredBlockDiff X j k|}) := by
        intro X hX
        by_contra hcon
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hcon
        obtain ⟨h1, h2, h3⟩ := hcon
        have hX' : (k : ℝ) ^ (P.val.2 / 2 + ε) ≤ |blockLength X j k - k| := hX
        have hdec : blockLength X j k - k =
            ((N : ℕ) : ℝ) * (cyclicLift X (j + k) - blockAverage X (j + k) k) +
              -(((N : ℕ) : ℝ) * (cyclicLift X j - blockAverage X j k)) +
              centeredBlockDiff X j k := by
          rw [blockLength_sub_eq_split X j k]
          ring
        have htri := abs_add_three
          (((N : ℕ) : ℝ) * (cyclicLift X (j + k) - blockAverage X (j + k) k))
          (-(((N : ℕ) : ℝ) * (cyclicLift X j - blockAverage X j k)))
          (centeredBlockDiff X j k)
        rw [abs_neg] at htri
        rw [hdec] at hX'
        linarith
      have hmain := (measureReal_mono hsub (measure_ne_top (gibbsMeasure P N) _)).trans
        ((measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le _ _)))
      have hE1 := hE c₁ hcc₁
      have hE2 := hE c₂ hcc₂
      have hA' := mul_le_mul_of_nonneg_left hE1 hC₁.le
      have hB' := mul_le_mul_of_nonneg_left hE1 hC₁.le
      have hC' := mul_le_mul_of_nonneg_left hE2 hC₂.le
      have hpos : 0 ≤ Real.exp (3 * c) * Real.exp (-c * (k : ℝ) ^ (ε / (2 * (P.val.2 + 2)))) :=
        mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
      nlinarith [hmain, hA, hB, hC, hA', hB', hC', hpos]
    · -- For `k^{ε/2} < 3`, the claim is trivial once `C` absorbs `exp(3c)`.
      have hlt : (k : ℝ) ^ (ε / 2) < 3 := not_le.mp hgood
      have hkα : (k : ℝ) ^ (ε / (2 * (P.val.2 + 2))) ≤ 3 :=
        (Real.rpow_le_rpow_of_exponent_le hk1 hαle).trans hlt.le
      have hbound : 1 ≤ Real.exp (3 * c) *
          Real.exp (-c * (k : ℝ) ^ (ε / (2 * (P.val.2 + 2)))) := by
        rw [← Real.exp_add]
        refine Real.one_le_exp_iff.mpr ?_
        have := mul_le_mul_of_nonneg_left hkα hc.le
        linarith
      calc (gibbsMeasure P N).real
            {X : Configuration N | (k : ℝ) ^ (P.val.2 / 2 + ε) ≤ |blockLength X j k - k|}
          ≤ 1 := measureReal_le_one
        _ ≤ Real.exp (3 * c) * Real.exp (-c * (k : ℝ) ^ (ε / (2 * (P.val.2 + 2)))) := hbound
        _ ≤ (2 * C₁ + C₂ + Real.exp (3 * c)) *
              Real.exp (-c * (k : ℝ) ^ (ε / (2 * (P.val.2 + 2)))) :=
          mul_le_mul_of_nonneg_right (by linarith [hC₁, hC₂]) (Real.exp_pos _).le
  refine ⟨fun k hk hkN => key i k hk hkN, fun k hk hkNlt => ?_⟩
  rcases le_total (2 * k) (N : ℕ) with h2k | h2k
  · have hmin : min k ((N : ℕ) - k) = k := by omega
    rw [hmin]
    exact key i k hk h2k
  · -- For `N/2 < k < N`, reflect the block to the block of length `N - k` at `i + k`.
    have hmin : min k ((N : ℕ) - k) = (N : ℕ) - k := by omega
    rw [hmin]
    have hset : {X : Configuration N | (((N : ℕ) - k : ℕ) : ℝ) ^ (P.val.2 / 2 + ε) ≤
          |blockLength X i k - k|} =
        {X : Configuration N | (((N : ℕ) - k : ℕ) : ℝ) ^ (P.val.2 / 2 + ε) ≤
          |blockLength X (i + k) ((N : ℕ) - k) - (((N : ℕ) - k : ℕ) : ℝ)|} := by
      ext X
      simp only [Set.mem_ofPred_eq]
      rw [abs_blockLength_sub_reflect X i (by omega)]
    rw [hset]
    exact key (i + k) ((N : ℕ) - k) (by omega) (by omega)

end Riesz1

end
