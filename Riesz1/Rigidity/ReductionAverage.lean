/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ReductionScales
public import Riesz1.Rigidity.ReductionAverageTail
public import Riesz1.Rigidity.ForcingPotential

/-!
# Comparison to a block average

This is Lemma 4.4. Let `P` be the Gibbs parameters, with exponent `s = P.val.2`, and let
`ε > 0`. For every `N ≥ 2`, every label `i ∈ ℤ` and every scale `1 ≤ k ≤ N/2`, the centered particle
`N (x_i - x_i^{[k]})` exceeds `k^{s/2+ε}` in absolute value with probability at most
`C exp(-c k^{ε/(s+2)})`, where `c, C` depend only on `s, β, ε` and not on `N`, `i`, `k`.

The proof splits `N (x_i - x_i^{[k]})` into the `q` multiscale increments `G_m` of
`Riesz1.reduction_av_scales`, with `q = max 2 ⌈2/ε⌉`. If the sum has absolute value at least
`k^{s/2+ε}`, some increment has absolute value at least `k^{s/2+ε}/q`. Each increment is compared with
its constrained law `Q_m` in total variation and bounded by the Chernoff tail of the centered moment bound.
When `k^{s/2+ε} < q`, the bound is trivial after enlarging `C`.

The Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler inequality
`External.PrekopaLeindler` enter as explicit hypotheses. The proof works for every `ε > 0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset

namespace Riesz1

/-- **Comparison to a block average**, Lemma 4.4. The constants `c, C` depend only on
the Gibbs parameters and `ε`, and are chosen before `N`, `i` and `k`. -/
theorem reduction_av (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) {ε : ℝ} (hε : 0 < ε) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ+) (_hN : 2 ≤ (N : ℕ)) (i : ℤ) {k : ℕ}, 1 ≤ k →
      2 * k ≤ (N : ℕ) →
      (gibbsMeasure P N).real {X | (k : ℝ) ^ ((parametersExponent P).val / 2 + ε) ≤
          |((N : ℕ) : ℝ) * (cyclicLift X i - blockAverage X i k)|} ≤
        C * Real.exp (-c * (k : ℝ) ^ (ε / ((parametersExponent P).val + 2))) := by
  classical
  rw [show (parametersExponent P).val = P.val.2 from rfl]
  have hs : 0 < P.val.2 := P.property.2.1
  set q : ℕ := max 2 ⌈2 / ε⌉₊ with hqdef
  have hq2 : 2 ≤ q := le_max_left _ _
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq2' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hqε : 2 / ε ≤ (q : ℝ) := by
    have h1 : 2 / ε ≤ (⌈2 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈2 / ε⌉₊ ≤ q := le_max_right _ _
    exact h1.trans (by exact_mod_cast h2)
  obtain ⟨Cs, hCs, hscale⟩ :=
    reduction_av_scales hBE hPL P hε hq2 hqε isForcingCutoff_forcingCutoff
  have hc0 : 0 < Real.log 2 / 4 := div_pos (Real.log_pos one_lt_two) (by norm_num)
  have ha0 : 0 < 1 / (16 * (q : ℝ) ^ 2 * Cs) := by positivity
  set c : ℝ := min (1 / (16 * (q : ℝ) ^ 2 * Cs)) (Real.log 2 / 4) with hcdef
  have hc : 0 < c := lt_min ha0 hc0
  have hca : c ≤ 1 / (16 * (q : ℝ) ^ 2 * Cs) := min_le_left _ _
  have hcb : c ≤ Real.log 2 / 4 := min_le_right _ _
  refine ⟨c, 5 * (q : ℝ) + Real.exp (c * q), hc, by positivity, ?_⟩
  intro N hN i k hk hkN
  have := isProbabilityMeasure_gibbsMeasure P N
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hαk : 0 ≤ (k : ℝ) ^ (ε / (P.val.2 + 2)) := Real.rpow_nonneg hk0.le _
  have hαT : ε / (P.val.2 + 2) ≤ P.val.2 / 2 + ε := by
    have : ε / (P.val.2 + 2) ≤ ε := div_le_self hε.le (by linarith)
    linarith
  by_cases hgood : (q : ℝ) ≤ (k : ℝ) ^ (P.val.2 / 2 + ε)
  · -- The threshold is at least `1` after division by `q`: the increments can be compared.
    have hw1 : (1 : ℝ) ≤ (k : ℝ) ^ (P.val.2 / 2 + ε) / q := (one_le_div hq0).mpr hgood
    have hmtail : ∀ m ∈ range q,
        (gibbsMeasure P N).real
            {X | (k : ℝ) ^ (P.val.2 / 2 + ε) / q ≤ |scaleIncrement i k q m X|} ≤
          5 * Real.exp (-c * (k : ℝ) ^ (ε / (P.val.2 + 2))) := by
      intro m hm
      have hmq : m < q := mem_range.mp hm
      obtain ⟨hsum, -, hmean, hTV, hmom⟩ := hscale N hN i hk hkN hmq
      have := isProbabilityMeasure_scaleLaw P N isForcingCutoff_forcingCutoff ε i hk q m
      have hK : 0 < Cs * (k : ℝ) ^ (P.val.2 + 1 / (q : ℝ) + ε) :=
        mul_pos hCs (Real.rpow_pos_of_pos hk0 _)
      have hcen := measureReal_le_totalVariation_add_of_centered (gibbsMeasure P N)
        (scaleLaw P N forcingCutoff ε i k q m) (measurable_scaleIncrement i k q m) hK hw1 hmean
        (fun t => (hmom t).1) (fun t => le_of_le_of_eq (hmom t).2.2 (by ring))
      have hexp := reduction_av_exponent_le (s := P.val.2) (ε := ε) (q := (q : ℝ)) (Cs := Cs)
        (k := (k : ℝ)) hs hε hq2' hqε hCs hk1
      have hTVb : totalVariation (gibbsMeasure P N) (scaleLaw P N forcingCutoff ε i k q m) ≤
          3 * Real.exp (-c * (k : ℝ) ^ (ε / (P.val.2 + 2))) := by
        refine hTV.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
        rw [neg_mul, neg_mul]
        exact neg_le_neg (mul_le_mul_of_nonneg_right hcb hαk)
      have hTail : 2 * Real.exp (-((k : ℝ) ^ (P.val.2 / 2 + ε) / q) ^ 2 /
          (16 * (Cs * (k : ℝ) ^ (P.val.2 + 1 / (q : ℝ) + ε)))) ≤
          2 * Real.exp (-c * (k : ℝ) ^ (ε / (P.val.2 + 2))) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hexp.trans ?_)) (by norm_num)
        rw [neg_mul, neg_mul]
        exact neg_le_neg (mul_le_mul_of_nonneg_right hca hαk)
      linarith
    have hsubset : {X : Configuration N | (k : ℝ) ^ (P.val.2 / 2 + ε) ≤
        |((N : ℕ) : ℝ) * (cyclicLift X i - blockAverage X i k)|} ⊆
          ⋃ m ∈ range q, {X | (k : ℝ) ^ (P.val.2 / 2 + ε) / q ≤ |scaleIncrement i k q m X|} := by
      intro X hX
      by_contra hcon
      have hlt : ∀ m ∈ range q, |scaleIncrement i k q m X| < (k : ℝ) ^ (P.val.2 / 2 + ε) / q := by
        intro m hm
        by_contra hm'
        exact hcon (Set.mem_iUnion₂.mpr ⟨m, hm, not_lt.mp hm'⟩)
      obtain ⟨hsum, -⟩ := hscale N hN i hk hkN (show 0 < q by omega)
      have hX' : (k : ℝ) ^ (P.val.2 / 2 + ε) ≤ |∑ m ∈ range q, scaleIncrement i k q m X| := by
        rw [hsum X]
        exact hX
      have h1 := Finset.abs_sum_le_sum_abs (fun m => scaleIncrement i k q m X) (range q)
      have h2 : ∑ m ∈ range q, |scaleIncrement i k q m X| <
          ∑ _m ∈ range q, (k : ℝ) ^ (P.val.2 / 2 + ε) / q :=
        Finset.sum_lt_sum_of_nonempty ⟨0, mem_range.mpr (by omega)⟩ hlt
      have hqT : (∑ _m ∈ range q, (k : ℝ) ^ (P.val.2 / 2 + ε) / q) = (k : ℝ) ^ (P.val.2 / 2 + ε) := by
        rw [sum_const, card_range, nsmul_eq_mul]
        field_simp
      linarith
    calc (gibbsMeasure P N).real {X : Configuration N | (k : ℝ) ^ (P.val.2 / 2 + ε) ≤
            |((N : ℕ) : ℝ) * (cyclicLift X i - blockAverage X i k)|}
        ≤ (gibbsMeasure P N).real
            (⋃ m ∈ range q, {X | (k : ℝ) ^ (P.val.2 / 2 + ε) / q ≤ |scaleIncrement i k q m X|}) :=
          measureReal_mono hsubset (measure_ne_top _ _)
      _ ≤ ∑ m ∈ range q,
            (gibbsMeasure P N).real
              {X | (k : ℝ) ^ (P.val.2 / 2 + ε) / q ≤ |scaleIncrement i k q m X|} :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _m ∈ range q, 5 * Real.exp (-c * (k : ℝ) ^ (ε / (P.val.2 + 2))) :=
          Finset.sum_le_sum hmtail
      _ = (5 * (q : ℝ)) * Real.exp (-c * (k : ℝ) ^ (ε / (P.val.2 + 2))) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          ring
      _ ≤ (5 * (q : ℝ) + Real.exp (c * q)) * Real.exp (-c * (k : ℝ) ^ (ε / (P.val.2 + 2))) :=
          mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos (c * q)])
            (Real.exp_pos _).le
  · -- Below the threshold `k^{s/2+ε} < q` the probability is at most one, and the claim holds
    -- once `C` absorbs the factor `exp(c q)`.
    have hbad : (k : ℝ) ^ (P.val.2 / 2 + ε) < q := not_le.mp hgood
    have hkα : (k : ℝ) ^ (ε / (P.val.2 + 2)) ≤ q :=
      (Real.rpow_le_rpow_of_exponent_le hk1 hαT).trans hbad.le
    have hbound : 1 ≤ Real.exp (c * q) * Real.exp (-c * (k : ℝ) ^ (ε / (P.val.2 + 2))) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp_iff.mpr ?_
      have : c * (k : ℝ) ^ (ε / (P.val.2 + 2)) ≤ c * q := mul_le_mul_of_nonneg_left hkα hc.le
      linarith
    calc (gibbsMeasure P N).real {X : Configuration N | (k : ℝ) ^ (P.val.2 / 2 + ε) ≤
            |((N : ℕ) : ℝ) * (cyclicLift X i - blockAverage X i k)|}
        ≤ 1 := measureReal_le_one
      _ ≤ Real.exp (c * q) * Real.exp (-c * (k : ℝ) ^ (ε / (P.val.2 + 2))) := hbound
      _ ≤ (5 * (q : ℝ) + Real.exp (c * q)) * Real.exp (-c * (k : ℝ) ^ (ε / (P.val.2 + 2))) :=
          mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos (c * q), hq0])
            (Real.exp_pos _).le

end Riesz1

end
