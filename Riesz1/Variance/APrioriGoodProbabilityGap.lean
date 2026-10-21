/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BlockMoments
public import Riesz1.Rigidity.NoExplosionUniform
public import Riesz1.Variance.APrioriGoodProbabilityPairs
public import Riesz1.ToMathlib.Packing.ProbabilityTail

/-!
# Nearest-neighbour gap events and the real estimates

Steps of the proof of Lemma 5.2: the nearest-neighbour upper failure and lower failure
events, and the final arithmetic of the union bound.

* `APrioriProb.gap_upper_prob`: the gap exceeds `u` with probability at most `3 exp(-m u)`, by the
  exponential block tail with one gap.
* `APrioriProb.gap_lt_prob`: the gap lies below `t` with probability at most `C_p t^p`, by Markov's
  inequality for the inverse moment `gap^{-p}`.
* `APrioriProb.nearest_upper_prob` and `APrioriProb.nearest_lower_prob`: the two nearest-neighbour
  failure events of the cutoff, in the form of the union bound.
* `APrioriProb.exp_upper_le`: the exponential comparison with the factor `(C + 3)`.
* `APrioriProb.sum_real_le`: the final real inequality of the union bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

namespace APrioriProb

/-- **Upper gap tail.** For `2 ≤ N` and every `u`, the gap at `j` exceeds `u` with probability at
most `3 exp(-m u)`, where `m = blockMomentExponent`. -/
theorem gap_upper_prob (P : Parameters) (hPL : External.PrekopaLeindler) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (j : ℤ) (u : ℝ) :
    gibbsMeasure P N {X | u < gap X j} ≤
      ENNReal.ofReal (3 * Real.exp (-blockMomentExponent * u)) := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have h := blockLength_upper_tail hPL P N hN j 1 one_pos u
  simp only [Nat.cast_one, one_mul, blockLength_one] at h
  exact measure_le_ofReal_of_real_le _ _ h

/-- **Lower gap tail.** Let `p > 0` and suppose the lower integral of `gap^{-p}` is at most
`ofReal Cp`. Then for every `t > 0`, the gap at `j` lies below `t` with probability at most
`Cp t^p`. -/
theorem gap_lt_prob (P : Parameters) (N : ℕ+) (j : ℤ) {p Cp t : ℝ} (hp : 0 < p)
    (ht : 0 < t)
    (hint : ∫⁻ X, ENNReal.ofReal (gap X j ^ (-p)) ∂gibbsMeasure P N ≤ ENNReal.ofReal Cp) :
    gibbsMeasure P N {X | gap X j < t} ≤ ENNReal.ofReal (Cp * t ^ p) := by
  have hf : Measurable (fun X : Configuration N => gap X j ^ (-p)) :=
    (measurable_gap j).pow_const _
  have htp : 0 < t ^ p := Real.rpow_pos_of_pos ht p
  have hc : 0 < (t ^ p)⁻¹ := inv_pos.2 htp
  have hM := measure_le_ofReal_div_of_lintegral_le (gibbsMeasure P N) hf hc hint
  have hsub : {X : Configuration N | gap X j < t} ⊆
      {X : Configuration N | (t ^ p)⁻¹ ≤ gap X j ^ (-p)} := by
    intro X hX
    change gap X j < t at hX
    have hg := gap_pos X j
    change (t ^ p)⁻¹ ≤ gap X j ^ (-p)
    rw [Real.rpow_neg hg.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hg p) (Real.rpow_le_rpow hg.le hX.le hp.le)
  rw [div_inv_eq_mul] at hM
  exact (measure_mono hsub).trans hM

/-- **Upper nearest-neighbour failure.** For `K > 0`, the event `1 < 2 gap / K^ε` has probability
at most `3 exp(-m K^ε / 2)`. -/
theorem nearest_upper_prob (P : Parameters) (hPL : External.PrekopaLeindler) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (j : ℤ) {K ε : ℝ} (hK : 0 < K) :
    gibbsMeasure P N {X | 1 < 2 * gap X j / K ^ ε} ≤
      ENNReal.ofReal (3 * Real.exp (-blockMomentExponent * (K ^ ε / 2))) := by
  refine (measure_mono ?_).trans (gap_upper_prob P hPL N hN j (K ^ ε / 2))
  intro X hX
  change 1 < 2 * gap X j / K ^ ε at hX
  rw [one_lt_div (Real.rpow_pos_of_pos hK ε)] at hX
  change K ^ ε / 2 < gap X j
  linarith

/-- **Lower nearest-neighbour failure.** For `K > 0` and `p > 0` with lower integral of `gap^{-p}`
at most `ofReal Cp`, the event `1 < 2 / (K^ε gap)` has probability at most
`Cp (2 / K^ε)^p`. -/
theorem nearest_lower_prob (P : Parameters) (N : ℕ+) (j : ℤ) {p Cp K ε : ℝ} (hK : 0 < K)
    (hp : 0 < p)
    (hint : ∫⁻ X, ENNReal.ofReal (gap X j ^ (-p)) ∂gibbsMeasure P N ≤ ENNReal.ofReal Cp) :
    gibbsMeasure P N {X | 1 < 2 / (K ^ ε * gap X j)} ≤
      ENNReal.ofReal (Cp * (2 / K ^ ε) ^ p) := by
  have hKε : 0 < K ^ ε := Real.rpow_pos_of_pos hK ε
  refine (measure_mono ?_).trans (gap_lt_prob P N j hp (div_pos two_pos hKε) hint)
  intro X hX
  change 1 < 2 / (K ^ ε * gap X j) at hX
  have hg := gap_pos X j
  rw [one_lt_div (mul_pos hKε hg)] at hX
  change gap X j < 2 / K ^ ε
  rw [lt_div_iff₀ hKε]
  linarith [mul_comm (K ^ ε) (gap X j)]

/-- **Exponential comparison.** Let `0 ≤ θ ≤ m/2` and `0 ≤ e ≤ ε`, and let `K ≥ 1`. Then
`3 exp(-m K^ε/2) ≤ (C + 3) exp(-θ K^e)`, with `m = blockMomentExponent`. -/
theorem exp_upper_le {K ε e θ C : ℝ} (hK : 1 ≤ K) (he : e ≤ ε)
    (hθm : θ ≤ blockMomentExponent / 2) (hC : 0 ≤ C) :
    3 * Real.exp (-blockMomentExponent * (K ^ ε / 2)) ≤
      (C + 3) * Real.exp (-θ * K ^ e) := by
  have hK0 : 0 < K := by linarith
  have hKe0 : 0 ≤ K ^ e := Real.rpow_nonneg hK0.le e
  have hKe : K ^ e ≤ K ^ ε := Real.rpow_le_rpow_of_exponent_le hK he
  have hexp : Real.exp (-blockMomentExponent * (K ^ ε / 2)) ≤ Real.exp (-θ * K ^ e) := by
    apply Real.exp_le_exp.2
    have h1 : θ * K ^ e ≤ (blockMomentExponent / 2) * K ^ e :=
      mul_le_mul_of_nonneg_right hθm hKe0
    have h2 : (blockMomentExponent / 2) * K ^ e ≤ (blockMomentExponent / 2) * K ^ ε :=
      mul_le_mul_of_nonneg_left hKe (by have := blockMomentExponent_pos; positivity)
    have e1 : -blockMomentExponent * (K ^ ε / 2) = -((blockMomentExponent / 2) * K ^ ε) := by
      ring
    rw [e1, neg_mul]
    linarith
  have hE : 0 < Real.exp (-θ * K ^ e) := Real.exp_pos _
  have h3 := mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 3)
  have h4 : (C + 3) * Real.exp (-θ * K ^ e) =
      C * Real.exp (-θ * K ^ e) + 3 * Real.exp (-θ * K ^ e) := by ring
  have h5 : 0 ≤ C * Real.exp (-θ * K ^ e) := mul_nonneg hC hE.le
  linarith

/-- **Final real inequality of the union bound.** Let `K ≥ 1`, `γ ≥ 0`, `Cp, C ≥ 0`,
and let `Kb` bound `x^{2γ+B} exp(-θ x^e)` on `x ≥ 1`, with `ε p = B + γ + 1`. Then the sum of the
three contributions, `72 K^{2γ} A + 8 K^γ A + 8 K^γ Cp (2/K^ε)^p` with `A = (C+3) exp(-θK^e)`, is
at most `(80 (C+3) Kb + 8 Cp 2^p) K^{-B}`. -/
theorem sum_real_le {K γ ε B p Cp C θ e Kb : ℝ} (hK : 1 ≤ K) (hγ : 0 ≤ γ) (hCp : 0 ≤ Cp)
    (hC : 0 ≤ C) (hεp : ε * p = B + γ + 1)
    (hKb : K ^ (2 * γ + B) * Real.exp (-θ * K ^ e) ≤ Kb) :
    72 * K ^ (2 * γ) * ((C + 3) * Real.exp (-θ * K ^ e)) +
        8 * K ^ γ * ((C + 3) * Real.exp (-θ * K ^ e)) +
        8 * K ^ γ * (Cp * (2 / K ^ ε) ^ p) ≤
      (80 * (C + 3) * Kb + 8 * Cp * (2 : ℝ) ^ p) * K ^ (-B) := by
  have hK0 : 0 < K := by linarith
  have hKε : 0 < K ^ ε := Real.rpow_pos_of_pos hK0 ε
  have hKB : 0 < K ^ B := Real.rpow_pos_of_pos hK0 B
  have hKγ : 0 < K ^ γ := Real.rpow_pos_of_pos hK0 γ
  have hE : 0 ≤ Real.exp (-θ * K ^ e) := (Real.exp_pos _).le
  have hY : 0 ≤ K ^ (-B) := Real.rpow_nonneg hK0.le _
  have hA : 0 ≤ (C + 3) * Real.exp (-θ * K ^ e) := mul_nonneg (by linarith) hE
  have hK2 : K ^ γ ≤ K ^ (2 * γ) := Real.rpow_le_rpow_of_exponent_le hK (by linarith)
  -- The factor `K^{2γ} exp(-θ K^e)` is at most `Kb K^{-B}`.
  have hX : K ^ (2 * γ) * Real.exp (-θ * K ^ e) ≤ Kb * K ^ (-B) := by
    rw [Real.rpow_add hK0, Real.rpow_neg hK0.le] at *
    have hKBne : K ^ B ≠ 0 := hKB.ne'
    have hkey : K ^ (2 * γ) * Real.exp (-θ * K ^ e) =
        (K ^ (2 * γ) * K ^ B * Real.exp (-θ * K ^ e)) * (K ^ B)⁻¹ := by
      field_simp
    rw [hkey]
    exact mul_le_mul_of_nonneg_right hKb (inv_nonneg.2 hKB.le)
  -- The factor `K^γ (2/K^ε)^p` is at most `2^p K^{-B}`.
  have hZ : K ^ γ * (2 / K ^ ε) ^ p ≤ 2 ^ p * K ^ (-B) := by
    have hpow2 : (2 / K ^ ε) ^ p = 2 ^ p / K ^ (B + γ + 1) := by
      rw [Real.div_rpow (by norm_num) hKε.le, ← Real.rpow_mul hK0.le, hεp]
    have hsplit : K ^ (B + γ + 1) = K ^ B * K ^ γ * K := by
      rw [Real.rpow_add hK0, Real.rpow_add hK0, Real.rpow_one]
    rw [hpow2, hsplit, Real.rpow_neg hK0.le]
    have hK1inv : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
    have hKγne : K ^ γ ≠ 0 := hKγ.ne'
    have hKBne : K ^ B ≠ 0 := hKB.ne'
    have hKne : K ≠ 0 := hK0.ne'
    calc K ^ γ * (2 ^ p / (K ^ B * K ^ γ * K)) = 2 ^ p * (K ^ B)⁻¹ * K⁻¹ := by
          field_simp
      _ ≤ 2 ^ p * (K ^ B)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hK1inv (by positivity)
      _ = 2 ^ p * (K ^ B)⁻¹ := mul_one _
  have h1 : K ^ γ * ((C + 3) * Real.exp (-θ * K ^ e)) ≤
      K ^ (2 * γ) * ((C + 3) * Real.exp (-θ * K ^ e)) :=
    mul_le_mul_of_nonneg_right hK2 hA
  have h2 : (C + 3) * (K ^ (2 * γ) * Real.exp (-θ * K ^ e)) ≤
      (C + 3) * (Kb * K ^ (-B)) := mul_le_mul_of_nonneg_left hX (by linarith)
  have h3 : Cp * (K ^ γ * (2 / K ^ ε) ^ p) ≤ Cp * (2 ^ p * K ^ (-B)) :=
    mul_le_mul_of_nonneg_left hZ hCp
  linarith

end APrioriProb

end Riesz1

end
end
