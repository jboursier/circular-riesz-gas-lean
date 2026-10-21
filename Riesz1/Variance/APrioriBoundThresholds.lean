/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodComparison
public import Riesz1.Variance.APrioriComparisonWeights
public import Riesz1.ToMathlib.Calculus.CutoffMajorant

/-!
# The sharp indicator thresholds in the a priori bound

The anchored error controls the circular distance error, including
labels past the antipode. This gives the two indicator implications
used in the proof of Lemma 5.2. The near implication
requires the explicit large-scale condition `4 ≤ K^ε`.
-/

public section

noncomputable section

open Set

namespace Riesz1.Internal

/-- The near spatial region can only contain labels in the near
comparison region, at sufficiently large scales. -/
theorem a_priori_inner_threshold {s K ε d t : ℝ}
    (_hs : 0 < s) (hs1 : s < 1) (hK : 1 ≤ K) (hε : 0 < ε)
    (hεs : ε ≤ (1 - s / 2) / 2) (hlarge : 4 ≤ K ^ ε)
    (hd : 0 < d) (herr : |K * t - d| ≤ K ^ ε * d ^ (s / 2))
    (ht : t ≤ 2) : d ≤ K ^ (1 + ε) := by
  have hK0 : 0 < K := by linarith
  have hq : 0 < 1 - s / 2 := by linarith
  by_contra h
  have hdK : K ^ (1 + ε) ≤ d := (lt_of_not_ge h).le
  have hp : (K ^ ε) ^ 2 ≤ d ^ (1 - s / 2) := by
    calc
      _ = K ^ (2 * ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
        congr 1
        ring
      _ ≤ K ^ ((1 + ε) * (1 - s / 2)) :=
        Real.rpow_le_rpow_of_exponent_le hK (by nlinarith)
      _ = (K ^ (1 + ε)) ^ (1 - s / 2) := Real.rpow_mul hK0.le _ _
      _ ≤ d ^ (1 - s / 2) := Real.rpow_le_rpow (by positivity) hdK hq.le
  have hhalf : 2 * K ^ ε * d ^ (s / 2) ≤ d := by
    calc
      _ ≤ d ^ (1 - s / 2) * d ^ (s / 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
      _ = d := by rw [← Real.rpow_add hd]; simp
  have hlow := (abs_le.mp herr).1
  have hpow : K ^ (1 + ε) = K * K ^ ε := by
    rw [Real.rpow_add hK0, Real.rpow_one]
  rw [hpow] at h
  have hhigh : K * t ≤ 2 * K := by nlinarith
  nlinarith

/-- The far spatial region can only contain labels in the far
comparison region. This implication holds for every `K ≥ 1`. -/
theorem a_priori_outer_threshold {s K ε d t : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hK : 1 ≤ K) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hd : 0 ≤ d) (herr : |K * t - d| ≤ K ^ ε * d ^ (s / 2))
    (ht : 2 ≤ t) : K ^ (1 - ε) ≤ d := by
  have hK0 : 0 < K := by linarith
  by_contra h
  have hdK : d < K ^ (1 - ε) := lt_of_not_ge h
  have hd1 : d < K := hdK.trans_le (by
    calc _ ≤ K ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK (by linarith)
         _ = K := Real.rpow_one _)
  have hp : K ^ ε * d ^ (s / 2) ≤ K := by
    calc
      _ ≤ K ^ ε * (K ^ (1 - ε)) ^ (s / 2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hd hdK.le (by linarith)) (by positivity)
      _ = K ^ (ε + (1 - ε) * (s / 2)) := by
        rw [← Real.rpow_mul hK0.le, ← Real.rpow_add hK0]
      _ ≤ K ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK (by nlinarith)
      _ = K := Real.rpow_one _
  have hhigh := (abs_le.mp herr).2
  have hlow : 2 * K ≤ K * t := by nlinarith
  linarith

/-- A distance error in the ordered lift bounds the corresponding
circular distance error. In particular no choice of the shorter arc
or of a signed label is added to the hypotheses. -/
theorem a_priori_circular_error {N : ℕ+} (X : Configuration N) (i : Fin (N : ℕ)) :
    |((N : ℕ) : ℝ) * circDist 1 (X.val i - X.val ⟨0, N.pos⟩) -
        (labelDistToOne N i : ℝ)| ≤
      |((N : ℕ) : ℝ) * (X.val i - X.val ⟨0, N.pos⟩) - (i : ℕ)| := by
  let x := X.val i - X.val ⟨0, N.pos⟩
  have hx0 : 0 ≤ x := by
    exact sub_nonneg.mpr (X.property.1.monotone (Fin.zero_le i))
  have hx1 : x < 1 := by
    exact sub_lt_iff_lt_add.mpr (by simpa only [add_comm] using X.property.2.2.2 i)
  have hc : circDist 1 x = min x (1 - x) := by
    rw [APG.circDist_one_eq_abs_sub_round, abs_sub_round_eq_min,
      Int.fract_eq_self.mpr ⟨hx0, hx1⟩]
  have hiN : (i : ℕ) ≤ (N : ℕ) := Nat.le_of_lt i.isLt
  have hd : (labelDistToOne N i : ℝ) = min (i : ℝ) (((N : ℕ) : ℝ) - (i : ℝ)) := by
    rw [labelDistToOne_eq, Nat.cast_min, Nat.cast_sub hiN]
  change |((N : ℕ) : ℝ) * circDist 1 x - (labelDistToOne N i : ℝ)| ≤ _
  rw [hc, hd, mul_min_of_nonneg _ _ (Nat.cast_nonneg (N : ℕ))]
  have h := abs_min_sub_min_le_max
    (((N : ℕ) : ℝ) * x) (((N : ℕ) : ℝ) * (1 - x))
    (i : ℝ) (((N : ℕ) : ℝ) - (i : ℝ))
  have he : ((N : ℕ) : ℝ) * (1 - x) - (((N : ℕ) : ℝ) - (i : ℝ)) =
      -(((N : ℕ) : ℝ) * x - (i : ℝ)) := by ring
  simpa only [he, abs_neg, max_self] using h

/-- The two sharp thresholds for actual circular positions on the good
event. This also covers a full window and labels beyond the antipode. -/
theorem a_priori_good_thresholds {N : ℕ+} (X : Configuration N)
    {s K γ ε ℓ : ℝ} (hs : 0 < s) (hs1 : s < 1) (hK : 1 ≤ K)
    (hε : 0 < ε) (hεs : ε ≤ (1 - s / 2) / 2) (hlarge : 4 ≤ K ^ ε)
    (hℓ : 0 < ℓ) (hscale : K = ((N : ℕ) : ℝ) * ℓ)
    (hX : X ∈ goodEvent N s K γ ε) {i : Fin (N : ℕ)}
    (hi : i ∈ window N K γ) (hi0 : i ≠ ⟨0, N.pos⟩) :
    (circDist 1 (X.val i - X.val ⟨0, N.pos⟩) / ℓ ≤ 2 →
      (labelDistToOne N i : ℝ) ≤ K ^ (1 + ε)) ∧
    (2 ≤ circDist 1 (X.val i - X.val ⟨0, N.pos⟩) / ℓ →
      K ^ (1 - ε) ≤ (labelDistToOne N i : ℝ)) := by
  have hd : 0 < (labelDistToOne N i : ℝ) := by
    have : 1 ≤ labelDistToOne N i := by
      rw [labelDistToOne_eq]
      have : 0 < i.val := by
        by_contra h
        exact hi0 (Fin.ext (show i.val = 0 by omega))
      have := i.isLt
      omega
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one this
  have he : K * (circDist 1 (X.val i - X.val ⟨0, N.pos⟩) / ℓ) =
      ((N : ℕ) : ℝ) * circDist 1 (X.val i - X.val ⟨0, N.pos⟩) := by
    rw [hscale]
    field_simp
  have herr : |K * (circDist 1 (X.val i - X.val ⟨0, N.pos⟩) / ℓ) -
      (labelDistToOne N i : ℝ)| ≤ K ^ ε * (labelDistToOne N i : ℝ) ^ (s / 2) := by
    rw [he]
    exact (a_priori_circular_error X i).trans (APG.anchored_error X hK hX hi)
  exact ⟨a_priori_inner_threshold hs hs1 hK hε hεs hlarge hd herr,
    a_priori_outer_threshold hs hs1 hK hε.le (by linarith) hd.le herr⟩

end Riesz1.Internal

end
