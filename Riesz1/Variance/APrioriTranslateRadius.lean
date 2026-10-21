/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriConclusion
public import Riesz1.ToMathlib.Calculus.CutoffMajorant

/-!
# Changing the fixed envelope radius

The fixed-radius clause of Lemma 5.2 follows from a
pointwise comparison of the envelopes. The factor is independent
of the scale `K ≥ 1` and of the distance to the centre.
-/

@[expose] public section

noncomputable section

namespace Riesz1.Internal

/-- Every positive fixed radius is dominated by radius two, uniformly
in the microscopic cutoff `K⁻¹`. No rescaling of the observation length
is necessary, so the macroscopic endpoint is included. -/
theorem aPrioriEnvelope_radius_le {s lam R : ℝ}
    (hs : s < 3) (hlam : 0 ≤ lam) (hR : 0 < R) :
    ∃ B : ℝ, 0 < B ∧ ∀ K : ℝ, 1 ≤ K → ∀ d : ℝ, 0 ≤ d →
      aPrioriEnvelope s lam K R d ≤ B * aPrioriEnvelope s lam K 2 d := by
  let A := (max R 2) ^ (3 - s)
  let B := 2 ^ (1 + lam) * (min R 1) ^ (-(3 - s))
  have hA : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨2 + A + B, by positivity, ?_⟩
  intro K hK d hd
  let a := ((max d K⁻¹) ^ (1 + lam))⁻¹
  let b := (d ^ (3 - s))⁻¹
  let E := aPrioriEnvelope s lam K 2 d
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hE : 0 ≤ E := by
    dsimp [E, aPrioriEnvelope]
    split_ifs <;> positivity
  have hanear : (if d ≤ 2 then a else 0) ≤ E := by
    change (if d ≤ 2 then a else 0) ≤
      (if d ≤ 2 then a else 0) + (if 2 ≤ d then b else 0)
    have h : 0 ≤ (if 2 ≤ d then b else 0) := by split_ifs <;> positivity
    linarith
  have hbfar : (if 2 ≤ d then b else 0) ≤ E := by
    change (if 2 ≤ d then b else 0) ≤
      (if d ≤ 2 then a else 0) + (if 2 ≤ d then b else 0)
    have h : 0 ≤ (if d ≤ 2 then a else 0) := by split_ifs <;> positivity
    linarith
  have hnear : (if d ≤ R then a else 0) ≤ (1 + A) * E := by
    split_ifs with hdR
    · by_cases hd2 : d ≤ 2
      · have h := hanear
        rw [ite_eq_left hd2] at h
        have he := mul_nonneg hA hE
        nlinarith
      · have h2d : 2 ≤ d := le_of_lt (lt_of_not_ge hd2)
        have hdpos : 0 < d := by linarith
        have hmax : 1 ≤ max d K⁻¹ := le_trans (by linarith) (le_max_left _ _)
        have ha1 : a ≤ 1 := by
          dsimp [a]
          exact inv_le_one_of_one_le₀ (Real.one_le_rpow hmax (by linarith))
        have hdp : 0 < d ^ (3 - s) := Real.rpow_pos_of_pos hdpos _
        have hdpA : d ^ (3 - s) ≤ A :=
          Real.rpow_le_rpow hdpos.le (hdR.trans (le_max_left _ _)) (by linarith)
        have hAb : 1 ≤ A * b := by
          dsimp [b]
          exact (le_mul_inv_iff₀ hdp).2 (by simpa only [one_mul] using hdpA)
        have hbe : b ≤ E := by simpa only [ite_eq_left h2d] using hbfar
        have hm := mul_le_mul_of_nonneg_left hbe hA
        nlinarith
    · exact mul_nonneg (by positivity) hE
  have hfar : (if R ≤ d then b else 0) ≤ (1 + B) * E := by
    split_ifs with hRd
    · by_cases h2d : 2 ≤ d
      · have h := hbfar
        rw [ite_eq_left h2d] at h
        have he := mul_nonneg hB hE
        nlinarith
      · have hdpos : 0 < d := lt_of_lt_of_le hR hRd
        have hmpos : 0 < min R 1 := lt_min hR zero_lt_one
        have hmin : min R 1 ≤ d := (min_le_left _ _).trans hRd
        have hbB : b ≤ (min R 1) ^ (-(3 - s)) := by
          dsimp [b]
          rw [← Real.rpow_neg hdpos.le]
          exact Real.rpow_le_rpow_of_nonpos hmpos hmin (by linarith)
        have hKinv : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
        have hm : max d K⁻¹ ≤ 2 := max_le (by linarith) (by linarith)
        have hmaxpos : 0 < max d K⁻¹ := lt_of_lt_of_le hdpos (le_max_left _ _)
        have hpow : (max d K⁻¹) ^ (1 + lam) ≤ 2 ^ (1 + lam) :=
          Real.rpow_le_rpow hmaxpos.le hm (by linarith)
        have haB : (2 ^ (1 + lam))⁻¹ ≤ a := by
          dsimp [a]
          exact inv_anti₀ (Real.rpow_pos_of_pos hmaxpos _) hpow
        have haE : a ≤ E := by
          simpa only [ite_eq_left (by linarith : d ≤ 2)] using hanear
        have hBmul : (min R 1) ^ (-(3 - s)) ≤ B * E := by
          have hm' := mul_le_mul_of_nonneg_left (haB.trans haE) hB
          have hp : 2 ^ (1 + lam) ≠ (0 : ℝ) := (Real.rpow_pos_of_pos (by norm_num) _).ne'
          dsimp only [B] at hm'
          have he : (2 ^ (1 + lam) * (min R 1) ^ (-(3 - s))) *
              (2 ^ (1 + lam))⁻¹ = (min R 1) ^ (-(3 - s)) := by field_simp
          rwa [he] at hm'
        nlinarith
    · exact mul_nonneg (by positivity) hE
  change (if d ≤ R then a else 0) + (if R ≤ d then b else 0) ≤ (2 + A + B) * E
  nlinarith only [hnear, hfar]

end Riesz1.Internal

end
