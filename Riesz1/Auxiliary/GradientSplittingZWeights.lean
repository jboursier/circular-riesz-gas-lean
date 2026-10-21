/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingDifferences

/-!
# The weights `w_1`, `w_2` and their monotonicity

The data part of Lemma 5.7. The weight `w_1` is
`gradWeightOne` of `GradientSplittingDifferences.lean`. Here we add the weight `w_2` and the facts
used by the divided-difference and convolution estimates: both weights are nonincreasing in the
circular distance, and they are bounded by `K^a` and `K^{1+a}`.

Throughout, `K ≥ 1` and `0 ≤ a`, so that the exponents `-a` and `-(1+a)` are nonpositive.
-/

@[expose] public section

namespace Riesz1

/-- The weight `w_2` of the data part of Lemma 5.7 on `L𝕋`, with the parameter `K`:
`max(|u|, K^{-1})^{-1-a}` when `|u| < 1`, and `|u|^{s-3}` when `|u| ≥ 1`, where `|u|` is the
circular distance `circDist L u`. -/
noncomputable def gradWeightTwo (s a K L u : ℝ) : ℝ :=
  if circDist L u < 1 then max (circDist L u) K⁻¹ ^ (-(1 + a)) else circDist L u ^ (s - 3)

/-- The weight `w_1` is nonincreasing in the circular distance. -/
lemma gradWeightOne_le_of_circDist_le {s a K L u v : ℝ} (hs1 : s < 1) (ha : 0 ≤ a) (hK : 1 ≤ K)
    (huv : circDist L u ≤ circDist L v) : gradWeightOne s a K L v ≤ gradWeightOne s a K L u := by
  have hK0 : 0 < K⁻¹ := by positivity
  unfold gradWeightOne
  by_cases hv : circDist L v < 1
  · have hu : circDist L u < 1 := lt_of_le_of_lt huv hv
    simp only [hv, hu, ↓reduceIte]
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hK0 (le_max_right _ _))
      (max_le_max huv le_rfl) (by linarith)
  · have hv' : 1 ≤ circDist L v := not_lt.mp hv
    simp only [hv, ↓reduceIte]
    by_cases hu : circDist L u < 1
    · simp only [hu, ↓reduceIte]
      have h1 : max (circDist L u) K⁻¹ ≤ 1 :=
        max_le hu.le (by rw [inv_le_one₀ (by linarith)]; linarith)
      have hpos : 0 < max (circDist L u) K⁻¹ := lt_of_lt_of_le hK0 (le_max_right _ _)
      have h2 : 1 ≤ max (circDist L u) K⁻¹ ^ (-a) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos h1 (by linarith)
      have h3 : circDist L v ^ (s - 2) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hv' (by linarith)
      exact le_trans h3 h2
    · simp only [hu, ↓reduceIte]
      exact Real.rpow_le_rpow_of_nonpos (by linarith [not_lt.mp hu]) huv (by linarith)

/-- The weight `w_2` is nonincreasing in the circular distance. -/
lemma gradWeightTwo_le_of_circDist_le {s a K L u v : ℝ} (hs1 : s < 1) (ha : 0 ≤ a) (hK : 1 ≤ K)
    (huv : circDist L u ≤ circDist L v) : gradWeightTwo s a K L v ≤ gradWeightTwo s a K L u := by
  have hK0 : 0 < K⁻¹ := by positivity
  unfold gradWeightTwo
  by_cases hv : circDist L v < 1
  · have hu : circDist L u < 1 := lt_of_le_of_lt huv hv
    simp only [hv, hu, ↓reduceIte]
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hK0 (le_max_right _ _))
      (max_le_max huv le_rfl) (by linarith)
  · have hv' : 1 ≤ circDist L v := not_lt.mp hv
    simp only [hv, ↓reduceIte]
    by_cases hu : circDist L u < 1
    · simp only [hu, ↓reduceIte]
      have h1 : max (circDist L u) K⁻¹ ≤ 1 :=
        max_le hu.le (by rw [inv_le_one₀ (by linarith)]; linarith)
      have hpos : 0 < max (circDist L u) K⁻¹ := lt_of_lt_of_le hK0 (le_max_right _ _)
      have h2 : 1 ≤ max (circDist L u) K⁻¹ ^ (-(1 + a)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos h1 (by linarith)
      have h3 : circDist L v ^ (s - 3) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hv' (by linarith)
      exact le_trans h3 h2
    · simp only [hu, ↓reduceIte]
      exact Real.rpow_le_rpow_of_nonpos (by linarith [not_lt.mp hu]) huv (by linarith)

/-- The weight `w_1` is bounded by `K^a`, the value at the origin. -/
lemma gradWeightOne_le_K_pow {s a K L u : ℝ} (hs1 : s < 1) (ha : 0 ≤ a) (hK : 1 ≤ K) :
    gradWeightOne s a K L u ≤ K ^ a := by
  have hK0 : 0 < K := by linarith
  unfold gradWeightOne
  split_ifs with hu
  · have hpos : 0 < max (circDist L u) K⁻¹ := lt_of_lt_of_le (inv_pos.mpr hK0) (le_max_right _ _)
    calc max (circDist L u) K⁻¹ ^ (-a) ≤ (K⁻¹) ^ (-a) :=
          Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hK0) (le_max_right _ _) (by linarith)
      _ = K ^ a := by rw [Real.inv_rpow hK0.le, Real.rpow_neg hK0.le, inv_inv]
  · have : circDist L u ^ (s - 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [not_lt.mp hu]) (by linarith)
    exact le_trans this (Real.one_le_rpow hK (by linarith))

/-- The weight `w_2` is bounded by `K^{1+a}`, the value at the origin. -/
lemma gradWeightTwo_le_K_pow {s a K L u : ℝ} (hs1 : s < 1) (ha : 0 ≤ a) (hK : 1 ≤ K) :
    gradWeightTwo s a K L u ≤ K ^ (1 + a) := by
  have hK0 : 0 < K := by linarith
  unfold gradWeightTwo
  split_ifs with hu
  · have hpos : 0 < max (circDist L u) K⁻¹ := lt_of_lt_of_le (inv_pos.mpr hK0) (le_max_right _ _)
    calc max (circDist L u) K⁻¹ ^ (-(1 + a)) ≤ (K⁻¹) ^ (-(1 + a)) :=
          Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hK0) (le_max_right _ _) (by linarith)
      _ = K ^ (1 + a) := by rw [Real.inv_rpow hK0.le, Real.rpow_neg hK0.le, inv_inv]
  · have : circDist L u ^ (s - 3) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [not_lt.mp hu]) (by linarith)
    exact le_trans this (Real.one_le_rpow hK (by linarith))

end Riesz1

end
