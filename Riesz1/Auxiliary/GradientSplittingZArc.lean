/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingZWeights

/-!
# Arcs of the circle and the weight integrals from the origin

The differences part of Lemma 5.7: auxiliary facts for its
`Z`-bounds. Let `L > 0` be the length of the circle `L𝕋`, so that `L = ℓ^{-1}`.

* Circular distance. `circDist L t` is the distance from `t` to `Lℤ`. It equals `min_n |t - nL|`.
  It is even, `L`-periodic, and at most `L/2`.
* Lattice-free segments. If a segment `[p, q]` contains no point of `Lℤ`, the circular distance
  on it is at least the smaller endpoint distance, so `w_1` and `w_2` are at most their larger
  endpoint values there.
* Integrals from the origin. `G(T) = ∫_0^T w_1` for `0 ≤ T ≤ L/2`. It satisfies
  `G(T) ≤ (1 + 1/(1-a)) T max(T, K^{-1})^{-a}` for `T ≤ 1`, and
  `G(T) ≤ 1 + 1/(1-a) + 1/(1-s)` for `T ≤ L/2`.
* Arm bound. If `|ψ'| ≤ C_0 w_1` and `ψ` is `L`-periodic, then `|ψ(r) - ψ(0)| ≤ C_0 G(circDist L r)`.
-/

@[expose] public section

open Set MeasureTheory
open scoped ContDiff

namespace Riesz1

/-- Rounding to the nearest integer is at least as close as any integer: `|x - round x| ≤ |x - n|`
for every `n ∈ ℤ`. -/
lemma abs_sub_round_le_abs_sub_int (x : ℝ) (n : ℤ) : |x - round x| ≤ |x - n| := by
  have hx := abs_le.mp (abs_sub_round x)
  rcases lt_trichotomy n (round x) with h | h | h
  · have h1 : (n : ℝ) + 1 ≤ round x := by exact_mod_cast h
    exact le_trans (abs_sub_round x) (le_abs.mpr (Or.inl (by linarith [hx.1])))
  · rw [h]
  · have h1 : (round x : ℝ) + 1 ≤ n := by exact_mod_cast h
    exact le_trans (abs_sub_round x) (le_abs.mpr (Or.inr (by linarith [hx.2])))

/-- The circular distance is at most the distance to any point of `Lℤ`. -/
lemma circDist_le_abs_sub_int_mul {L : ℝ} (hL : 0 < L) (t : ℝ) (n : ℤ) :
    circDist L t ≤ |t - n * L| := by
  have h := abs_sub_round_le_abs_sub_int (t / L) n
  have hL0 : L ≠ 0 := hL.ne'
  unfold circDist
  have e1 : t - L * round (t / L) = L * (t / L - round (t / L)) := by field_simp
  have e2 : t - n * L = L * (t / L - n) := by field_simp
  rw [e1, e2, abs_mul, abs_mul, abs_of_pos hL]
  exact mul_le_mul_of_nonneg_left h hL.le

/-- The circular distance is a distance to some point of `Lℤ`. -/
lemma exists_circDist_eq (L t : ℝ) : ∃ n : ℤ, circDist L t = |t - n * L| :=
  ⟨round (t / L), by unfold circDist; congr 1; ring⟩

/-- The circular distance is at most `L/2`. -/
lemma circDist_le_half {L : ℝ} (hL : 0 < L) (t : ℝ) : circDist L t ≤ L / 2 := by
  have hL0 : L ≠ 0 := hL.ne'
  have h := abs_sub_round (t / L)
  unfold circDist
  have e1 : t - L * round (t / L) = L * (t / L - round (t / L)) := by field_simp
  rw [e1, abs_mul, abs_of_pos hL]
  calc L * |t / L - round (t / L)| ≤ L * (1 / 2) := mul_le_mul_of_nonneg_left h hL.le
    _ = L / 2 := by ring

/-- Shifting by a lattice point does not change the circular distance. -/
lemma circDist_add_int_mul_le {L : ℝ} (hL : 0 < L) (t : ℝ) (n : ℤ) :
    circDist L (t + n * L) ≤ circDist L t := by
  obtain ⟨m, hm⟩ := exists_circDist_eq L t
  have h := circDist_le_abs_sub_int_mul hL (t + n * L) (m + n)
  have e : t + n * L - ((m + n : ℤ) : ℝ) * L = t - m * L := by push_cast; ring
  rw [e] at h
  rw [hm]
  exact h

/-- The circular distance is even. -/
lemma circDist_neg {L : ℝ} (hL : 0 < L) (t : ℝ) : circDist L (-t) = circDist L t := by
  have key : ∀ u : ℝ, circDist L (-u) ≤ circDist L u := by
    intro u
    obtain ⟨n, hn⟩ := exists_circDist_eq L u
    have h := circDist_le_abs_sub_int_mul hL (-u) (-n)
    have e : -u - ((-n : ℤ) : ℝ) * L = -(u - n * L) := by push_cast; ring
    rw [e, abs_neg] at h
    rw [hn]
    exact h
  apply le_antisymm (key t)
  have h := key (-t)
  rwa [neg_neg] at h

/-- The weight `w_1` is even. -/
lemma gradWeightOne_neg {s a K L : ℝ} (hL : 0 < L) (t : ℝ) :
    gradWeightOne s a K L (-t) = gradWeightOne s a K L t := by
  unfold gradWeightOne
  rw [circDist_neg hL]

/-- The weight `w_2` is even. -/
lemma gradWeightTwo_neg {s a K L : ℝ} (hL : 0 < L) (t : ℝ) :
    gradWeightTwo s a K L (-t) = gradWeightTwo s a K L t := by
  unfold gradWeightTwo
  rw [circDist_neg hL]

/-- On a segment `[p, q]` with no point of `Lℤ`, the circular distance of each point is at least
the smaller of the circular distances of the endpoints. -/
lemma circDist_ge_min_of_no_lattice {L p q t : ℝ} (hL : 0 < L)
    (hno : ∀ n : ℤ, ¬(p ≤ n * L ∧ n * L ≤ q)) (ht : t ∈ Icc p q) :
    min (circDist L p) (circDist L q) ≤ circDist L t := by
  obtain ⟨n, hn⟩ := exists_circDist_eq L t
  rw [hn]
  by_cases h1 : (n : ℝ) * L < p
  · have hp := circDist_le_abs_sub_int_mul hL p n
    rw [abs_of_pos (by linarith [ht.1] : 0 < p - n * L)] at hp
    rw [abs_of_pos (by linarith [ht.1] : 0 < t - n * L)]
    exact le_trans (min_le_left _ _) (le_trans hp (by linarith [ht.1]))
  · have hq : q < n * L := by
      by_contra hc
      exact hno n ⟨by linarith [not_lt.mp h1, ht.1], not_lt.mp hc⟩
    have hq' := circDist_le_abs_sub_int_mul hL q n
    rw [abs_of_neg (by linarith [ht.2] : q - n * L < 0)] at hq'
    rw [abs_of_neg (by linarith [ht.2] : t - n * L < 0)]
    exact le_trans (min_le_right _ _) (le_trans hq' (by linarith [ht.2]))

/-- The differences part of Lemma 5.7, lattice-free case: on a segment `[p, q]`
with no point of `Lℤ`, the weight `w_1` is at most its larger endpoint value. -/
lemma gradWeightOne_le_max_of_no_lattice {s a K L p q t : ℝ} (hL : 0 < L) (hs1 : s < 1)
    (ha : 0 ≤ a) (hK : 1 ≤ K) (hno : ∀ n : ℤ, ¬(p ≤ n * L ∧ n * L ≤ q)) (ht : t ∈ Icc p q) :
    gradWeightOne s a K L t ≤ max (gradWeightOne s a K L p) (gradWeightOne s a K L q) := by
  have hmin := circDist_ge_min_of_no_lattice hL hno ht
  rcases le_total (circDist L p) (circDist L q) with h | h
  · have h' : circDist L p ≤ circDist L t := by rwa [min_eq_left h] at hmin
    exact le_trans (gradWeightOne_le_of_circDist_le hs1 ha hK h') (le_max_left _ _)
  · have h' : circDist L q ≤ circDist L t := by rwa [min_eq_right h] at hmin
    exact le_trans (gradWeightOne_le_of_circDist_le hs1 ha hK h') (le_max_right _ _)

/-- The weight `w_2` version of `gradWeightOne_le_max_of_no_lattice`. -/
lemma gradWeightTwo_le_max_of_no_lattice {s a K L p q t : ℝ} (hL : 0 < L) (hs1 : s < 1)
    (ha : 0 ≤ a) (hK : 1 ≤ K) (hno : ∀ n : ℤ, ¬(p ≤ n * L ∧ n * L ≤ q)) (ht : t ∈ Icc p q) :
    gradWeightTwo s a K L t ≤ max (gradWeightTwo s a K L p) (gradWeightTwo s a K L q) := by
  have hmin := circDist_ge_min_of_no_lattice hL hno ht
  rcases le_total (circDist L p) (circDist L q) with h | h
  · have h' : circDist L p ≤ circDist L t := by rwa [min_eq_left h] at hmin
    exact le_trans (gradWeightTwo_le_of_circDist_le hs1 ha hK h') (le_max_left _ _)
  · have h' : circDist L q ≤ circDist L t := by rwa [min_eq_right h] at hmin
    exact le_trans (gradWeightTwo_le_of_circDist_le hs1 ha hK h') (le_max_right _ _)

/-- On `[0, L/2]` the weight `w_1` is `max(t, K^{-1})^{-a}` for `t ≤ 1`. -/
lemma gradWeightOne_eq_max {s a K L t : ℝ} (hL : 0 < L) (hK : 1 ≤ K) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (htL : t ≤ L / 2) : gradWeightOne s a K L t = max t K⁻¹ ^ (-a) := by
  unfold gradWeightOne
  rw [circDist_of_mem_Icc hL ht0 htL]
  by_cases h : t < 1
  · simp only [h, ↓reduceIte]
  · have ht : t = 1 := le_antisymm ht1 (not_lt.mp h)
    have hc : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
    simp only [h, ↓reduceIte]
    rw [ht, Real.one_rpow, max_eq_left hc, Real.one_rpow]

/-- On `[1, L/2]` the weight `w_1` is `t^{s-2}`. -/
lemma gradWeightOne_eq_rpow {s a K L t : ℝ} (hL : 0 < L) (ht1 : 1 ≤ t) (htL : t ≤ L / 2) :
    gradWeightOne s a K L t = t ^ (s - 2) := by
  unfold gradWeightOne
  rw [circDist_of_mem_Icc hL (by linarith) htL]
  simp only [show ¬ t < 1 from not_lt.mpr ht1, ↓reduceIte]

/-- The weight `w_1` is interval integrable from the origin on `[0, T]` for `T ≤ L/2`. -/
lemma intervalIntegrable_gradWeightOne {s a K L T : ℝ} (hL : 0 < L) (hK : 1 ≤ K)
    (hT0 : 0 ≤ T) (hTL : T ≤ L / 2) :
    IntervalIntegrable (fun t => gradWeightOne s a K L t) volume 0 T := by
  have hc : 0 < K⁻¹ := inv_pos.mpr (by linarith)
  have hcont1 : Continuous (fun t : ℝ => max t K⁻¹ ^ (-a)) :=
    Continuous.rpow_const (continuous_id.max continuous_const)
      (fun t => Or.inl (ne_of_gt (lt_of_lt_of_le hc (le_max_right _ _))))
  by_cases hT1 : T ≤ 1
  · refine IntervalIntegrable.congr_uIoo (hcont1.intervalIntegrable 0 T) ?_
    intro t ht
    rw [uIoo, min_eq_left hT0, max_eq_right hT0] at ht
    exact (gradWeightOne_eq_max hL hK (le_of_lt ht.1) (le_trans (le_of_lt ht.2) hT1)
      (le_trans (le_of_lt ht.2) hTL)).symm
  · have hT1' : 1 < T := not_le.mp hT1
    have h01 : IntervalIntegrable (fun t => gradWeightOne s a K L t) volume 0 1 := by
      refine IntervalIntegrable.congr_uIoo (hcont1.intervalIntegrable 0 1) ?_
      intro t ht
      rw [uIoo, min_eq_left zero_le_one, max_eq_right zero_le_one] at ht
      exact (gradWeightOne_eq_max hL hK (le_of_lt ht.1) (le_of_lt ht.2)
        (le_trans (le_of_lt ht.2) (by linarith))).symm
    have h1T : IntervalIntegrable (fun t => gradWeightOne s a K L t) volume 1 T := by
      have hcont2 : ContinuousOn (fun t : ℝ => t ^ (s - 2)) (uIcc 1 T) := by
        apply ContinuousOn.rpow_const continuousOn_id
        intro x hx
        left
        rw [uIcc_of_le hT1'.le] at hx
        show x ≠ 0
        exact ne_of_gt (by linarith [hx.1])
      refine IntervalIntegrable.congr_uIoo (hcont2.intervalIntegrable) ?_
      intro t ht
      rw [uIoo, min_eq_left hT1'.le, max_eq_right hT1'.le] at ht
      exact (gradWeightOne_eq_rpow hL (by linarith [ht.1]) (by linarith [ht.2])).symm
    exact h01.trans h1T

/-- The integral `G(T) = ∫_0^T w_1` from the origin in the differences part of Lemma 5.7.
It is used for `T ≤ L/2`, where the circular distance is the identity on `[0, T]`. -/
noncomputable def gradWeightOneIntegral (s a K L T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, gradWeightOne s a K L t

/-- The integral of `max(t, c)^{-a}` from `0` to `T`, for `0 < c ≤ 1`: it is at most
`(1 + 1/(1-a)) T max(T, c)^{-a}`. -/
lemma integral_max_rpow_le {a c T : ℝ} (ha1 : a < 1) (hc0 : 0 < c) (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, max t c ^ (-a) ≤ (1 + 1 / (1 - a)) * T * max T c ^ (-a) := by
  have hk : 0 ≤ 1 / (1 - a) := div_nonneg zero_le_one (by linarith)
  have hcont : Continuous (fun t : ℝ => max t c ^ (-a)) :=
    Continuous.rpow_const (continuous_id.max continuous_const)
      (fun t => Or.inl (ne_of_gt (lt_of_lt_of_le hc0 (le_max_right _ _))))
  rcases le_total T c with hTc | hTc
  · have heq : ∫ t in (0 : ℝ)..T, max t c ^ (-a) = ∫ t in (0 : ℝ)..T, c ^ (-a) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hT] at ht
      simp only [max_eq_right (le_trans ht.2 hTc)]
    rw [heq, max_eq_right hTc, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    have hp : 0 ≤ c ^ (-a) := Real.rpow_nonneg hc0.le _
    nlinarith [mul_nonneg (mul_nonneg hk hT) hp]
  · have h1 : IntervalIntegrable (fun t : ℝ => max t c ^ (-a)) volume 0 c :=
      hcont.intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun t : ℝ => max t c ^ (-a)) volume c T :=
      hcont.intervalIntegrable _ _
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, max_eq_left hTc]
    -- The piece on `[0, c]` is the constant `c^{-a}`.
    have e1 : ∫ t in (0 : ℝ)..c, max t c ^ (-a) = c ^ (1 - a) := by
      have : ∫ t in (0 : ℝ)..c, max t c ^ (-a) = ∫ t in (0 : ℝ)..c, c ^ (-a) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hc0.le] at ht
        simp only [max_eq_right ht.2]
      rw [this, intervalIntegral.integral_const, smul_eq_mul, sub_zero,
        show (1 - a) = 1 + -a by ring, Real.rpow_add hc0, Real.rpow_one]
    -- The piece on `[c, T]` is `t^{-a}`.
    have e2 : ∫ t in c..T, max t c ^ (-a) = ∫ t in c..T, t ^ (-a) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hTc] at ht
      simp only [max_eq_left ht.1]
    have e3 : ∫ t in c..T, t ^ (-a) = (T ^ (1 - a) - c ^ (1 - a)) / (1 - a) := by
      rw [integral_rpow (Or.inl (by linarith))]
      rw [show -a + 1 = 1 - a by ring]
    rw [e1, e2, e3]
    have hY0 : 0 ≤ c ^ (1 - a) := Real.rpow_nonneg hc0.le _
    have hYX : c ^ (1 - a) ≤ T ^ (1 - a) :=
      Real.rpow_le_rpow hc0.le hTc (by linarith)
    have hTpos : 0 < T := lt_of_lt_of_le hc0 hTc
    have hXT : T ^ (1 - a) = T * T ^ (-a) := by
      rw [show (1 - a) = 1 + -a by ring, Real.rpow_add hTpos, Real.rpow_one]
    rw [show (1 + 1 / (1 - a)) * T * T ^ (-a) = (1 + 1 / (1 - a)) * T ^ (1 - a) by
      rw [hXT]; ring]
    rw [div_eq_mul_one_div (T ^ (1 - a) - c ^ (1 - a)) (1 - a),
      show (1 + 1 / (1 - a)) * T ^ (1 - a) = T ^ (1 - a) + T ^ (1 - a) * (1 / (1 - a)) by ring]
    nlinarith [mul_nonneg hY0 hk, hYX]

/-- The differences part of Lemma 5.7: the bound `G(T) ≤ (1 + 1/(1-a)) T max(T, K^{-1})^{-a}`
for `0 ≤ T ≤ 1` and `T ≤ L/2`. -/
lemma gradWeightOneIntegral_le_of_le_one {s a K L T : ℝ} (hL : 0 < L) (ha1 : a < 1) (hK : 1 ≤ K)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (hTL : T ≤ L / 2) :
    gradWeightOneIntegral s a K L T ≤ (1 + 1 / (1 - a)) * T * max T K⁻¹ ^ (-a) := by
  unfold gradWeightOneIntegral
  have heq : ∫ t in (0 : ℝ)..T, gradWeightOne s a K L t = ∫ t in (0 : ℝ)..T, max t K⁻¹ ^ (-a) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT0] at ht
    exact gradWeightOne_eq_max hL hK ht.1 (le_trans ht.2 hT1) (le_trans ht.2 hTL)
  rw [heq]
  exact integral_max_rpow_le ha1 (inv_pos.mpr (by linarith)) hT0

/-- The differences part of Lemma 5.7: the integral `G(T) = ∫_0^T w_1` is bounded
uniformly in `T ∈ [0, L/2]`. -/
lemma gradWeightOneIntegral_le_const {s a K L T : ℝ} (hL : 0 < L) (ha1 : a < 1)
    (hs0 : 0 < s) (hs1 : s < 1) (hK : 1 ≤ K) (hT0 : 0 ≤ T) (hTL : T ≤ L / 2) :
    gradWeightOneIntegral s a K L T ≤ (1 + 1 / (1 - a)) + 1 / (1 - s) := by
  have hc1 : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
  have hk : 0 ≤ 1 / (1 - s) := div_nonneg zero_le_one (by linarith)
  have hk1 : 0 ≤ 1 / (1 - a) := div_nonneg zero_le_one (by linarith)
  by_cases hT1 : T ≤ 1
  · have h := gradWeightOneIntegral_le_of_le_one (s := s) hL ha1 hK hT0 hT1 hTL
    have hM : max T K⁻¹ ≤ 1 := max_le hT1 hc1
    have hMpos : 0 < max T K⁻¹ := lt_of_lt_of_le (inv_pos.mpr (by linarith)) (le_max_right _ _)
    have hTM : T ≤ max T K⁻¹ := le_max_left _ _
    have hp : 0 ≤ max T K⁻¹ ^ (-a) := Real.rpow_nonneg hMpos.le _
    have e : max T K⁻¹ ^ (1 - a) = max T K⁻¹ * max T K⁻¹ ^ (-a) := by
      rw [show (1 - a) = 1 + -a by ring, Real.rpow_add hMpos, Real.rpow_one]
    have hsmall : max T K⁻¹ * max T K⁻¹ ^ (-a) ≤ 1 := by
      rw [← e]; exact Real.rpow_le_one hMpos.le hM (by linarith)
    have hTM' : T * max T K⁻¹ ^ (-a) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_right hTM hp) hsmall
    calc gradWeightOneIntegral s a K L T ≤ (1 + 1 / (1 - a)) * T * max T K⁻¹ ^ (-a) := h
      _ = (1 + 1 / (1 - a)) * (T * max T K⁻¹ ^ (-a)) := by ring
      _ ≤ (1 + 1 / (1 - a)) * 1 := mul_le_mul_of_nonneg_left hTM' (by linarith)
      _ ≤ (1 + 1 / (1 - a)) + 1 / (1 - s) := by linarith
  · have hT1' : 1 < T := not_le.mp hT1
    have hI : IntervalIntegrable (fun t => gradWeightOne s a K L t) volume 0 T :=
      intervalIntegrable_gradWeightOne hL hK hT0 hTL
    have hI1 : IntervalIntegrable (fun t => gradWeightOne s a K L t) volume 0 1 :=
      hI.mono_set (by
        rw [uIcc_of_le zero_le_one, uIcc_of_le hT0]
        exact Icc_subset_Icc le_rfl hT1'.le)
    have hI2 : IntervalIntegrable (fun t => gradWeightOne s a K L t) volume 1 T :=
      hI.mono_set (by
        rw [uIcc_of_le hT1'.le, uIcc_of_le hT0]
        exact Icc_subset_Icc (by linarith) le_rfl)
    have h01 := gradWeightOneIntegral_le_of_le_one (s := s) hL ha1 hK zero_le_one le_rfl
      (by linarith : (1 : ℝ) ≤ L / 2)
    unfold gradWeightOneIntegral at h01 ⊢
    rw [max_eq_left hc1, Real.one_rpow, mul_one, mul_one] at h01
    have hrpow : ∫ t in (1 : ℝ)..T, gradWeightOne s a K L t ≤ 1 / (1 - s) := by
      have heq : ∫ t in (1 : ℝ)..T, gradWeightOne s a K L t = ∫ t in (1 : ℝ)..T, t ^ (s - 2) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hT1'.le] at ht
        exact gradWeightOne_eq_rpow hL ht.1 (le_trans ht.2 hTL)
      rw [heq]
      have := integral_rpow_sub_two_le hs0 hs1 le_rfl hT1'.le
      rwa [Real.one_rpow] at this
    rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
    linarith

/-- Arm bound, on the core interval: if `|ψ'| ≤ C_0 w_1` and `|x| ≤ L/2`, then
`|ψ(x) - ψ(0)| ≤ C_0 G(|x|)`. -/
lemma abs_sub_zero_le_arm_core {s a K L C0 : ℝ} (hL : 0 < L) (hK : 1 ≤ K)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K L t) {x : ℝ} (hx : |x| ≤ L / 2) :
    |ψ x - ψ 0| ≤ C0 * gradWeightOneIntegral s a K L |x| := by
  have hcont : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hdiff : ∀ t, HasDerivAt ψ (deriv ψ t) t := fun t => (hψ.differentiable (by simp) t).hasDerivAt
  rcases le_total 0 x with hx0 | hx0
  · rw [abs_of_nonneg hx0]
    have hxL : x ≤ L / 2 := le_trans (le_abs_self x) hx
    have hFTC : ∫ t in (0 : ℝ)..x, deriv ψ t = ψ x - ψ 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hdiff t)
        (hcont.intervalIntegrable _ _)
    have hI : IntervalIntegrable (fun t => gradWeightOne s a K L t) volume 0 x :=
      intervalIntegrable_gradWeightOne hL hK hx0 hxL
    calc |ψ x - ψ 0| = |∫ t in (0 : ℝ)..x, deriv ψ t| := by rw [hFTC]
      _ ≤ ∫ t in (0 : ℝ)..x, |deriv ψ t| := intervalIntegral.abs_integral_le_integral_abs hx0
      _ ≤ ∫ t in (0 : ℝ)..x, C0 * gradWeightOne s a K L t :=
          intervalIntegral.integral_mono_on hx0 (hcont.abs.intervalIntegrable _ _)
            (hI.const_mul C0) (fun t _ => hbd t)
      _ = C0 * gradWeightOneIntegral s a K L x := by
          rw [intervalIntegral.integral_const_mul]; rfl
  · rw [abs_of_nonpos hx0]
    have hxL : -x ≤ L / 2 := le_trans (neg_le_abs x) hx
    have hFTC : ∫ t in x..(0 : ℝ), deriv ψ t = ψ 0 - ψ x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hdiff t)
        (hcont.intervalIntegrable _ _)
    have hrefl : ∫ t in x..(0 : ℝ), deriv ψ t = ∫ u in (0 : ℝ)..(-x), deriv ψ (-u) := by
      have h := intervalIntegral.integral_comp_neg (a := x) (b := 0) (fun t => deriv ψ (-t))
      simp only [neg_neg, neg_zero] at h
      exact h
    have hI : IntervalIntegrable (fun t => gradWeightOne s a K L t) volume 0 (-x) :=
      intervalIntegrable_gradWeightOne hL hK (by linarith) hxL
    calc |ψ x - ψ 0| = |∫ t in x..(0 : ℝ), deriv ψ t| := by rw [hFTC, abs_sub_comm]
      _ = |∫ u in (0 : ℝ)..(-x), deriv ψ (-u)| := by rw [hrefl]
      _ ≤ ∫ u in (0 : ℝ)..(-x), |deriv ψ (-u)| :=
          intervalIntegral.abs_integral_le_integral_abs (by linarith)
      _ ≤ ∫ u in (0 : ℝ)..(-x), C0 * gradWeightOne s a K L u := by
          apply intervalIntegral.integral_mono_on (by linarith)
          · exact ((hcont.comp continuous_neg).abs).intervalIntegrable _ _
          · exact hI.const_mul C0
          · intro u _
            have h := hbd (-u)
            rwa [gradWeightOne_neg hL u] at h
      _ = C0 * gradWeightOneIntegral s a K L (-x) := by
          rw [intervalIntegral.integral_const_mul]; rfl

/-- Arm bound (differences part of Lemma 5.7): for an `L`-periodic smooth `ψ` with
`|ψ'| ≤ C_0 w_1`, one has `|ψ(r) - ψ(0)| ≤ C_0 G(circDist L r)` for every real `r`. -/
lemma abs_sub_zero_le_arm {s a K L C0 : ℝ} (hL : 0 < L) (hK : 1 ≤ K)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hper : Function.Periodic ψ L)
    (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K L t) (r : ℝ) :
    |ψ r - ψ 0| ≤ C0 * gradWeightOneIntegral s a K L (circDist L r) := by
  obtain ⟨n, hn⟩ := exists_circDist_eq L r
  have hψr : ψ r = ψ (r - n * L) := by
    have h := hper.int_mul n (r - n * L)
    rw [sub_add_cancel] at h
    exact h
  have hle : |r - n * L| ≤ L / 2 := by rw [← hn]; exact circDist_le_half hL r
  rw [hn, hψr]
  exact abs_sub_zero_le_arm_core hL hK hψ hbd hle

end Riesz1

end
