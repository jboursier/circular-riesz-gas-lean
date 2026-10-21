/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ScaleIncrement

/-!
# Block coordinates of the multiscale increments

Part of Lemma 4.4, first part. Fix `N ≥ 2`, a label `i`, a scale
`1 ≤ k ≤ ⌊N/2⌋`, an integer `q`, and `m < q`. Let `K = k_{m+1}` and let `B = J_K(i)` be the block of
`G_m`, with first label `i0` and `L` gaps. This file writes `G_m` as a linear form in the block
coordinates `x_{i0 + r} - ⌊x_{i0}⌋`, `0 ≤ r ≤ L`:

* `blockWeight J j = |J|⁻¹ 1_J(j)` is the normalized indicator of a finite set `J` of labels, so
  `x_i^{[k']} = ∑_{r ≤ L} blockWeight (J_{k'}(i)) (i0 + r) x_{i0 + r}` whenever `J_{k'}(i) ⊆ B`
  (`blockAverage_eq_sum_range`).
* `scaleCoef` is the coefficient `N (w_{low}(r) - w_K(r))` of `G_m`, where `low = 0` for `m = 0` and
  `low = k_m` otherwise (`scaleIncrement_eq_sum_coef`).
* the coefficients sum to zero (`sum_scaleCoef`), so the lifted block shift cancels, and their
  squares satisfy `∑ coef² ≤ 4 N² k^{-m/q}` (`sum_scaleCoef_sq_le`).

The results are stated for every label `i` and every scale. The reflection and mean statements
are in the companion files.
-/

@[expose] public section

open MeasureTheory Finset

namespace Riesz1

variable {N : ℕ+}

/-! ### Integer intervals as ranges of offsets -/

/-- A finite sum over the integer interval `[a, a + n]` is a sum over the offsets `r ∈ {0, …, n}`. -/
theorem sum_Icc_eq_sum_range_int {M : Type*} [AddCommMonoid M] (f : ℤ → M) (a : ℤ) (n : ℕ) :
    ∑ j ∈ Finset.Icc a (a + n), f j = ∑ r ∈ range (n + 1), f (a + r) := by
  refine Finset.sum_nbij' (fun j => (j - a).toNat) (fun r : ℕ => a + (r : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
    omega
  · intro r hr
    simp only [Finset.mem_range, Finset.mem_Icc] at hr ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    omega
  · intro r _
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    congr 1
    omega

/-- The cardinality of the representatives is the span plus one. -/
theorem card_cyclicRep (N : ℕ+) (s : ℕ) (i : ℤ) :
    (cyclicRep N s i).card = cyclicRepSpan N s + 1 := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [cyclicRep, cyclicRepSpan, N.pos]
  · rw [cyclicRep_eq_Icc hs i, Int.card_Icc]
    omega

/-- The representatives are nonempty. -/
theorem cyclicRep_nonempty (N : ℕ+) (s : ℕ) (i : ℤ) : (cyclicRep N s i).Nonempty := by
  rw [← Finset.card_pos, card_cyclicRep]
  omega

/-- The span of the representatives is less than `N` when `2s ≤ N`. -/
theorem cyclicRepSpan_lt {N : ℕ+} {s : ℕ} (hs : 1 ≤ s) (hsN : 2 * s ≤ (N : ℕ)) :
    cyclicRepSpan N s < (N : ℕ) := by
  unfold cyclicRepSpan
  split_ifs with h
  · exact h
  · omega

/-- The representatives grow with the scale: `J_s(i) ⊆ J_S(i)` for `s ≤ S` and `2S ≤ N`. -/
theorem cyclicRep_subset_of_le {s S : ℕ} (hsS : s ≤ S) (hS : 2 * S ≤ (N : ℕ)) (i : ℤ) :
    cyclicRep N s i ⊆ cyclicRep N S i := by
  unfold cyclicRep
  split_ifs with h1 h2 h2
  · exact Finset.Icc_subset_Icc (by omega) (by omega)
  · exact Finset.Icc_subset_Icc (by omega) (by omega)
  · omega
  · exact Finset.Icc_subset_Icc (by omega) (by omega)

/-! ### Normalized block weights -/

/-- The normalized indicator `|J|⁻¹ 1_J(j)` of a finite set `J` of labels. It is the coefficient of
`x_j` in the average over `J`. -/
noncomputable def blockWeight (J : Finset ℤ) (j : ℤ) : ℝ :=
  if j ∈ J then ((J.card : ℕ) : ℝ)⁻¹ else 0

/-- Averaging a function over a block with normalized weights: for `J ⊆ [a, a + n]`, the weighted sum
over offsets equals the average of `c` over `J`. -/
theorem sum_blockWeight_mul_range {J : Finset ℤ} {a : ℤ} {n : ℕ} (hJ : J ⊆ Finset.Icc a (a + n))
    (c : ℤ → ℝ) :
    ∑ r ∈ range (n + 1), blockWeight J (a + r) * c (a + r) =
      ((J.card : ℕ) : ℝ)⁻¹ * ∑ j ∈ J, c j := by
  rw [← sum_Icc_eq_sum_range_int (fun j => blockWeight J j * c j) a n]
  rw [← Finset.sum_subset hJ (fun j _ hj => by simp [blockWeight, hj])]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp [blockWeight, hj]

/-- The normalized weights over a block sum to one when the set is nonempty. -/
theorem sum_blockWeight_range {J : Finset ℤ} {a : ℤ} {n : ℕ} (hJ : J ⊆ Finset.Icc a (a + n))
    (hne : J.Nonempty) :
    ∑ r ∈ range (n + 1), blockWeight J (a + r) = 1 := by
  have h := sum_blockWeight_mul_range hJ (fun _ => (1 : ℝ))
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h
  rw [h]
  have hcard : ((J.card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 hne).ne'
  field_simp

/-- The squared normalized weights sum to the inverse cardinality. -/
theorem sum_blockWeight_sq_range {J : Finset ℤ} {a : ℤ} {n : ℕ} (hJ : J ⊆ Finset.Icc a (a + n))
    (hne : J.Nonempty) :
    ∑ r ∈ range (n + 1), blockWeight J (a + r) * blockWeight J (a + r) =
      ((J.card : ℕ) : ℝ)⁻¹ := by
  rw [sum_blockWeight_mul_range hJ (blockWeight J)]
  rw [show ∑ j ∈ J, blockWeight J j = 1 by
    simp only [blockWeight]
    rw [Finset.sum_ite_mem, Finset.inter_self]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((J.card : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.2 hne).ne'
    field_simp]
  ring

/-! ### Averages in block coordinates -/

/-- The average `x_i^{[k']}` over the representatives of a scale `k' ≤ K`, written as a weighted sum
over the offsets `r ≤ L` of the block of scale `K`, where `K ≥ 1` and `2K ≤ N`. -/
theorem blockAverage_eq_sum_range (X : Configuration N) (i : ℤ) {s K : ℕ} (hK : 1 ≤ K)
    (hsK : s ≤ K) (hKN : 2 * K ≤ (N : ℕ)) :
    blockAverage X i s =
      ∑ r ∈ range (cyclicRepSpan N K + 1),
        blockWeight (cyclicRep N s i) (cyclicRepStart N K i + r) *
          cyclicLift X (cyclicRepStart N K i + r) := by
  have hsub : cyclicRep N s i ⊆ Finset.Icc (cyclicRepStart N K i)
      (cyclicRepStart N K i + cyclicRepSpan N K) := by
    rw [← cyclicRep_eq_Icc hK i]
    exact cyclicRep_subset_of_le hsK hKN i
  rw [sum_blockWeight_mul_range hsub (cyclicLift X)]
  rfl

/-- The lower scale of the increment `G_m`: it is `0` for `m = 0` (so the lower term is the lift
`x_i`) and `k_m` for `m ≥ 1`. -/
noncomputable def lowScale (k q m : ℕ) : ℕ :=
  if m = 0 then 0 else scaleIndex k q m

/-- The increment `G_m` is the difference of two block averages, with the lower average at scale
`lowScale`. -/
theorem scaleIncrement_eq_lowScale (i : ℤ) (k q m : ℕ) (X : Configuration N) :
    scaleIncrement i k q m X = ((N : ℕ) : ℝ) *
      (blockAverage X i (lowScale k q m) - blockAverage X i (scaleIndex k q (m + 1))) := by
  unfold scaleIncrement lowScale
  by_cases hm : m = 0
  · simp [hm, blockAverage_zero]
  · simp [hm]

/-- The scale index is monotone in `m`, since the base `k ≥ 1`. -/
theorem scaleIndex_mono {k q : ℕ} (hk : 1 ≤ k) {m m' : ℕ} (h : m ≤ m') :
    scaleIndex k q m ≤ scaleIndex k q m' := by
  unfold scaleIndex
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hk' ?_)
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

/-- The scale index is at most the real power `k^{m/q}`. -/
theorem scaleIndex_le_rpow {k q m : ℕ} :
    (scaleIndex k q m : ℝ) ≤ (k : ℝ) ^ ((m : ℝ) / q) :=
  Nat.floor_le (by positivity)

/-- The lower scale is at most the upper scale `k_{m+1}`. -/
theorem lowScale_le {k q m : ℕ} (hk : 1 ≤ k) : lowScale k q m ≤ scaleIndex k q (m + 1) := by
  unfold lowScale
  split_ifs with hm
  · exact Nat.zero_le _
  · exact scaleIndex_mono hk (by omega)

/-! ### Coefficients of the increments -/

/-- The coefficient `N (w_{low}(r) - w_{k_{m+1}}(r))` of the block coordinate `r` in `G_m`, where
`w_{k'}(r) = blockWeight (J_{k'}(i)) (i0 + r)` and `i0` is the first label of `J_{k_{m+1}}(i)`. -/
noncomputable def scaleCoef (N : ℕ+) (i : ℤ) (k q m : ℕ) (r : ℕ) : ℝ :=
  ((N : ℕ) : ℝ) *
    (blockWeight (cyclicRep N (lowScale k q m) i)
        (cyclicRepStart N (scaleIndex k q (m + 1)) i + r) -
      blockWeight (cyclicRep N (scaleIndex k q (m + 1)) i)
        (cyclicRepStart N (scaleIndex k q (m + 1)) i + r))

/-- The increment `G_m` is the linear form `∑_{r ≤ L} coef_r x_{i0 + r}` in the lifts of the block. -/
theorem scaleIncrement_eq_sum_coef (i : ℤ) {k q m : ℕ} (hk : 1 ≤ k) (hkN : 2 * k ≤ (N : ℕ))
    (hm : m < q) (X : Configuration N) :
    scaleIncrement i k q m X =
      ∑ r ∈ range (cyclicRepSpan N (scaleIndex k q (m + 1)) + 1),
        scaleCoef N i k q m r * cyclicLift X (cyclicRepStart N (scaleIndex k q (m + 1)) i + r) := by
  have hK : 1 ≤ scaleIndex k q (m + 1) := one_le_scaleIndex hk
  have hKk : scaleIndex k q (m + 1) ≤ k := (scaleIndex_mem hk (by omega) (by omega)).2
  have hKN : 2 * scaleIndex k q (m + 1) ≤ (N : ℕ) := by omega
  have hlow : lowScale k q m ≤ scaleIndex k q (m + 1) := lowScale_le hk
  rw [scaleIncrement_eq_lowScale, blockAverage_eq_sum_range X i hK hlow hKN,
    blockAverage_eq_sum_range X i hK le_rfl hKN, mul_sub, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold scaleCoef
  ring

/-- The coefficients sum to zero, so that the increment is invariant under a common shift of the
block lifts. -/
theorem sum_scaleCoef (i : ℤ) {k q m : ℕ} (hk : 1 ≤ k) (hkN : 2 * k ≤ (N : ℕ)) (hm : m < q) :
    ∑ r ∈ range (cyclicRepSpan N (scaleIndex k q (m + 1)) + 1), scaleCoef N i k q m r = 0 := by
  have hK : 1 ≤ scaleIndex k q (m + 1) := one_le_scaleIndex hk
  have hKk : scaleIndex k q (m + 1) ≤ k := (scaleIndex_mem hk (by omega) (by omega)).2
  have hKN : 2 * scaleIndex k q (m + 1) ≤ (N : ℕ) := by omega
  have hlow : lowScale k q m ≤ scaleIndex k q (m + 1) := lowScale_le hk
  have hsub : cyclicRep N (lowScale k q m) i ⊆ Finset.Icc (cyclicRepStart N (scaleIndex k q (m + 1)) i)
      (cyclicRepStart N (scaleIndex k q (m + 1)) i + cyclicRepSpan N (scaleIndex k q (m + 1))) := by
    rw [← cyclicRep_eq_Icc hK i]
    exact cyclicRep_subset_of_le hlow hKN i
  have hsubK : cyclicRep N (scaleIndex k q (m + 1)) i ⊆ Finset.Icc
      (cyclicRepStart N (scaleIndex k q (m + 1)) i)
      (cyclicRepStart N (scaleIndex k q (m + 1)) i + cyclicRepSpan N (scaleIndex k q (m + 1))) :=
    (cyclicRep_eq_Icc hK i).subset
  unfold scaleCoef
  rw [← mul_sum, Finset.sum_sub_distrib,
    sum_blockWeight_range hsub (cyclicRep_nonempty N _ i),
    sum_blockWeight_range hsubK (cyclicRep_nonempty N _ i)]
  ring

/-- The lower scale has at least `k^{m/q}` labels: for `m = 0` the lower average is the single lift,
and for `m ≥ 1`, `|J_{k_m}(i)| ≥ 2 k_m ≥ k^{m/q}`. -/
theorem rpow_le_card_lowScale {k q m : ℕ} (hk : 1 ≤ k) (hkN : 2 * k ≤ (N : ℕ))
    (hm : m ≤ q) (i : ℤ) :
    (k : ℝ) ^ ((m : ℝ) / q) ≤ ((cyclicRep N (lowScale k q m) i).card : ℝ) := by
  unfold lowScale
  split_ifs with hm0
  · subst hm0
    rw [card_cyclicRep]
    simp [cyclicRepSpan, N.pos]
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    set x : ℝ := (k : ℝ) ^ ((m : ℝ) / q) with hx
    have hx1 : 1 ≤ x := Real.one_le_rpow hk' (by positivity)
    have hfl : 1 ≤ scaleIndex k q m := Nat.le_floor (by exact_mod_cast hx1)
    have hKk : scaleIndex k q m ≤ k := (scaleIndex_mem hk (by omega) (by omega)).2
    have hKN : 2 * scaleIndex k q m ≤ (N : ℕ) := by omega
    have hfloor : x < (scaleIndex k q m : ℝ) + 1 := Nat.lt_floor_add_one x
    have hfl' : (1 : ℝ) ≤ (scaleIndex k q m : ℝ) := by exact_mod_cast hfl
    have hcard : 2 * scaleIndex k q m ≤ cyclicRepSpan N (scaleIndex k q m) + 1 := by
      unfold cyclicRepSpan
      split_ifs with h
      · omega
      · omega
    rw [card_cyclicRep]
    have : (2 * scaleIndex k q m : ℝ) ≤ ((cyclicRepSpan N (scaleIndex k q m) + 1 : ℕ) : ℝ) := by
      exact_mod_cast hcard
    push_cast at this ⊢
    linarith

/-- The squared coefficients are bounded: `∑_r coef_r² ≤ 4 N² / |J_{low}(i)|`. -/
theorem sum_scaleCoef_sq_le (i : ℤ) {k q m : ℕ} (hk : 1 ≤ k) (hkN : 2 * k ≤ (N : ℕ))
    (hm : m < q) :
    ∑ r ∈ range (cyclicRepSpan N (scaleIndex k q (m + 1)) + 1), scaleCoef N i k q m r ^ 2 ≤
      4 * ((N : ℕ) : ℝ) ^ 2 * ((cyclicRep N (lowScale k q m) i).card : ℝ)⁻¹ := by
  have hK : 1 ≤ scaleIndex k q (m + 1) := one_le_scaleIndex hk
  have hKk : scaleIndex k q (m + 1) ≤ k := (scaleIndex_mem hk (by omega) (by omega)).2
  have hKN : 2 * scaleIndex k q (m + 1) ≤ (N : ℕ) := by omega
  have hlow : lowScale k q m ≤ scaleIndex k q (m + 1) := lowScale_le hk
  have hsub : cyclicRep N (lowScale k q m) i ⊆ Finset.Icc (cyclicRepStart N (scaleIndex k q (m + 1)) i)
      (cyclicRepStart N (scaleIndex k q (m + 1)) i + cyclicRepSpan N (scaleIndex k q (m + 1))) := by
    rw [← cyclicRep_eq_Icc hK i]
    exact cyclicRep_subset_of_le hlow hKN i
  have hsubK : cyclicRep N (scaleIndex k q (m + 1)) i ⊆ Finset.Icc
      (cyclicRepStart N (scaleIndex k q (m + 1)) i)
      (cyclicRepStart N (scaleIndex k q (m + 1)) i + cyclicRepSpan N (scaleIndex k q (m + 1))) :=
    (cyclicRep_eq_Icc hK i).subset
  have hcardle : ((cyclicRep N (lowScale k q m) i).card : ℝ) ≤
      ((cyclicRep N (scaleIndex k q (m + 1)) i).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (cyclicRep_subset_of_le hlow hKN i)
  have hpos : (0 : ℝ) < ((cyclicRep N (lowScale k q m) i).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 (cyclicRep_nonempty N _ i)
  have hposK : (0 : ℝ) < ((cyclicRep N (scaleIndex k q (m + 1)) i).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 (cyclicRep_nonempty N _ i)
  -- pointwise: (a - b)² ≤ 2a² + 2b²
  have hpt : ∀ r ∈ range (cyclicRepSpan N (scaleIndex k q (m + 1)) + 1),
      scaleCoef N i k q m r ^ 2 ≤
        2 * ((N : ℕ) : ℝ) ^ 2 *
          (blockWeight (cyclicRep N (lowScale k q m) i)
              (cyclicRepStart N (scaleIndex k q (m + 1)) i + r) *
            blockWeight (cyclicRep N (lowScale k q m) i)
              (cyclicRepStart N (scaleIndex k q (m + 1)) i + r) +
          blockWeight (cyclicRep N (scaleIndex k q (m + 1)) i)
              (cyclicRepStart N (scaleIndex k q (m + 1)) i + r) *
            blockWeight (cyclicRep N (scaleIndex k q (m + 1)) i)
              (cyclicRepStart N (scaleIndex k q (m + 1)) i + r)) := by
    intro r _
    unfold scaleCoef
    have h := sq_nonneg
      (blockWeight (cyclicRep N (lowScale k q m) i)
          (cyclicRepStart N (scaleIndex k q (m + 1)) i + r) +
        blockWeight (cyclicRep N (scaleIndex k q (m + 1)) i)
          (cyclicRepStart N (scaleIndex k q (m + 1)) i + r))
    have hN2 : (0 : ℝ) ≤ ((N : ℕ) : ℝ) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hN2 h]
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← mul_sum, Finset.sum_add_distrib, sum_blockWeight_sq_range hsub (cyclicRep_nonempty N _ i),
    sum_blockWeight_sq_range hsubK (cyclicRep_nonempty N _ i)]
  have hinv : ((cyclicRep N (scaleIndex k q (m + 1)) i).card : ℝ)⁻¹ ≤
      ((cyclicRep N (lowScale k q m) i).card : ℝ)⁻¹ :=
    inv_anti₀ hpos hcardle
  have hN2 : (0 : ℝ) ≤ ((N : ℕ) : ℝ) ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hinv hN2]

end Riesz1

end
