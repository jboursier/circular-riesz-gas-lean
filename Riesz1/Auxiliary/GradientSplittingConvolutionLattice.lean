/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingZWeights
public import Riesz1.Auxiliary.GradientSplittingZArc
public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Lattice sums of the gradient-splitting weights

The convolution part of Lemma 5.7, the three lattice bounds
for the weights `w_1`, `w_2` on the circle `(N/K)𝕋`. Throughout, `N ≥ 2` is a natural number,
`K ≥ 1` is real, and the circle `(N/K)𝕋` is the image of `N𝕋` under division by `K`. Since
`circDist (N/K) (x/K) = circDist N x / K`, the weight at the point `(z + k)/K` depends only on
the circular distance `circDist N (z + k)`.

The sums are controlled by a packing argument: for each integer shell `[m, m+1)` of distances,
at most two of the points `z + k`, `0 ≤ k < N`, lie in it.
-/

@[expose] public section

namespace Riesz1

section Circle

lemma circDist_le_abs_sub_int {L : ℝ} (hL : 0 < L) (x : ℝ) (n : ℤ) :
    circDist L x ≤ |x - L * n| := by
  have hL0 : L ≠ 0 := hL.ne'
  have h := round_le (x / L) n
  have e1 : x - L * round (x / L) = L * (x / L - round (x / L)) := by
    field_simp
  have e2 : x - L * n = L * (x / L - n) := by
    field_simp
  unfold circDist
  rw [e1, e2, abs_mul, abs_mul, abs_of_pos hL]
  exact mul_le_mul_of_nonneg_left h hL.le

lemma circDist_neg_le {L : ℝ} (hL : 0 < L) (x : ℝ) : circDist L (-x) ≤ circDist L x := by
  have h := circDist_le_abs_sub_int hL (-x) (-round (x / L))
  have e : -x - L * (((-round (x / L) : ℤ)) : ℝ) = -(x - L * round (x / L)) := by
    push_cast
    ring
  rw [e, abs_neg] at h
  exact h

lemma circDist_triangle {L : ℝ} (hL : 0 < L) (x y : ℝ) :
    circDist L (x + y) ≤ circDist L x + circDist L y := by
  have h := circDist_le_abs_sub_int hL (x + y) (round (x / L) + round (y / L))
  have e : x + y - L * (((round (x / L) + round (y / L) : ℤ)) : ℝ)
      = (x - L * round (x / L)) + (y - L * round (y / L)) := by
    push_cast
    ring
  rw [e] at h
  exact h.trans (abs_add_le _ _)

/-- The scaling identity: the circular distance on `(N/K)𝕋` of `x/K` is `circDist N x / K`. -/
lemma circDist_scale {K : ℝ} (hK : 0 < K) (N x : ℝ) :
    circDist (N / K) (x / K) = circDist N x / K := by
  unfold circDist
  rw [div_div_div_cancel_right₀ hK.ne']
  rw [show x / K - N / K * (round (x / N) : ℝ) = (x - N * round (x / N)) / K by ring,
    abs_div, abs_of_pos hK]

/-- The weight `w_2` depends on `u` only through its circular distance. -/
lemma gradWeightTwo_congr {s a K L u v : ℝ} (h : circDist L u = circDist L v) :
    gradWeightTwo s a K L u = gradWeightTwo s a K L v := by
  unfold gradWeightTwo
  rw [h]

/-- The weight `w_1` depends on `u` only through its circular distance. -/
lemma gradWeightOne_congr {s a K L u v : ℝ} (h : circDist L u = circDist L v) :
    gradWeightOne s a K L u = gradWeightOne s a K L v := by
  unfold gradWeightOne
  rw [h]

end Circle

section Packing

/-- Points `z + k` with `0 ≤ k < N` whose signed representative `z + k - N round((z+k)/N)` lies
in a set of diameter below one: at most one such `k`. -/
lemma card_filter_packing_le_one (N : ℕ) (hN : 0 < N) (z : ℝ) (P : ℝ → Prop) [DecidablePred P]
    (hP : ∀ x y, P x → P y → |x - y| < 1) :
    ((Finset.range N).filter
      (fun k : ℕ => P (z + k - (N : ℝ) * round ((z + k) / N)))).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_filter, Finset.mem_range] at ha hb
  have hlt := hP _ _ ha.2 hb.2
  have hq : ((((a : ℤ) - b - (N : ℤ) * (round ((z + a) / N) - round ((z + b) / N))) : ℤ) : ℝ)
      = (z + a - N * round ((z + a) / N)) - (z + b - N * round ((z + b) / N)) := by
    push_cast
    ring
  have key : ∀ q : ℤ, |(q : ℝ)| < 1 → q = 0 := by
    intro q hq1
    rw [abs_lt] at hq1
    obtain ⟨h1, h2⟩ := hq1
    have h1' : (-1 : ℤ) < q := by exact_mod_cast h1
    have h2' : q < 1 := by exact_mod_cast h2
    omega
  have hq0 := key ((a : ℤ) - b - (N : ℤ) * (round ((z + a) / N) - round ((z + b) / N)))
    (by rw [hq]; exact hlt)
  have hj : (a : ℤ) - b = (N : ℤ) * (round ((z + a) / N) - round ((z + b) / N)) := by
    linarith
  have hNz : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have ha0 : (0 : ℤ) ≤ a := by positivity
  have hb0 : (0 : ℤ) ≤ b := by positivity
  have haN : (a : ℤ) < N := by exact_mod_cast ha.1
  have hbN : (b : ℤ) < N := by exact_mod_cast hb.1
  have hr : round ((z + a) / N) - round ((z + b) / N) = 0 := by
    rcases lt_trichotomy (round ((z + a) / N) - round ((z + b) / N)) 0 with h | h | h
    · have h' : round ((z + a) / N) - round ((z + b) / N) ≤ -1 := by omega
      have : (N : ℤ) * (round ((z + a) / N) - round ((z + b) / N)) ≤ -N := by nlinarith
      linarith
    · exact h
    · have h' : 1 ≤ round ((z + a) / N) - round ((z + b) / N) := by omega
      have : (N : ℤ) ≤ (N : ℤ) * (round ((z + a) / N) - round ((z + b) / N)) := by nlinarith
      linarith
  rw [hr, mul_zero] at hj
  omega

/-- Each shell `m ≤ circDist N (z + k) < m + 1` contains at most two of the points `z + k`,
`0 ≤ k < N`: one on each side of the lattice `N ℤ`. -/
lemma card_shell_le_two (N : ℕ) (hN : 0 < N) (z : ℝ) (m : ℕ) :
    ((Finset.range N).filter (fun k : ℕ => ⌊circDist (N : ℝ) (z + k)⌋₊ = m)).card ≤ 2 := by
  classical
  have hA := card_filter_packing_le_one N hN z (fun x : ℝ => (m : ℝ) ≤ x ∧ x < m + 1)
    (fun x y hx hy => by
      rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2])
  have hB := card_filter_packing_le_one N hN z
    (fun x : ℝ => -((m : ℝ) + 1) < x ∧ x ≤ -(m : ℝ))
    (fun x y hx hy => by
      rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2])
  have hsub : (Finset.range N).filter (fun k : ℕ => ⌊circDist (N : ℝ) (z + k)⌋₊ = m) ⊆
      (Finset.range N).filter
          (fun k : ℕ => (m : ℝ) ≤ z + k - N * round ((z + k) / N) ∧
            z + k - N * round ((z + k) / N) < m + 1) ∪
        (Finset.range N).filter
          (fun k : ℕ => -((m : ℝ) + 1) < z + k - N * round ((z + k) / N) ∧
            z + k - N * round ((z + k) / N) ≤ -(m : ℝ)) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    obtain ⟨hk1, hk2⟩ := hk
    have hfl := (Nat.floor_eq_iff (circDist_nonneg (L := (N : ℝ)) (z + k))).mp hk2
    have hT : circDist (N : ℝ) (z + k) = |z + k - N * round ((z + k) / N)| := rfl
    rw [hT] at hfl
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases le_or_gt 0 (z + k - N * round ((z + k) / N)) with h0 | h0
    · left
      rw [abs_of_nonneg h0] at hfl
      exact ⟨hk1, hfl.1, hfl.2⟩
    · right
      rw [abs_of_neg h0] at hfl
      exact ⟨hk1, by linarith [hfl.2], by linarith [hfl.1]⟩
  calc ((Finset.range N).filter (fun k : ℕ => ⌊circDist (N : ℝ) (z + k)⌋₊ = m)).card
      ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 1 + 1 := add_le_add hA hB
    _ = 2 := by norm_num

end Packing
section Shell

/-- Summing a nonincreasing nonnegative `φ` over the points `z + k`, `0 ≤ k < N`, along the
distances `circDist N (z + k)`: each shell contributes at most twice its value at the left
endpoint, so the sum is at most twice the sum of `φ` over the integers `0, …, ⌊N/2⌋`. -/
lemma sum_shell_le (N : ℕ) (hN : 0 < N) (z : ℝ) (G φ : ℝ → ℝ)
    (hG : ∀ x, G x = φ (circDist (N : ℝ) x))
    (hφ0 : ∀ x : ℝ, 0 ≤ x → x ≤ (N : ℝ) / 2 → 0 ≤ φ x)
    (hφa : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ (N : ℝ) / 2 → φ y ≤ φ x) :
    ∑ k ∈ Finset.range N, G (z + k) ≤ 2 * ∑ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1), φ m := by
  classical
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmem : ∀ k ∈ Finset.range N,
      ⌊circDist (N : ℝ) (z + k)⌋₊ ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1) := by
    intro k _
    rw [Finset.mem_range]
    have h1 : ((⌊circDist (N : ℝ) (z + k)⌋₊ : ℕ) : ℝ) ≤ circDist (N : ℝ) (z + k) :=
      Nat.floor_le (circDist_nonneg _ _)
    have h3 := Nat.le_floor (h1.trans (circDist_le_half hNR (z + k)))
    omega
  have hbound : ∀ k ∈ Finset.range N,
      G (z + k) ≤ φ ((⌊circDist (N : ℝ) (z + k)⌋₊ : ℕ) : ℝ) := by
    intro k _
    rw [hG]
    exact hφa _ _ (Nat.cast_nonneg _) (Nat.floor_le (circDist_nonneg _ _))
      (circDist_le_half hNR (z + k))
  have hmR : ∀ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1), (m : ℝ) ≤ (N : ℝ) / 2 := by
    intro m hm
    have hm' : m ≤ ⌊(N : ℝ) / 2⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    exact (Nat.cast_le.mpr hm').trans (Nat.floor_le (by positivity))
  calc ∑ k ∈ Finset.range N, G (z + k)
      ≤ ∑ k ∈ Finset.range N, φ ((⌊circDist (N : ℝ) (z + k)⌋₊ : ℕ) : ℝ) :=
        Finset.sum_le_sum hbound
    _ = ∑ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1),
          ∑ k ∈ (Finset.range N).filter (fun k : ℕ => ⌊circDist (N : ℝ) (z + k)⌋₊ = m),
            φ ((⌊circDist (N : ℝ) (z + k)⌋₊ : ℕ) : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to hmem _).symm
    _ = ∑ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1),
          ∑ k ∈ (Finset.range N).filter (fun k : ℕ => ⌊circDist (N : ℝ) (z + k)⌋₊ = m),
            φ (m : ℝ) := by
        apply Finset.sum_congr rfl
        intro m _
        apply Finset.sum_congr rfl
        intro k hk
        rw [(Finset.mem_filter.mp hk).2]
    _ = ∑ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1),
          (((Finset.range N).filter (fun k : ℕ => ⌊circDist (N : ℝ) (z + k)⌋₊ = m)).card : ℝ) *
            φ (m : ℝ) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1), 2 * φ (m : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        apply mul_le_mul_of_nonneg_right _ (hφ0 _ (Nat.cast_nonneg _) (hmR m hm))
        exact_mod_cast card_shell_le_two N hN z m
    _ = 2 * ∑ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1), φ (m : ℝ) := by
        rw [Finset.mul_sum]

end Shell

section Sums

/-- The harmonic-type sum `∑_{0 ≤ m ≤ M} 1/max(m,1)` is at most `2 + log M`. -/
lemma sum_inv_max_le (M : ℕ) :
    ∑ m ∈ Finset.range (M + 1), 1 / max (m : ℝ) 1 ≤ 2 + Real.log M := by
  rw [Finset.sum_range_succ']
  have h1 : ∀ i : ℕ, 1 / max ((i + 1 : ℕ) : ℝ) 1 = 1 / ((i : ℝ) + 1) := by
    intro i
    push_cast
    rw [max_eq_left (le_add_of_nonneg_left (Nat.cast_nonneg i))]
  have hsum : ∑ i ∈ Finset.range M, 1 / max ((i + 1 : ℕ) : ℝ) 1
      = ∑ i ∈ Finset.range M, 1 / ((i : ℝ) + 1) :=
    Finset.sum_congr rfl (fun i _ => h1 i)
  have hh := harmonic_le_one_add_log M
  have hcast : ((harmonic M : ℚ) : ℝ) = ∑ i ∈ Finset.range M, 1 / ((i : ℝ) + 1) := by
    simp [harmonic]
  have h0 : 1 / max ((0 : ℕ) : ℝ) 1 = 1 := by simp
  rw [hsum, h0]
  linarith [hh, hcast]

/-- The tail `∑_{J ≤ m} 1/m^2` is at most `2/J` for `J ≥ 1`. -/
lemma sum_tail_inv_sq_le (J : ℕ) (hJ : 1 ≤ J) (M : ℕ) :
    ∑ m ∈ Finset.range M, (if J ≤ m then 1 / (m : ℝ) ^ 2 else 0) ≤ 2 / (J : ℝ) := by
  have key : ∀ n : ℕ, ∑ m ∈ Finset.range (J + n), (if J ≤ m then 1 / (m : ℝ) ^ 2 else 0)
      ≤ 2 / (J : ℝ) - 2 / ((J + n : ℕ) : ℝ) := by
    intro n
    induction n with
    | zero =>
      have h0 : ∑ m ∈ Finset.range (J + 0), (if J ≤ m then 1 / (m : ℝ) ^ 2 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        rw [Finset.mem_range] at hm
        simp [show ¬ (J ≤ m) by omega]
      rw [h0]
      simp
    | succ n ih =>
      rw [show J + (n + 1) = (J + n) + 1 by ring, Finset.sum_range_succ,
        ite_eq_left (show J ≤ J + n by omega)]
      have hx : (1 : ℝ) ≤ ((J + n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ J + n)
      have hcast : ((J + n + 1 : ℕ) : ℝ) = ((J + n : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      set x : ℝ := ((J + n : ℕ) : ℝ) with hxdef
      have hstep : 1 / x ^ 2 ≤ 2 / x - 2 / (x + 1) := by
        rw [div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith [ih]
  have hmono : ∑ m ∈ Finset.range M, (if J ≤ m then 1 / (m : ℝ) ^ 2 else 0)
      ≤ ∑ m ∈ Finset.range (M + J), (if J ≤ m then 1 / (m : ℝ) ^ 2 else 0) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
    intro i _ _
    split_ifs
    · positivity
    · exact le_refl 0
  rw [Nat.add_comm] at hmono
  have hk := key M
  have hpos : (0 : ℝ) ≤ 2 / ((J + M : ℕ) : ℝ) := by positivity
  linarith

lemma natCast_le_half_of_mem {N m : ℕ} (hm : m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1)) :
    (m : ℝ) ≤ (N : ℝ) / 2 := by
  have hm' : m ≤ ⌊(N : ℝ) / 2⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  exact (Nat.cast_le.mpr hm').trans (Nat.floor_le (by positivity))

lemma sum_small_part (c K : ℝ) (hc : 0 ≤ c) (hK : 1 ≤ K) (M : ℕ) :
    ∑ m ∈ Finset.range M, (if (m : ℝ) < K then c / max (m : ℝ) 1 else 0)
      ≤ c * (2 + Real.log K) := by
  rw [← Finset.sum_filter]
  have hsub : (Finset.range M).filter (fun m : ℕ => (m : ℝ) < K) ⊆ Finset.range (⌊K⌋₊ + 1) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_range]
    have : m ≤ ⌊K⌋₊ := Nat.le_floor hm.2.le
    omega
  have hlog : Real.log (⌊K⌋₊ : ℝ) ≤ Real.log K := by
    rcases Nat.eq_zero_or_pos ⌊K⌋₊ with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg hK
    · exact Real.log_le_log (by exact_mod_cast hpos) (Nat.floor_le (by linarith))
  calc ∑ m ∈ (Finset.range M).filter (fun m : ℕ => (m : ℝ) < K), c / max (m : ℝ) 1
      ≤ ∑ m ∈ Finset.range (⌊K⌋₊ + 1), c / max (m : ℝ) 1 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i _ _ => div_nonneg hc (le_trans zero_le_one (le_max_right _ _)))
    _ = c * ∑ m ∈ Finset.range (⌊K⌋₊ + 1), 1 / max (m : ℝ) 1 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun m _ => by ring)
    _ ≤ c * (2 + Real.log (⌊K⌋₊ : ℝ)) := mul_le_mul_of_nonneg_left (sum_inv_max_le _) hc
    _ ≤ c * (2 + Real.log K) := by
        apply mul_le_mul_of_nonneg_left _ hc
        linarith

lemma sum_large_part (K : ℝ) (hK : 1 ≤ K) (M : ℕ) :
    ∑ m ∈ Finset.range M, (if K ≤ (m : ℝ) then K ^ 2 / (m : ℝ) ^ 2 else 0) ≤ 2 * K := by
  have hKc : K ≤ (⌈K⌉₊ : ℝ) := Nat.le_ceil K
  have hJ : 1 ≤ ⌈K⌉₊ := by
    have : (1 : ℝ) ≤ (⌈K⌉₊ : ℝ) := le_trans hK hKc
    exact_mod_cast this
  have hpt : ∀ m ∈ Finset.range M, (if K ≤ (m : ℝ) then K ^ 2 / (m : ℝ) ^ 2 else 0)
      ≤ K ^ 2 * (if ⌈K⌉₊ ≤ m then 1 / (m : ℝ) ^ 2 else 0) := by
    intro m _
    by_cases hm : K ≤ (m : ℝ)
    · rw [ite_eq_left hm, ite_eq_left (Nat.ceil_le.mpr hm), mul_one_div]
    · rw [ite_eq_right hm]
      apply mul_nonneg (sq_nonneg _)
      split_ifs
      · positivity
      · exact le_refl 0
  have hJpos : (0 : ℝ) < ⌈K⌉₊ := by linarith
  calc ∑ m ∈ Finset.range M, (if K ≤ (m : ℝ) then K ^ 2 / (m : ℝ) ^ 2 else 0)
      ≤ ∑ m ∈ Finset.range M, K ^ 2 * (if ⌈K⌉₊ ≤ m then 1 / (m : ℝ) ^ 2 else 0) :=
        Finset.sum_le_sum hpt
    _ = K ^ 2 * ∑ m ∈ Finset.range M, (if ⌈K⌉₊ ≤ m then 1 / (m : ℝ) ^ 2 else 0) := by
        rw [Finset.mul_sum]
    _ ≤ K ^ 2 * (2 / (⌈K⌉₊ : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_tail_inv_sq_le ⌈K⌉₊ hJ M) (sq_nonneg _)
    _ ≤ 2 * K := by
        rw [← mul_div_assoc, div_le_iff₀ hJpos]
        nlinarith [mul_le_mul_of_nonneg_left hKc (by linarith : (0 : ℝ) ≤ K)]

end Sums

section Weights

lemma gradWeightTwo_nonneg_unconditional (s a K L u : ℝ) : 0 ≤ gradWeightTwo s a K L u := by
  unfold gradWeightTwo
  split_ifs
  · exact Real.rpow_nonneg (le_trans (circDist_nonneg _ u) (le_max_left _ _)) _
  · exact Real.rpow_nonneg (circDist_nonneg _ u) _

lemma gradWeightOne_nonneg_unconditional (s a K L u : ℝ) : 0 ≤ gradWeightOne s a K L u := by
  unfold gradWeightOne
  split_ifs
  · exact Real.rpow_nonneg (le_trans (circDist_nonneg _ u) (le_max_left _ _)) _
  · exact Real.rpow_nonneg (circDist_nonneg _ u) _

/-- Monotonicity of `w_2` on `(N/K)𝕋` along the scaled points `x/K`, `0 ≤ x ≤ y ≤ N/2`. -/
lemma gradWeightTwo_anti_scaled {s a K : ℝ} (hs1 : s < 1) (ha : 0 ≤ a) (hK : 1 ≤ K) {N : ℝ}
    (hN : 0 < N) {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hyN : y ≤ N / 2) :
    gradWeightTwo s a K (N / K) (y / K) ≤ gradWeightTwo s a K (N / K) (x / K) := by
  have hK0 : 0 < K := by linarith
  apply gradWeightTwo_le_of_circDist_le hs1 ha hK
  rw [circDist_scale hK0, circDist_scale hK0, circDist_of_mem_Icc hN hx0 (hxy.trans hyN),
    circDist_of_mem_Icc hN (hx0.trans hxy) hyN]
  exact div_le_div_of_nonneg_right hxy hK0.le

/-- Monotonicity of `w_1` on `(N/K)𝕋` along the scaled points `x/K`, `0 ≤ x ≤ y ≤ N/2`. -/
lemma gradWeightOne_anti_scaled {s a K : ℝ} (hs1 : s < 1) (ha : 0 ≤ a) (hK : 1 ≤ K) {N : ℝ}
    (hN : 0 < N) {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hyN : y ≤ N / 2) :
    gradWeightOne s a K (N / K) (y / K) ≤ gradWeightOne s a K (N / K) (x / K) := by
  have hK0 : 0 < K := by linarith
  apply gradWeightOne_le_of_circDist_le hs1 ha hK
  rw [circDist_scale hK0, circDist_scale hK0, circDist_of_mem_Icc hN hx0 (hxy.trans hyN),
    circDist_of_mem_Icc hN (hx0.trans hxy) hyN]
  exact div_le_div_of_nonneg_right hxy hK0.le

lemma rpow_div_neg_eq {M K : ℝ} (hM : 0 ≤ M) (hK : 0 < K) (t : ℝ) :
    (M / K) ^ (-t) = M ^ (-t) * K ^ t := by
  rw [Real.div_rpow hM hK.le, Real.rpow_neg hK.le, div_inv_eq_mul]

lemma max_div_inv_eq {y K : ℝ} (hK : 0 < K) : max (y / K) K⁻¹ = max y 1 / K := by
  rcases le_total y 1 with h | h
  · have hle : y / K ≤ K⁻¹ := by
      rw [div_le_iff₀ hK, inv_mul_cancel₀ hK.ne']
      exact h
    rw [max_eq_right h, max_eq_right hle, inv_eq_one_div]
  · have hle : K⁻¹ ≤ y / K := by
      rw [inv_eq_one_div]
      gcongr
    rw [max_eq_left h, max_eq_left hle]

lemma gradWeightTwo_small_eq {s a K : ℝ} (hK : 1 ≤ K) {N : ℝ} (hN : 0 < N) {y : ℝ}
    (hy0 : 0 ≤ y) (hyN : y ≤ N / 2) (hyK : y < K) :
    gradWeightTwo s a K (N / K) (y / K) = (max y 1) ^ (-(1 + a)) * K ^ (1 + a) := by
  have hK0 : 0 < K := by linarith
  have hc : circDist (N / K) (y / K) = y / K := by
    rw [circDist_scale hK0, circDist_of_mem_Icc hN hy0 hyN]
  unfold gradWeightTwo
  rw [hc, ite_eq_left (show y / K < 1 by rw [div_lt_one hK0]; exact hyK), max_div_inv_eq hK0,
    rpow_div_neg_eq (le_trans zero_le_one (le_max_right y 1)) hK0]

lemma gradWeightOne_small_eq {s a K : ℝ} (hK : 1 ≤ K) {N : ℝ} (hN : 0 < N) {y : ℝ}
    (hy0 : 0 ≤ y) (hyN : y ≤ N / 2) (hyK : y < K) :
    gradWeightOne s a K (N / K) (y / K) = (max y 1) ^ (-a) * K ^ a := by
  have hK0 : 0 < K := by linarith
  have hc : circDist (N / K) (y / K) = y / K := by
    rw [circDist_scale hK0, circDist_of_mem_Icc hN hy0 hyN]
  unfold gradWeightOne
  rw [hc, ite_eq_left (show y / K < 1 by rw [div_lt_one hK0]; exact hyK), max_div_inv_eq hK0,
    rpow_div_neg_eq (le_trans zero_le_one (le_max_right y 1)) hK0]

/-- The weight `w_2` at a point `y/K` with `y < K`, bounded by `K^{1+a}/max(y,1)`. -/
lemma gradWeightTwo_small_le {s a K : ℝ} (ha : 0 ≤ a) (hK : 1 ≤ K) {N : ℝ} (hN : 0 < N)
    {y : ℝ} (hy0 : 0 ≤ y) (hyN : y ≤ N / 2) (hyK : y < K) :
    gradWeightTwo s a K (N / K) (y / K) ≤ K ^ (1 + a) / max y 1 := by
  rw [gradWeightTwo_small_eq hK hN hy0 hyN hyK]
  have hM1 : 1 ≤ max y 1 := le_max_right y 1
  have hMpow : (max y 1) ^ (-(1 + a)) ≤ (max y 1)⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
  have hK1 : 0 ≤ K ^ (1 + a) := Real.rpow_nonneg (by linarith) _
  calc (max y 1) ^ (-(1 + a)) * K ^ (1 + a) ≤ (max y 1)⁻¹ * K ^ (1 + a) :=
        mul_le_mul_of_nonneg_right hMpow hK1
    _ = K ^ (1 + a) / max y 1 := by ring

/-- The weight `w_2` at a point `y/K` with `K ≤ y`, bounded by `K^2/y^2`. -/
lemma gradWeightTwo_large_le {s a K : ℝ} (hs1 : s < 1) (hK : 1 ≤ K) {N : ℝ} (hN : 0 < N)
    {y : ℝ} (hyK : K ≤ y) (hyN : y ≤ N / 2) :
    gradWeightTwo s a K (N / K) (y / K) ≤ K ^ 2 / y ^ 2 := by
  have hK0 : 0 < K := by linarith
  have hy0 : 0 < y := by linarith
  have hx1 : 1 ≤ y / K := by
    rw [le_div_iff₀ hK0]
    linarith
  have hx0 : 0 ≤ y / K := by linarith
  have hc : circDist (N / K) (y / K) = y / K := by
    rw [circDist_scale hK0, circDist_of_mem_Icc hN hy0.le hyN]
  unfold gradWeightTwo
  rw [hc, ite_eq_right (not_lt.mpr hx1)]
  calc (y / K) ^ (s - 3) ≤ (y / K) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    _ = K ^ 2 / y ^ 2 := by
        rw [Real.rpow_neg hx0, Real.rpow_two, div_pow, inv_div]

/-- The weight `w_1` squared at a point `y/K` with `y < K`. -/
lemma gradWeightOne_small_sq_le {s a K : ℝ} (hK : 1 ≤ K) {N : ℝ} (hN : 0 < N)
    {y : ℝ} (hy0 : 0 ≤ y) (hyN : y ≤ N / 2) (hyK : y < K) :
    gradWeightOne s a K (N / K) (y / K) ^ 2 ≤ (K ^ (2 * a) + K) / max y 1 := by
  rw [gradWeightOne_small_eq hK hN hy0 hyN hyK]
  have hK0 : 0 < K := by linarith
  have hM1 : 1 ≤ max y 1 := le_max_right y 1
  have hM0 : 0 < max y 1 := by linarith
  have hMK : max y 1 ≤ K := max_le hyK.le hK
  have hq2 : (K ^ a) ^ 2 = K ^ (2 * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
    congr 1
    push_cast
    ring
  have hpM : ((max y 1) ^ (-a)) ^ 2 * max y 1 = (max y 1) ^ (1 - 2 * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM0.le,
      show (1 : ℝ) - 2 * a = -a * ((2 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.rpow_add hM0, Real.rpow_one]
  have hgW : ((max y 1) ^ (-a) * K ^ a) ^ 2 * max y 1 = (K ^ a) ^ 2 * (max y 1) ^ (1 - 2 * a) := by
    rw [mul_pow, ← hpM]
    ring
  rw [le_div_iff₀ hM0, hgW, ← hq2]
  rcases le_total a (1 / 2) with h | h
  · have h1 : (max y 1) ^ (1 - 2 * a) ≤ K ^ (1 - 2 * a) :=
      Real.rpow_le_rpow hM0.le hMK (by linarith)
    have h2 : (K ^ a) ^ 2 * K ^ (1 - 2 * a) = K := by
      rw [hq2, ← Real.rpow_add hK0, show 2 * a + (1 - 2 * a) = (1 : ℝ) by ring, Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg (K ^ a)), sq_nonneg (K ^ a)]
  · have h1 : (max y 1) ^ (1 - 2 * a) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hM1 (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg (K ^ a)), sq_nonneg (K ^ a)]

/-- The weight `w_1` squared at a point `y/K` with `K ≤ y`, bounded by `K^2/y^2`. -/
lemma gradWeightOne_large_sq_le {s a K : ℝ} (hs1 : s < 1) (hK : 1 ≤ K) {N : ℝ} (hN : 0 < N)
    {y : ℝ} (hyK : K ≤ y) (hyN : y ≤ N / 2) :
    gradWeightOne s a K (N / K) (y / K) ^ 2 ≤ K ^ 2 / y ^ 2 := by
  have hK0 : 0 < K := by linarith
  have hy0 : 0 < y := by linarith
  have hx1 : 1 ≤ y / K := by
    rw [le_div_iff₀ hK0]
    linarith
  have hx0 : 0 ≤ y / K := by linarith
  have hc : circDist (N / K) (y / K) = y / K := by
    rw [circDist_scale hK0, circDist_of_mem_Icc hN hy0.le hyN]
  unfold gradWeightOne
  rw [hc, ite_eq_right (not_lt.mpr hx1)]
  calc ((y / K) ^ (s - 2)) ^ 2 = (y / K) ^ ((s - 2) * 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
        norm_num
    _ ≤ (y / K) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    _ = K ^ 2 / y ^ 2 := by
        rw [Real.rpow_neg hx0, Real.rpow_two, div_pow, inv_div]

/-- The ratio bound for `w_2`, at the level of the distance function: halving the circular
distance multiplies the weight by at most `64 · 2^a`. -/
lemma gradWeightTwo_half_le {s a K : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 ≤ a) (hK : 1 ≤ K)
    {t : ℝ} :
    (if t / 2 < 1 then max (t / 2) K⁻¹ ^ (-(1 + a)) else (t / 2) ^ (s - 3)) ≤
      64 * 2 ^ a * (if t < 1 then max t K⁻¹ ^ (-(1 + a)) else t ^ (s - 3)) := by
  have hK0 : 0 < K⁻¹ := inv_pos.mpr (by linarith)
  have h2a : 1 ≤ (2 : ℝ) ^ a := Real.one_le_rpow (by norm_num) ha
  have hpow1 : (2 : ℝ) ^ (1 + a) = 2 * 2 ^ a := by
    rw [Real.rpow_add (show (0 : ℝ) < 2 by norm_num), Real.rpow_one]
  have hpow3 : (1 / 8 : ℝ) ≤ (2 : ℝ) ^ (s - 3) := by
    have h1 : (2 : ℝ) ^ (-3 : ℝ) ≤ (2 : ℝ) ^ (s - 3) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (2 : ℝ) ^ (-3 : ℝ) = 1 / 8 := by
      rw [Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num)]
      norm_num
    rw [← h2]
    exact h1
  by_cases ht1 : t < 1
  · rw [ite_eq_left (show t / 2 < 1 by linarith), ite_eq_left ht1]
    have hx0 : 0 < max t K⁻¹ := lt_of_lt_of_le hK0 (le_max_right _ _)
    have hhalf : max t K⁻¹ / 2 ≤ max (t / 2) K⁻¹ := by
      rcases le_total t K⁻¹ with h | h
      · rw [max_eq_right h]
        have := le_max_right (t / 2) K⁻¹
        linarith
      · rw [max_eq_left h]
        have := le_max_left (t / 2) K⁻¹
        linarith
    have hmono : max (t / 2) K⁻¹ ^ (-(1 + a)) ≤ (max t K⁻¹ / 2) ^ (-(1 + a)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hhalf (by linarith)
    have hdiv : (max t K⁻¹ / 2) ^ (-(1 + a)) = 2 * 2 ^ a * (max t K⁻¹) ^ (-(1 + a)) := by
      rw [Real.div_rpow hx0.le (show (0 : ℝ) ≤ 2 by norm_num),
        Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num) (1 + a), div_inv_eq_mul, hpow1]
      ring
    have hnonneg : 0 ≤ (max t K⁻¹) ^ (-(1 + a)) := Real.rpow_nonneg hx0.le _
    calc max (t / 2) K⁻¹ ^ (-(1 + a)) ≤ (max t K⁻¹ / 2) ^ (-(1 + a)) := hmono
      _ = 2 * 2 ^ a * (max t K⁻¹) ^ (-(1 + a)) := hdiv
      _ ≤ 64 * 2 ^ a * (max t K⁻¹) ^ (-(1 + a)) := by
          apply mul_le_mul_of_nonneg_right _ hnonneg
          nlinarith
  · rw [ite_eq_right ht1]
    have ht1' : 1 ≤ t := not_lt.mp ht1
    by_cases ht2 : t < 2
    · rw [ite_eq_left (show t / 2 < 1 by linarith)]
      have hge : (1 / 2 : ℝ) ≤ max (t / 2) K⁻¹ := le_trans (by linarith) (le_max_left _ _)
      have hLHS : max (t / 2) K⁻¹ ^ (-(1 + a)) ≤ (1 / 2 : ℝ) ^ (-(1 + a)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hge (by linarith)
      have hval : (1 / 2 : ℝ) ^ (-(1 + a)) = 2 * 2 ^ a := by
        rw [one_div, Real.inv_rpow (show (0 : ℝ) ≤ 2 by norm_num),
          Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num), inv_inv, hpow1]
      have hRHS : (1 / 8 : ℝ) ≤ t ^ (s - 3) := by
        have h1 : (2 : ℝ) ^ (s - 3) ≤ t ^ (s - 3) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) ht2.le (by linarith)
        linarith
      calc max (t / 2) K⁻¹ ^ (-(1 + a)) ≤ 2 * 2 ^ a := hLHS.trans hval.le
        _ ≤ 64 * 2 ^ a * (1 / 8) := by linarith
        _ ≤ 64 * 2 ^ a * t ^ (s - 3) := mul_le_mul_of_nonneg_left hRHS (by positivity)
    · rw [ite_eq_right (not_lt.mpr (show 1 ≤ t / 2 by linarith))]
      have ht0 : 0 ≤ t := by linarith
      rw [Real.div_rpow ht0 (show (0 : ℝ) ≤ 2 by norm_num)]
      have htpos : 0 ≤ t ^ (s - 3) := Real.rpow_nonneg ht0 _
      have h2pos : 0 < (2 : ℝ) ^ (s - 3) := by positivity
      rw [div_le_iff₀ h2pos]
      have hc : 1 ≤ 64 * 2 ^ a * (2 : ℝ) ^ (s - 3) := by
        have hm := mul_le_mul h2a hpow3 (by norm_num) (by positivity)
        nlinarith
      nlinarith [mul_nonneg htpos (sub_nonneg.mpr hc)]

/-- The ratio bound for `w_2` on the circle `L𝕋`, in terms of two points with circular distances
`t` and `t/2`. -/
lemma gradWeightTwo_ratio {s a K L t u v : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 ≤ a) (hK : 1 ≤ K)
    (hu : circDist L u = t) (hv : circDist L v = t / 2) :
    gradWeightTwo s a K L v ≤ 64 * 2 ^ a * gradWeightTwo s a K L u := by
  unfold gradWeightTwo
  rw [hu, hv]
  exact gradWeightTwo_half_le hs0 hs1 ha hK

end Weights

section Main

/-- Shift bound: a point `z + k` with `circDist N k ≤ circDist N z / 2` has weight `w_2` at most
`64 · 2^a` times the weight at `z`. -/
lemma gradWeightTwo_shift_le {s a K : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 ≤ a) (hK : 1 ≤ K)
    {N : ℝ}
    (hN : 0 < N) (z k : ℝ) (hk : circDist N k ≤ circDist N z / 2) :
    gradWeightTwo s a K (N / K) ((z + k) / K) ≤ 64 * 2 ^ a * gradWeightTwo s a K (N / K) (z / K) := by
  have hK0 : 0 < K := by linarith
  have hr0 : 0 ≤ circDist N z := circDist_nonneg _ z
  have hrN : circDist N z ≤ N / 2 := circDist_le_half hN z
  have htri : circDist N z ≤ circDist N (z + k) + circDist N k := by
    have h := circDist_triangle hN (z + k) (-k)
    rw [circDist_neg hN] at h
    have e : z + k + -k = z := by ring
    rw [e] at h
    exact h
  have hd : circDist N z / 2 ≤ circDist N (z + k) := by linarith
  have hrh : circDist N (circDist N z / 2) = circDist N z / 2 :=
    circDist_of_mem_Icc hN (by linarith) (by linarith)
  have hmono : gradWeightTwo s a K (N / K) ((z + k) / K)
      ≤ gradWeightTwo s a K (N / K) ((circDist N z / 2) / K) := by
    apply gradWeightTwo_le_of_circDist_le hs1 ha hK
    rw [circDist_scale hK0, circDist_scale hK0, hrh]
    exact div_le_div_of_nonneg_right hd hK0.le
  have hratio : gradWeightTwo s a K (N / K) ((circDist N z / 2) / K)
      ≤ 64 * 2 ^ a * gradWeightTwo s a K (N / K) (z / K) := by
    apply gradWeightTwo_ratio hs0 hs1 ha hK
    · rw [circDist_scale hK0]
    · rw [circDist_scale hK0, hrh]
      ring
  exact hmono.trans hratio

lemma one_div_rpow_le_two_rpow {p e r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r)
    (h : r < 2 * e) : 1 / (1 + e) ^ p ≤ 2 ^ p / (1 + r) ^ p := by
  have h1 : (1 + r) ^ p ≤ 2 ^ p * (1 + e) ^ p := by
    rw [← Real.mul_rpow (show (0 : ℝ) ≤ 2 by norm_num) (show (0 : ℝ) ≤ 1 + e by linarith)]
    exact Real.rpow_le_rpow (by linarith) (by linarith) hp
  have hD : 0 < (1 + e) ^ p := Real.rpow_pos_of_pos (by linarith) _
  have hE : 0 < (1 + r) ^ p := Real.rpow_pos_of_pos (by linarith) _
  rw [div_le_div_iff₀ hD hE]
  linarith

end Main


section Final

/-- The `w_2` sum over the lattice: `∑_k w_2(z + k) ≤ 8 K^{1+a} (1 + log K)`. -/
lemma sum_gradWeightTwo_le {s a : ℝ} (hs1 : s < 1) (ha : 0 ≤ a) (N : ℕ) (hN : 2 ≤ N) {K : ℝ}
    (hK : 1 ≤ K) (z : ℝ) :
    ∑ k ∈ Finset.range N, gradWeightTwo s a K ((N : ℝ) / K) ((z + k) / K)
      ≤ 8 * K ^ (1 + a) * (1 + Real.log K) := by
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hK0 : 0 < K := by linarith
  have hG : ∀ x : ℝ, gradWeightTwo s a K ((N : ℝ) / K) (x / K)
      = gradWeightTwo s a K ((N : ℝ) / K) (circDist (N : ℝ) x / K) := by
    intro x
    apply gradWeightTwo_congr
    rw [circDist_scale hK0, circDist_scale hK0,
      circDist_of_mem_Icc hNR (circDist_nonneg _ x) (circDist_le_half hNR x)]
  have hS : ∑ k ∈ Finset.range N, gradWeightTwo s a K ((N : ℝ) / K) ((z + k) / K)
      ≤ 2 * ∑ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1),
          gradWeightTwo s a K ((N : ℝ) / K) ((m : ℝ) / K) :=
    sum_shell_le N hNpos z (fun x => gradWeightTwo s a K ((N : ℝ) / K) (x / K))
      (fun d => gradWeightTwo s a K ((N : ℝ) / K) (d / K)) hG
      (fun x _ _ => gradWeightTwo_nonneg_unconditional _ _ _ _ _)
      (fun x y hx hxy hy => gradWeightTwo_anti_scaled hs1 ha hK hNR hx hxy hy)
  have hpt : ∀ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1),
      gradWeightTwo s a K ((N : ℝ) / K) ((m : ℝ) / K)
        ≤ (if (m : ℝ) < K then K ^ (1 + a) / max (m : ℝ) 1 else 0)
          + (if K ≤ (m : ℝ) then K ^ 2 / (m : ℝ) ^ 2 else 0) := by
    intro m hm
    have hmN := natCast_le_half_of_mem (N := N) hm
    by_cases hmK : (m : ℝ) < K
    · rw [ite_eq_left hmK, ite_eq_right (not_le.mpr hmK), add_zero]
      exact gradWeightTwo_small_le ha hK hNR (Nat.cast_nonneg m) hmN hmK
    · rw [ite_eq_right hmK, ite_eq_left (not_lt.mp hmK), zero_add]
      exact gradWeightTwo_large_le hs1 hK hNR (not_lt.mp hmK) hmN
  have hA := sum_small_part (K ^ (1 + a)) K (Real.rpow_nonneg (by linarith) _) hK
    (⌊(N : ℝ) / 2⌋₊ + 1)
  have hB := sum_large_part K hK (⌊(N : ℝ) / 2⌋₊ + 1)
  have hK1 : K ≤ K ^ (1 + a) := by
    calc K = K ^ (1 : ℝ) := (Real.rpow_one K).symm
      _ ≤ K ^ (1 + a) := Real.rpow_le_rpow_of_exponent_le hK (by linarith)
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK
  have hKa : 0 ≤ K ^ (1 + a) := Real.rpow_nonneg (by linarith) _
  calc ∑ k ∈ Finset.range N, gradWeightTwo s a K ((N : ℝ) / K) ((z + k) / K)
      ≤ 2 * ∑ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1),
          gradWeightTwo s a K ((N : ℝ) / K) ((m : ℝ) / K) := hS
    _ ≤ 2 * ∑ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1),
          ((if (m : ℝ) < K then K ^ (1 + a) / max (m : ℝ) 1 else 0)
            + (if K ≤ (m : ℝ) then K ^ 2 / (m : ℝ) ^ 2 else 0)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) (by norm_num)
    _ = 2 * (∑ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1),
          (if (m : ℝ) < K then K ^ (1 + a) / max (m : ℝ) 1 else 0)
          + ∑ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1),
          (if K ≤ (m : ℝ) then K ^ 2 / (m : ℝ) ^ 2 else 0)) := by
        rw [Finset.sum_add_distrib]
    _ ≤ 2 * (K ^ (1 + a) * (2 + Real.log K) + 2 * K) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) (by norm_num)
    _ ≤ 8 * K ^ (1 + a) * (1 + Real.log K) := by
        nlinarith [mul_nonneg hKa hlog]

/-- The `w_1` squared sum over the lattice:
`∑_k w_1(z + k)^2 ≤ 8 (K + K^{2a}) (1 + log K)`. -/
lemma sum_gradWeightOne_sq_le {s a : ℝ} (hs1 : s < 1) (ha : 0 ≤ a) (N : ℕ) (hN : 2 ≤ N)
    {K : ℝ} (hK : 1 ≤ K) (z : ℝ) :
    ∑ k ∈ Finset.range N, gradWeightOne s a K ((N : ℝ) / K) ((z + k) / K) ^ 2
      ≤ 8 * (K + K ^ (2 * a)) * (1 + Real.log K) := by
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hK0 : 0 < K := by linarith
  have hG : ∀ x : ℝ, gradWeightOne s a K ((N : ℝ) / K) (x / K) ^ 2
      = gradWeightOne s a K ((N : ℝ) / K) (circDist (N : ℝ) x / K) ^ 2 := by
    intro x
    congr 1
    apply gradWeightOne_congr
    rw [circDist_scale hK0, circDist_scale hK0,
      circDist_of_mem_Icc hNR (circDist_nonneg _ x) (circDist_le_half hNR x)]
  have hS : ∑ k ∈ Finset.range N, gradWeightOne s a K ((N : ℝ) / K) ((z + k) / K) ^ 2
      ≤ 2 * ∑ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1),
          gradWeightOne s a K ((N : ℝ) / K) ((m : ℝ) / K) ^ 2 :=
    sum_shell_le N hNpos z (fun x => gradWeightOne s a K ((N : ℝ) / K) (x / K) ^ 2)
      (fun d => gradWeightOne s a K ((N : ℝ) / K) (d / K) ^ 2) hG
      (fun x _ _ => sq_nonneg _)
      (fun x y hx hxy hy => by
        have h1 := gradWeightOne_anti_scaled hs1 ha hK hNR hx hxy hy
        have h2 := gradWeightOne_nonneg_unconditional s a K ((N : ℝ) / K) (y / K)
        show gradWeightOne s a K ((N : ℝ) / K) (y / K) ^ 2
          ≤ gradWeightOne s a K ((N : ℝ) / K) (x / K) ^ 2
        nlinarith)
  have hpt : ∀ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1),
      gradWeightOne s a K ((N : ℝ) / K) ((m : ℝ) / K) ^ 2
        ≤ (if (m : ℝ) < K then (K ^ (2 * a) + K) / max (m : ℝ) 1 else 0)
          + (if K ≤ (m : ℝ) then K ^ 2 / (m : ℝ) ^ 2 else 0) := by
    intro m hm
    have hmN := natCast_le_half_of_mem (N := N) hm
    by_cases hmK : (m : ℝ) < K
    · rw [ite_eq_left hmK, ite_eq_right (not_le.mpr hmK), add_zero]
      exact gradWeightOne_small_sq_le hK hNR (Nat.cast_nonneg m) hmN hmK
    · rw [ite_eq_right hmK, ite_eq_left (not_lt.mp hmK), zero_add]
      exact gradWeightOne_large_sq_le hs1 hK hNR (not_lt.mp hmK) hmN
  have hK2 : 0 ≤ K ^ (2 * a) := Real.rpow_nonneg (by linarith) _
  have hA := sum_small_part (K ^ (2 * a) + K) K (add_nonneg hK2 hK0.le) hK
    (⌊(N : ℝ) / 2⌋₊ + 1)
  have hB := sum_large_part K hK (⌊(N : ℝ) / 2⌋₊ + 1)
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK
  calc ∑ k ∈ Finset.range N, gradWeightOne s a K ((N : ℝ) / K) ((z + k) / K) ^ 2
      ≤ 2 * ∑ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1),
          gradWeightOne s a K ((N : ℝ) / K) ((m : ℝ) / K) ^ 2 := hS
    _ ≤ 2 * ∑ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1),
          ((if (m : ℝ) < K then (K ^ (2 * a) + K) / max (m : ℝ) 1 else 0)
            + (if K ≤ (m : ℝ) then K ^ 2 / (m : ℝ) ^ 2 else 0)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) (by norm_num)
    _ = 2 * (∑ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1),
          (if (m : ℝ) < K then (K ^ (2 * a) + K) / max (m : ℝ) 1 else 0)
          + ∑ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1),
          (if K ≤ (m : ℝ) then K ^ 2 / (m : ℝ) ^ 2 else 0)) := by
        rw [Finset.sum_add_distrib]
    _ ≤ 2 * ((K ^ (2 * a) + K) * (2 + Real.log K) + 2 * K) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) (by norm_num)
    _ ≤ 8 * (K + K ^ (2 * a)) * (1 + Real.log K) := by
        nlinarith [mul_nonneg (add_nonneg hK2 hK0.le) hlog]

/-- Pure algebra for the final combination in the weighted sum. -/
lemma final_combine_ineq {c T W A E P L : ℝ} (hc : 0 ≤ c) (hT : 0 ≤ T) (hW : 0 ≤ W)
    (hA : 0 ≤ A) (hE : 0 < E) (hP : 0 ≤ P) (hL : 1 ≤ L) :
    64 * c * W * (2 * T) + 8 * A * L * (P / E)
      ≤ (2 * (64 * c) * T + 8 * P) * L * (W + A / E) := by
  have hY : 0 ≤ A / E := div_nonneg hA hE.le
  have e1 : 8 * A * L * (P / E) = 8 * P * L * (A / E) := by ring
  rw [e1]
  nlinarith [mul_nonneg (mul_nonneg hc hT) (mul_nonneg hW (sub_nonneg.mpr hL)),
    mul_nonneg (mul_nonneg hc hT) (mul_nonneg (by linarith : (0 : ℝ) ≤ L) hY),
    mul_nonneg hP (mul_nonneg (by linarith : (0 : ℝ) ≤ L) hW)]

/-- The weighted lattice sum, with the denominator `(1 + circDist N k)^p`, `p = 1 + s/2`. -/
lemma sum_gradWeightTwo_weighted_le {s a p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 ≤ a)
    (hp : p = 1 + s / 2) (N : ℕ) (hN : 2 ≤ N) {K : ℝ} (hK : 1 ≤ K) (z : ℝ) :
    ∑ k ∈ Finset.range N, gradWeightTwo s a K ((N : ℝ) / K) ((z + k) / K)
        / (1 + circDist (N : ℝ) (k : ℝ)) ^ p
      ≤ (2 * (64 * 2 ^ a) * (∑' m : ℕ, 1 / (1 + (m : ℝ)) ^ p) + 8 * 2 ^ p) * (1 + Real.log K)
        * (gradWeightTwo s a K ((N : ℝ) / K) (z / K)
          + K ^ (1 + a) / (1 + circDist (N : ℝ) z) ^ p) := by
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hK0 : 0 < K := by linarith
  have hp1 : 1 < p := by rw [hp]; linarith
  have hp0 : 0 ≤ p := by linarith
  have hsum_p : Summable (fun m : ℕ => 1 / (1 + (m : ℝ)) ^ p) := by
    refine ((Real.summable_one_div_nat_add_rpow 1 p).mpr hp1).congr (fun m => ?_)
    rw [abs_of_nonneg (show (0 : ℝ) ≤ (m : ℝ) + 1 by positivity), add_comm]
  have hT0 : 0 ≤ ∑' m : ℕ, 1 / (1 + (m : ℝ)) ^ p := tsum_nonneg (fun m => by positivity)
  have hS1 := sum_gradWeightTwo_le hs1 ha N hN hK z
  have hsh : ∑ k ∈ Finset.range N, 1 / (1 + circDist (N : ℝ) (k : ℝ)) ^ p
      ≤ 2 * ∑' m : ℕ, 1 / (1 + (m : ℝ)) ^ p := by
    have h := sum_shell_le N hNpos 0 (fun x => 1 / (1 + circDist (N : ℝ) x) ^ p)
      (fun d => 1 / (1 + d) ^ p) (fun x => rfl)
      (fun x hx _ => div_nonneg zero_le_one (Real.rpow_nonneg (by linarith) _))
      (fun x y hx hxy _ => one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by linarith) _)
        (Real.rpow_le_rpow (by linarith) (by linarith) hp0))
    have h2 : ∑ m ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1), 1 / (1 + (m : ℝ)) ^ p
        ≤ ∑' m : ℕ, 1 / (1 + (m : ℝ)) ^ p :=
      hsum_p.sum_le_tsum _ (fun i _ => by positivity)
    simp only [zero_add] at h
    linarith
  have hE0 : 0 < (1 + circDist (N : ℝ) z) ^ p :=
    Real.rpow_pos_of_pos (by linarith [circDist_nonneg (L := (N : ℝ)) z]) _
  have hpt : ∀ k ∈ Finset.range N,
      gradWeightTwo s a K ((N : ℝ) / K) ((z + k) / K) / (1 + circDist (N : ℝ) (k : ℝ)) ^ p
        ≤ 64 * 2 ^ a * gradWeightTwo s a K ((N : ℝ) / K) (z / K)
            * (1 / (1 + circDist (N : ℝ) (k : ℝ)) ^ p)
          + gradWeightTwo s a K ((N : ℝ) / K) ((z + k) / K)
            * (2 ^ p / (1 + circDist (N : ℝ) z) ^ p) := by
    intro k _
    have hr := circDist_nonneg (L := (N : ℝ)) z
    have hD : 0 < (1 + circDist (N : ℝ) (k : ℝ)) ^ p :=
      Real.rpow_pos_of_pos (by linarith [circDist_nonneg (L := (N : ℝ)) (k : ℝ)]) _
    have hW := gradWeightTwo_nonneg_unconditional s a K ((N : ℝ) / K) ((z + k) / K)
    have hW0 := gradWeightTwo_nonneg_unconditional s a K ((N : ℝ) / K) (z / K)
    have hF : 0 ≤ 64 * 2 ^ a * gradWeightTwo s a K ((N : ℝ) / K) (z / K)
        * (1 / (1 + circDist (N : ℝ) (k : ℝ)) ^ p) :=
      mul_nonneg (mul_nonneg (by positivity) hW0) (div_nonneg zero_le_one hD.le)
    have hG : 0 ≤ gradWeightTwo s a K ((N : ℝ) / K) ((z + k) / K)
        * (2 ^ p / (1 + circDist (N : ℝ) z) ^ p) :=
      mul_nonneg hW (div_nonneg (by positivity) hE0.le)
    by_cases hcase : circDist (N : ℝ) (k : ℝ) ≤ circDist (N : ℝ) z / 2
    · have hA := gradWeightTwo_shift_le hs0 hs1 ha hK hNR z (k : ℝ) hcase
      have h1 : gradWeightTwo s a K ((N : ℝ) / K) ((z + k) / K)
          / (1 + circDist (N : ℝ) (k : ℝ)) ^ p
          ≤ 64 * 2 ^ a * gradWeightTwo s a K ((N : ℝ) / K) (z / K)
            / (1 + circDist (N : ℝ) (k : ℝ)) ^ p :=
        div_le_div_of_nonneg_right hA hD.le
      have h2 : 64 * 2 ^ a * gradWeightTwo s a K ((N : ℝ) / K) (z / K)
            / (1 + circDist (N : ℝ) (k : ℝ)) ^ p
          = 64 * 2 ^ a * gradWeightTwo s a K ((N : ℝ) / K) (z / K)
            * (1 / (1 + circDist (N : ℝ) (k : ℝ)) ^ p) := by
        ring
      linarith
    · have hlt : circDist (N : ℝ) z < 2 * circDist (N : ℝ) (k : ℝ) := by
        rw [not_le] at hcase
        linarith
      have hinv := one_div_rpow_le_two_rpow hp0 hr hlt
      have h1 : gradWeightTwo s a K ((N : ℝ) / K) ((z + k) / K)
          / (1 + circDist (N : ℝ) (k : ℝ)) ^ p
          ≤ gradWeightTwo s a K ((N : ℝ) / K) ((z + k) / K)
            * (2 ^ p / (1 + circDist (N : ℝ) z) ^ p) := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left hinv hW
      linarith
  calc ∑ k ∈ Finset.range N, gradWeightTwo s a K ((N : ℝ) / K) ((z + k) / K)
        / (1 + circDist (N : ℝ) (k : ℝ)) ^ p
      ≤ ∑ k ∈ Finset.range N, (64 * 2 ^ a * gradWeightTwo s a K ((N : ℝ) / K) (z / K)
            * (1 / (1 + circDist (N : ℝ) (k : ℝ)) ^ p)
          + gradWeightTwo s a K ((N : ℝ) / K) ((z + k) / K)
            * (2 ^ p / (1 + circDist (N : ℝ) z) ^ p)) := Finset.sum_le_sum hpt
    _ = 64 * 2 ^ a * gradWeightTwo s a K ((N : ℝ) / K) (z / K)
            * ∑ k ∈ Finset.range N, (1 / (1 + circDist (N : ℝ) (k : ℝ)) ^ p)
          + (∑ k ∈ Finset.range N, gradWeightTwo s a K ((N : ℝ) / K) ((z + k) / K))
            * (2 ^ p / (1 + circDist (N : ℝ) z) ^ p) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ 64 * 2 ^ a * gradWeightTwo s a K ((N : ℝ) / K) (z / K)
            * (2 * ∑' m : ℕ, 1 / (1 + (m : ℝ)) ^ p)
          + (8 * K ^ (1 + a) * (1 + Real.log K)) * (2 ^ p / (1 + circDist (N : ℝ) z) ^ p) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hsh (mul_nonneg (by positivity)
            (gradWeightTwo_nonneg_unconditional _ _ _ _ _))
        · exact mul_le_mul_of_nonneg_right hS1 (div_nonneg (by positivity) hE0.le)
    _ ≤ (2 * (64 * 2 ^ a) * (∑' m : ℕ, 1 / (1 + (m : ℝ)) ^ p) + 8 * 2 ^ p) * (1 + Real.log K)
        * (gradWeightTwo s a K ((N : ℝ) / K) (z / K)
          + K ^ (1 + a) / (1 + circDist (N : ℝ) z) ^ p) :=
        final_combine_ineq (by positivity) hT0 (gradWeightTwo_nonneg_unconditional _ _ _ _ _)
          (Real.rpow_nonneg (by linarith) _) hE0 (by positivity)
          (by linarith [Real.log_nonneg hK])

end Final

/-! ## The three lattice bounds -/

/-- The convolution part of Lemma 5.7, first lattice bound: the sum of the weight
`w_2` over `z + k`, `0 ≤ k < N`, is at most `C K^{1+a} (1 + log K)`. -/
theorem gradient_splitting_lattice_sum_one {s a : ℝ} (_hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a)
    (_ha : a < 1 - s / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (K z : ℝ), 2 ≤ N → 1 ≤ K → K ≤ N →
      ∑ k ∈ Finset.range N, gradWeightTwo s a K ((N : ℝ) / K) ((z + k) / K)
        ≤ C * K ^ (1 + a) * (1 + Real.log K) :=
  ⟨8, by norm_num, fun N K z hN hK _ => sum_gradWeightTwo_le hs1 ha0 N hN hK z⟩

/-- The convolution part of Lemma 5.7, second lattice bound: the sum of the squared
weight `w_1` over `z + k`, `0 ≤ k < N`, is at most `C (K + K^{2a}) (1 + log K)`. -/
theorem gradient_splitting_lattice_sum_two {s a : ℝ} (_hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a)
    (_ha : a < 1 - s / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (K z : ℝ), 2 ≤ N → 1 ≤ K → K ≤ N →
      ∑ k ∈ Finset.range N, gradWeightOne s a K ((N : ℝ) / K) ((z + k) / K) ^ 2
        ≤ C * (K + K ^ (2 * a)) * (1 + Real.log K) :=
  ⟨8, by norm_num, fun N K z hN hK _ => sum_gradWeightOne_sq_le hs1 ha0 N hN hK z⟩

/-- The convolution part of Lemma 5.7, third lattice bound (A1): the weighted sum
of `w_2(z + k)` against `(1 + circDist N k)^{-(1 + s/2)}` is at most
`C (1 + log K) (w_2(z) + K^{1+a} (1 + circDist N z)^{-(1 + s/2)})`. -/
theorem gradient_splitting_lattice_sum_three {s a : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a)
    (_ha : a < 1 - s / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (K z : ℝ), 2 ≤ N → 1 ≤ K → K ≤ N →
      ∑ k ∈ Finset.range N, gradWeightTwo s a K ((N : ℝ) / K) ((z + k) / K)
          / (1 + circDist (N : ℝ) (k : ℝ)) ^ (1 + s / 2)
        ≤ C * (1 + Real.log K) * (gradWeightTwo s a K ((N : ℝ) / K) (z / K)
          + K ^ (1 + a) / (1 + circDist (N : ℝ) z) ^ (1 + s / 2)) :=
  ⟨2 * (64 * 2 ^ a) * (∑' m : ℕ, 1 / (1 + (m : ℝ)) ^ (1 + s / 2)) + 8 * 2 ^ (1 + s / 2),
    add_pos_of_nonneg_of_pos
      (mul_nonneg (by positivity) (tsum_nonneg fun m => by positivity)) (by positivity),
    fun N K z hN hK _ => sum_gradWeightTwo_weighted_le hs0 hs1 ha0 rfl N hN hK z⟩

end Riesz1

end
