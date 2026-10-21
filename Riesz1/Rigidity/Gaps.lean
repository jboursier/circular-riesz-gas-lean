/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.CyclicLift

/-!
# Gap coordinates and block lengths

For a configuration `X` of `N` particles, the gap at
`j` is `N (x_{j+1} - x_j)` and the block length of `L` gaps from `j` is
`N (x_{j+L} - x_j)`, where `x_j = cyclicLift X j` is the cyclic lift. The
gaps are positive, `N`-periodic in `j`, and sum to `N` over one period.
Their measurability on `Configuration N` is recorded at the end.
-/

@[expose] public section

open MeasureTheory Finset

namespace Riesz1

variable {N : ℕ+}

/-- The gap `y_j = N (x_{j+1} - x_j)` at the cyclic index `j`. -/
def gap (X : Configuration N) (j : ℤ) : ℝ :=
  ((N : ℕ) : ℝ) * (cyclicLift X (j + 1) - cyclicLift X j)

/-- The block length `S_{j,L} = N (x_{j+L} - x_j)`, the sum of `L` consecutive gaps from `j`. -/
def blockLength (X : Configuration N) (j : ℤ) (L : ℕ) : ℝ :=
  ((N : ℕ) : ℝ) * (cyclicLift X (j + L) - cyclicLift X j)

/-! ### Lifts of a configuration -/

/-- The lifts of a configuration are strictly increasing in the particle index. -/
theorem config_strictMono (X : Configuration N) : StrictMono X.val := by
  obtain ⟨h, -⟩ := X.2
  exact h

/-- Every lift lies below the first lift plus one. -/
theorem config_lt_first_add_one (X : Configuration N) (i : Fin (N : ℕ)) :
    X.val i < X.val ⟨0, N.pos⟩ + 1 := by
  obtain ⟨-, -, -, h⟩ := X.2
  exact h i

/-- Every integer `j` writes as `i + N q` with `0 ≤ i < N` and `q` an integer. -/
theorem exists_nat_add_mul (j : ℤ) :
    ∃ i : ℕ, i < (N : ℕ) ∧ ∃ q : ℤ, j = (i : ℤ) + ((N : ℕ) : ℤ) * q := by
  have hN : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  refine ⟨(j % ((N : ℕ) : ℤ)).toNat, ?_, j / ((N : ℕ) : ℤ), ?_⟩
  · have := Int.emod_lt_of_pos j hN
    have := Int.emod_nonneg j hN.ne'
    omega
  · have h := Int.emod_def j ((N : ℕ) : ℤ)
    rw [Int.toNat_of_nonneg (Int.emod_nonneg j hN.ne')]
    linarith

/-- The cyclic lift at `i + N q` for `i < N` is the `i`-th lift shifted by `q`. -/
theorem cyclicLift_add_mul (X : Configuration N) {i : ℕ} (hi : i < (N : ℕ)) (q : ℤ) :
    cyclicLift X ((i : ℤ) + ((N : ℕ) : ℤ) * q) = X.val ⟨i, hi⟩ + q := by
  have hN : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  have hmod : ((i : ℤ) + ((N : ℕ) : ℤ) * q) % ((N : ℕ) : ℤ) = i := by
    rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hi)]
  have hdiv : ((i : ℤ) + ((N : ℕ) : ℤ) * q) / ((N : ℕ) : ℤ) = q := by
    rw [Int.add_mul_ediv_left _ _ hN.ne',
      Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hi), zero_add]
  unfold cyclicLift
  simp only [hmod, hdiv, Int.toNat_natCast]

/-- The lift at the particle index `i < N` is the `i`-th lift itself. -/
theorem cyclicLift_natCast (X : Configuration N) (i : Fin (N : ℕ)) :
    cyclicLift X (i : ℕ) = X.val i := by
  simpa using cyclicLift_add_mul X i.isLt 0

/-- Consecutive cyclic lifts increase. -/
theorem cyclicLift_lt_succ (X : Configuration N) (j : ℤ) :
    cyclicLift X j < cyclicLift X (j + 1) := by
  obtain ⟨i, hi, q, rfl⟩ := exists_nat_add_mul (N := N) j
  by_cases hsucc : i + 1 < (N : ℕ)
  · have h1 : (i : ℤ) + ((N : ℕ) : ℤ) * q + 1
        = ((i + 1 : ℕ) : ℤ) + ((N : ℕ) : ℤ) * q := by
      push_cast
      ring
    rw [h1, cyclicLift_add_mul X hi, cyclicLift_add_mul X hsucc]
    have h2 : X.val ⟨i, hi⟩ < X.val ⟨i + 1, hsucc⟩ :=
      config_strictMono X (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))
    linarith
  · have hiN : (i : ℤ) + 1 = ((N : ℕ) : ℤ) := by
      have : i + 1 = (N : ℕ) := by omega
      exact_mod_cast this
    have h1 : (i : ℤ) + ((N : ℕ) : ℤ) * q + 1
        = ((0 : ℕ) : ℤ) + ((N : ℕ) : ℤ) * (q + 1) := by
      push_cast
      linear_combination hiN
    rw [h1, cyclicLift_add_mul X N.pos (q + 1), cyclicLift_add_mul X hi q]
    have h2 := config_lt_first_add_one X ⟨i, hi⟩
    push_cast
    linarith

/-- The cyclic lift is strictly increasing on `ℤ`. -/
theorem cyclicLift_strictMono (X : Configuration N) : StrictMono (cyclicLift X) :=
  strictMono_int_of_lt_succ (cyclicLift_lt_succ X)

/-- Shifting the index by `N` adds one to the cyclic lift. -/
theorem cyclicLift_add_N (X : Configuration N) (j : ℤ) :
    cyclicLift X (j + ((N : ℕ) : ℤ)) = cyclicLift X j + 1 := by
  obtain ⟨i, hi, q, rfl⟩ := exists_nat_add_mul (N := N) j
  have h1 : (i : ℤ) + ((N : ℕ) : ℤ) * q + ((N : ℕ) : ℤ)
      = (i : ℤ) + ((N : ℕ) : ℤ) * (q + 1) := by
    ring
  rw [h1, cyclicLift_add_mul X hi (q + 1), cyclicLift_add_mul X hi q]
  push_cast
  ring

/-! ### Gaps and block lengths -/

/-- Each gap is positive, since the cyclic lifts strictly increase. -/
theorem gap_pos (X : Configuration N) (j : ℤ) : 0 < gap X j := by
  unfold gap
  have hN : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  exact mul_pos hN (sub_pos.mpr (cyclicLift_strictMono X (lt_add_one j)))

/-- The gap sequence is `N`-periodic. -/
theorem gap_add_N (X : Configuration N) (j : ℤ) :
    gap X (j + ((N : ℕ) : ℤ)) = gap X j := by
  unfold gap
  rw [show j + ((N : ℕ) : ℤ) + 1 = (j + 1) + ((N : ℕ) : ℤ) by ring,
    cyclicLift_add_N, cyclicLift_add_N]
  ring

/-- A block length is the sum of the gaps it covers. -/
theorem blockLength_eq_sum (X : Configuration N) (j : ℤ) (L : ℕ) :
    blockLength X j L = ∑ r ∈ range L, gap X (j + r) := by
  set f : ℕ → ℝ := fun r => cyclicLift X (j + r) with hf
  have h1 : ∀ r : ℕ, gap X (j + r) = ((N : ℕ) : ℝ) * (f (r + 1) - f r) := by
    intro r
    simp only [gap, hf, Nat.cast_succ, add_assoc]
  simp only [h1, ← Finset.mul_sum, Finset.sum_range_sub]
  simp [blockLength, hf]

/-- A block of `N` consecutive gaps has length `N`. -/
theorem blockLength_N (X : Configuration N) (j : ℤ) :
    blockLength X j (N : ℕ) = ((N : ℕ) : ℝ) := by
  unfold blockLength
  rw [cyclicLift_add_N]
  ring

/-- The gaps over one period add up to `N`. -/
theorem sum_gap_eq (X : Configuration N) :
    ∑ j ∈ range (N : ℕ), gap X (j : ℤ) = ((N : ℕ) : ℝ) := by
  have h := blockLength_eq_sum X 0 (N : ℕ)
  rw [blockLength_N] at h
  simpa using h.symm

/-! ### Measurability on the configuration space -/

/-- Each cyclic lift is a measurable function of the configuration. -/
theorem measurable_cyclicLift (j : ℤ) :
    Measurable fun X : Configuration N => cyclicLift X j := by
  have hk : ∀ k : Fin (N : ℕ), Measurable fun X : Configuration N => X.val k :=
    fun k => (measurable_pi_apply k).comp measurable_subtype_coe
  unfold cyclicLift
  exact (hk _).add_const _

/-- Each gap is a measurable function of the configuration. -/
theorem measurable_gap (j : ℤ) : Measurable fun X : Configuration N => gap X j := by
  unfold gap
  exact measurable_const.mul ((measurable_cyclicLift _).sub (measurable_cyclicLift _))

/-- Each block length is a measurable function of the configuration. -/
theorem measurable_blockLength (j : ℤ) (L : ℕ) :
    Measurable fun X : Configuration N => blockLength X j L := by
  unfold blockLength
  exact measurable_const.mul ((measurable_cyclicLift _).sub (measurable_cyclicLift _))

end Riesz1

end
