/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodCutoff

/-!
# The good-event cutoff in gap coordinates

This serves the gradient claim in the proof of Lemma 5.2. The cutoff `η_{ε,γ}` of
`Riesz1/Variance/APrioriGoodCutoff.lean` is a function of a configuration `X` through the
dimensionless gaps `z_i = N (x_{i+1} - x_i)`. Here the same cutoff is written as a function of
the gap vector `z : Fin N → ℝ`, with the label `j` carrying the gap `z_j`.

* `gapOrientedSum N z a b` is the oriented sum of the gaps from the integer `a` to the integer `b`:
  `∑_{r ∈ [a, b)} z_{r} - ∑_{r ∈ [b, a)} z_{r}`, where `z_r` is `z (labelOf N r)`. For `a ≤ b`
  the second sum is empty. It is `N (x_b - x_a)` for `z` the gaps of `X`.
* `gapPairDev N z p = gapOrientedSum N z i (i + k) - k` for a pair `p = (i, k)`. It is the
  pair deviation `pairDev N X p` written in the gaps.
* `gapCutoff N s K γ ε z` is the product defining `goodCutoff`, with `pairDev` replaced by
  `gapPairDev` and each nearest-neighbour gap `gap X i` replaced by `z i`.
* `gapGoodEvent N s K γ ε` is the set of gap vectors satisfying the two conditions of `goodEvent`.

The bridging identity `goodCutoff_eq_gapCutoff` says that `η_{ε,γ}(X)` equals `gapCutoff` at the
gap vector of `X`.
-/

@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace Riesz1

variable {N : ℕ+}

/-! ### Oriented sums of gaps -/

/-- The oriented sum of the gap vector `z` from the integer `a` to the integer `b`: the sum of
`z (labelOf N r)` over `r ∈ [a, b)`, minus the same sum over `r ∈ [b, a)`. -/
def gapOrientedSum (N : ℕ+) (z : Fin (N : ℕ) → ℝ) (a b : ℤ) : ℝ :=
  ∑ r ∈ Ico a b, z (labelOf N r) - ∑ r ∈ Ico b a, z (labelOf N r)

/-- The deviation `N (x_{i+k} - x_i) - k` of a pair `p = (i, k)`, written in the gap vector `z`. -/
def gapPairDev (N : ℕ+) (z : Fin (N : ℕ) → ℝ) (p : Fin (N : ℕ) × ℤ) : ℝ :=
  gapOrientedSum N z ((p.1 : ℕ) : ℤ) (((p.1 : ℕ) : ℤ) + p.2) - p.2

/-- The good-event cutoff `η_{ε,γ}`, written in the gap vector `z`. It is
the product of `goodCutoff`, with the pair deviation and the nearest-neighbour gaps replaced by
their expressions in `z`. -/
def gapCutoff (N : ℕ+) (s K γ ε : ℝ) (z : Fin (N : ℕ) → ℝ) : ℝ :=
  (∏ p ∈ cutoffPairs N (window N K γ),
      scalarCutoff (2 * |gapPairDev N z p| / pairScale s K ε p)) *
    ∏ i ∈ nearestPairs N (window N K γ),
      (scalarCutoff (2 * z i / K ^ ε) * scalarCutoff (2 / (K ^ ε * z i)))

/-- The good event `A_{ε,γ}` of `goodEvent`, as a set of gap vectors. -/
def gapGoodEvent (N : ℕ+) (s K γ ε : ℝ) : Set (Fin (N : ℕ) → ℝ) :=
  {z | (∀ p ∈ cutoffPairs N (window N K γ), |gapPairDev N z p| ≤ pairScale s K ε p) ∧
    ∀ i ∈ nearestPairs N (window N K γ), K ^ (-ε) ≤ z i ∧ z i ≤ K ^ ε}

/-! ### Telescoping over the integers -/

/-- Telescoping over the natural lengths: `∑_{r ∈ [a, a + n)} (F (r + 1) - F r) = F (a + n) - F a`. -/
theorem sum_Ico_telescope_nat (F : ℤ → ℝ) (a : ℤ) (n : ℕ) :
    ∑ r ∈ Ico a (a + n), (F (r + 1) - F r) = F (a + n) - F a := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : a ≤ a + (n : ℤ) := by omega
    have h2 : a + (n : ℤ) ≤ a + (n : ℤ) + 1 := by omega
    rw [Nat.cast_succ, ← add_assoc,
      ← Finset.Ico_union_Ico_eq_Ico h1 h2,
      Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive a (a + (n : ℤ)) (a + (n : ℤ) + 1)),
      ih]
    have hsingle : Ico (a + (n : ℤ)) (a + (n : ℤ) + 1) = {a + (n : ℤ)} := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      omega
    rw [hsingle, Finset.sum_singleton]
    ring

/-- Telescoping over the integers: `∑_{r ∈ [a, b)} (F (r + 1) - F r) = F b - F a` for `a ≤ b`. -/
private theorem sum_Ico_telescope_int (F : ℤ → ℝ) {a b : ℤ} (hab : a ≤ b) :
    ∑ r ∈ Ico a b, (F (r + 1) - F r) = F b - F a := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  exact sum_Ico_telescope_nat F a n

/-! ### Labels and periodicity of the gaps -/

/-- The label of an integer, as an integer, is its residue modulo `N`. -/
theorem labelOf_val_int (N : ℕ+) (r : ℤ) : (((labelOf N r : Fin (N : ℕ)) : ℕ) : ℤ) = r % (N : ℕ) := by
  unfold labelOf
  simp only
  exact Int.toNat_of_nonneg (Int.emod_nonneg r (by exact_mod_cast N.ne_zero))

/-- The gaps are `N`-periodic on all integer multiples of `N`. -/
theorem gap_add_mul_N (X : Configuration N) (j : ℤ) (m : ℤ) :
    gap X (j + ((N : ℕ) : ℤ) * m) = gap X j := by
  induction m using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [show j + ((N : ℕ) : ℤ) * ((i : ℤ) + 1) = (j + ((N : ℕ) : ℤ) * i) + ((N : ℕ) : ℤ) by ring,
      gap_add_N, ih]
  | pred i ih =>
    rw [← ih, ← gap_add_N X (j + ((N : ℕ) : ℤ) * (-(i : ℤ) - 1))]
    congr 1
    ring

/-- A gap at an integer equals the gap at its label: `gap X r = gap X (labelOf N r)`. -/
theorem gap_labelOf (X : Configuration N) (r : ℤ) :
    gap X ((((labelOf N r : Fin (N : ℕ)) : ℕ) : ℤ)) = gap X r := by
  rw [labelOf_val_int]
  have hdecomp : r % ((N : ℕ) : ℤ) + ((N : ℕ) : ℤ) * (r / ((N : ℕ) : ℤ)) = r := by
    rw [Int.emod_def]
    ring
  conv_rhs => rw [← hdecomp]
  exact (gap_add_mul_N X _ _).symm

/-! ### The lifted difference in gap coordinates -/

/-- For a configuration, the oriented sum of its gaps from `a` to `b` is the lifted difference
`N (x_b - x_a)`. -/
theorem gapOrientedSum_gap (X : Configuration N) (a b : ℤ) :
    gapOrientedSum N (fun i : Fin (N : ℕ) => gap X (((i : ℕ) : ℤ))) a b =
      ((N : ℕ) : ℝ) * (cyclicLift X b - cyclicLift X a) := by
  unfold gapOrientedSum
  have hcongr : ∀ r : ℤ, gap X ((((labelOf N r : Fin (N : ℕ)) : ℕ) : ℤ)) = gap X r :=
    fun r => gap_labelOf X r
  simp only [hcongr]
  -- Telescoping: the gap at `r` is `N (x_{r+1} - x_r)`.
  have hgap : ∀ r : ℤ, gap X r = (fun t : ℤ => ((N : ℕ) : ℝ) * cyclicLift X t) (r + 1) -
      (fun t : ℤ => ((N : ℕ) : ℝ) * cyclicLift X t) r := by
    intro r
    simp only [gap]
    ring
  rcases le_total a b with hab | hba
  · rw [Finset.Ico_eq_empty_of_le hab, Finset.sum_empty, sub_zero]
    simp_rw [hgap]
    rw [sum_Ico_telescope_int (fun t : ℤ => ((N : ℕ) : ℝ) * cyclicLift X t) hab]
    ring
  · rw [Finset.Ico_eq_empty_of_le hba, Finset.sum_empty, zero_sub]
    simp_rw [hgap]
    rw [sum_Ico_telescope_int (fun t : ℤ => ((N : ℕ) : ℝ) * cyclicLift X t) hba]
    ring

/-! ### The bridging identity -/

/-- The pair deviation is the gap-coordinate pair deviation at the gaps of the configuration. -/
theorem pairDev_eq_gapPairDev (X : Configuration N) (p : Fin (N : ℕ) × ℤ) :
    pairDev N X p = gapPairDev N (fun i : Fin (N : ℕ) => gap X (((i : ℕ) : ℤ))) p := by
  unfold pairDev gapPairDev
  rw [gapOrientedSum_gap]

/-- **Bridging identity.** The good-event cutoff of a configuration is the gap-coordinate cutoff
at the gap vector of that configuration: `η_{ε,γ}(X) = η_{ε,γ}(z)` for `z_i = N (x_{i+1} - x_i)`. -/
theorem goodCutoff_eq_gapCutoff (s K γ ε : ℝ) (X : Configuration N) :
    goodCutoff N s K γ ε X =
      gapCutoff N s K γ ε (fun i : Fin (N : ℕ) => gap X (((i : ℕ) : ℤ))) := by
  unfold goodCutoff gapCutoff
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [pairDev_eq_gapPairDev]

end Riesz1

end
end
