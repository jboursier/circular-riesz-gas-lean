/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopMomentsDefs

/-!
# Integer lifts of the particles and their residues

Deterministic facts used by the count moment estimate in Lemma 5.8:

* the gaps and the cyclic lifts are periodic with period `N` along the integers, the lift
  shifting by one period per `N` indices.
* the residue map `residueFin N : ℤ → Fin N` names the particle of an integer index, and two
  indices with the same residue differ by a multiple of `N`.
* the sum of the gaps over `L` consecutive indices is the block length.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset

attribute [local instance] Classical.propDecidable

namespace Riesz1

variable {N : ℕ+}

/-- The lifts shift by the integer `n` when the index shifts by `n` periods. -/
theorem cyclicLift_add_int_mul (X : Configuration N) (j n : ℤ) :
    cyclicLift X (j + n * ((N : ℕ) : ℤ)) = cyclicLift X j + n := by
  obtain ⟨i, hi, q, rfl⟩ := exists_nat_add_mul (N := N) j
  have h1 : (i : ℤ) + ((N : ℕ) : ℤ) * q + n * ((N : ℕ) : ℤ) =
      (i : ℤ) + ((N : ℕ) : ℤ) * (q + n) := by ring
  rw [h1, cyclicLift_add_mul X hi (q + n), cyclicLift_add_mul X hi q]
  push_cast
  ring

/-- The gaps are periodic along the integers. -/
theorem gap_add_int_mul (X : Configuration N) (j n : ℤ) :
    gap X (j + n * ((N : ℕ) : ℤ)) = gap X j := by
  unfold gap
  rw [show j + n * ((N : ℕ) : ℤ) + 1 = (j + 1) + n * ((N : ℕ) : ℤ) by ring,
    cyclicLift_add_int_mul, cyclicLift_add_int_mul]
  ring

/-- A gap is the block of length one. -/
theorem gap_eq_blockLength_one (X : Configuration N) (j : ℤ) :
    gap X j = blockLength X j 1 := by
  unfold gap blockLength
  simp

/-- The sum of the gaps over `L` consecutive indices is the block length. -/
theorem sum_gap_range_eq_blockLength (X : Configuration N) (c : ℤ) (L : ℕ) :
    ∑ r ∈ range L, gap X (c + r) = blockLength X c L :=
  (blockLength_eq_sum X c L).symm

/-- The residue of an integer index, as a particle index of `Fin N`. -/
def residueFin (N : ℕ+) (j : ℤ) : Fin (N : ℕ) :=
  ⟨(j % ((N : ℕ) : ℤ)).toNat, by
    have hN : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
    have h1 := Int.emod_nonneg j hN.ne'
    have h2 := Int.emod_lt_of_pos j hN
    omega⟩

theorem natCast_residueFin (j : ℤ) : (((residueFin N j : Fin (N : ℕ)) : ℕ) : ℤ) = j % ((N : ℕ) : ℤ) := by
  have hN : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  unfold residueFin
  exact Int.toNat_of_nonneg (Int.emod_nonneg j hN.ne')

/-- Shifting an index by a multiple of `N` does not change its residue. -/
theorem residueFin_add_int_mul (i : Fin (N : ℕ)) (n : ℤ) :
    residueFin N ((i : ℕ) + n * ((N : ℕ) : ℤ)) = i := by
  apply Fin.ext
  have h : (((residueFin N ((i : ℕ) + n * ((N : ℕ) : ℤ))) : ℕ) : ℤ) = ((i : ℕ) : ℤ) := by
    rw [natCast_residueFin, show ((i : ℕ) : ℤ) + n * ((N : ℕ) : ℤ) = (i : ℕ) + ((N : ℕ) : ℤ) * n by ring,
      Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast i.isLt)
  exact_mod_cast h

/-- Two integer indices with the same residue differ by a multiple of `N`. -/
theorem exists_int_mul_of_residueFin_eq {j j' : ℤ} (h : residueFin N j = residueFin N j') :
    ∃ n : ℤ, j' = j + n * ((N : ℕ) : ℤ) := by
  have h1 : j % ((N : ℕ) : ℤ) = j' % ((N : ℕ) : ℤ) := by
    rw [← natCast_residueFin, ← natCast_residueFin, h]
  obtain ⟨n, hn⟩ := Int.modEq_iff_dvd.mp (h1 : j ≡ j' [ZMOD ((N : ℕ) : ℤ)])
  exact ⟨n, by linarith [hn]⟩

/-! ### Jensen for inverse powers -/

/-- **Jensen for inverse powers.** Let `g_i > 0` for `i ∈ S`, with `∑ g_i ≤ r`, `r > 0`, and let
`q` be a natural number. Then `(card S)^(q+1) ≤ r^q ∑ g_i^{-q}`. -/
theorem card_pow_le_sum_inv_pow {ι : Type*} (S : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ S, 0 < g i) (q : ℕ) {r : ℝ} (hr : 0 < r) (hsum : ∑ i ∈ S, g i ≤ r) :
    ((S.card : ℝ)) ^ (q + 1) ≤ r ^ q * ∑ i ∈ S, g i ^ (-(q : ℤ)) := by
  rcases Nat.eq_zero_or_pos S.card with hcard | hcard
  · rw [hcard, Nat.cast_zero, zero_pow (by omega)]
    exact mul_nonneg (pow_nonneg hr.le q) (Finset.sum_nonneg fun i hi => zpow_nonneg (hg i hi).le _)
  set n : ℝ := (S.card : ℝ) with hn_def
  have hnpos : 0 < n := by rw [hn_def]; exact_mod_cast hcard
  have hSpos : 0 < ∑ i ∈ S, g i := by
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hcard
    exact Finset.sum_pos (fun j hj => hg j hj) ⟨i, hi⟩
  have hw1 : ∑ _i ∈ S, (1 / n) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, hn_def]
    field_simp
  -- Jensen for the convex function `x ↦ x^{-q}` at the mean of the `g_i`.
  have hJ : ((∑ i ∈ S, g i) / n) ^ (-(q : ℤ)) ≤ (1 / n) * ∑ i ∈ S, g i ^ (-(q : ℤ)) := by
    have h := Real.zpow_arith_mean_le_arith_mean_zpow (s := S) (fun _ => 1 / n) g
      (fun _ _ => by positivity) hw1 (fun i hi => hg i hi) (-(q : ℤ))
    beta_reduce at h
    have e1 : ∑ i ∈ S, (1 / n) * g i = (∑ i ∈ S, g i) / n := by
      rw [← Finset.mul_sum]
      ring
    have e2 : ∑ i ∈ S, (1 / n) * g i ^ (-(q : ℤ)) = (1 / n) * ∑ i ∈ S, g i ^ (-(q : ℤ)) := by
      rw [← Finset.mul_sum]
    rw [e1, e2] at h
    exact h
  -- The mean is at most `r/n`, so its inverse power is at least `(r/n)^{-q}`.
  have hμ_le : (∑ i ∈ S, g i) / n ≤ r / n := div_le_div_of_nonneg_right hsum hnpos.le
  have hμ_pos : 0 < (∑ i ∈ S, g i) / n := div_pos hSpos hnpos
  have H2 : (r / n) ^ (-(q : ℤ)) ≤ ((∑ i ∈ S, g i) / n) ^ (-(q : ℤ)) := by
    rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
    exact inv_anti₀ (pow_pos hμ_pos q) (pow_le_pow_left₀ hμ_pos.le hμ_le q)
  have hrq : (r / n) ^ (-(q : ℤ)) = n ^ q / r ^ q := by
    rw [zpow_neg, zpow_natCast, div_pow, inv_div]
  have hkey : n * (n ^ q / r ^ q) ≤ ∑ i ∈ S, g i ^ (-(q : ℤ)) := by
    rw [← hrq]
    have h3 : n * (r / n) ^ (-(q : ℤ)) ≤ n * ((1 / n) * ∑ i ∈ S, g i ^ (-(q : ℤ))) :=
      mul_le_mul_of_nonneg_left (H2.trans hJ) hnpos.le
    rwa [show n * ((1 / n) * ∑ i ∈ S, g i ^ (-(q : ℤ))) = ∑ i ∈ S, g i ^ (-(q : ℤ)) by
      field_simp] at h3
  have hrq_pos : 0 < r ^ q := pow_pos hr q
  have hfin : n ^ (q + 1) ≤ r ^ q * ∑ i ∈ S, g i ^ (-(q : ℤ)) := by
    have h4 := mul_le_mul_of_nonneg_right hkey hrq_pos.le
    have e : n * (n ^ q / r ^ q) * r ^ q = n ^ (q + 1) := by
      field_simp
      ring
    rw [e, mul_comm] at h4
    exact h4
  rw [hn_def] at hfin
  exact hfin

end Riesz1

end
end
