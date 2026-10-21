/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlGapGeometry

/-!
# Identification of the loop and good-event cutoffs

The two formulas for the loop cutoff agree.
This connects the cutoffs to the negligible cutoff-energy API.
-/

@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace Riesz1

theorem varAlGap_prod_pairs (N : ℕ+) (I : Finset (Fin (N : ℕ)))
    (f : Fin (N : ℕ) × ℤ → ℝ) :
    ∏ p ∈ cutoffPairs N I, f p =
      ∏ i ∈ I, ∏ k ∈ Icc (-((N : ℤ) / 2)) ((N : ℤ) / 2),
        if k ≠ 0 ∧ labelOf N ((i.val : ℤ) + k) ∈ I then f (i, k) else 1 := by
  classical
  have hdiv : (((N : ℕ) / 2 : ℕ) : ℤ) = (N : ℤ) / 2 := by omega
  simp only [cutoffPairs, Finset.prod_filter, Finset.prod_product, hdiv]
  let J := Icc (-((N : ℤ) / 2)) ((N : ℤ) / 2)
  calc (∏ i : Fin (N : ℕ), ∏ k ∈ J.erase 0,
      if i ∈ I ∧ labelOf N ((i.val : ℤ) + k) ∈ I then f (i, k) else 1)
      = ∏ i ∈ I, ∏ k ∈ J.erase 0,
          if i ∈ I ∧ labelOf N ((i.val : ℤ) + k) ∈ I then f (i, k) else 1 := by
        symm
        apply Finset.prod_subset (Finset.subset_univ I)
        intro i _ hi
        simp [hi]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [hi, true_and]
      calc (∏ k ∈ J.erase 0, if labelOf N ((i.val : ℤ) + k) ∈ I then f (i, k) else 1)
          = ∏ k ∈ J.erase 0,
            if k ≠ 0 ∧ labelOf N ((i.val : ℤ) + k) ∈ I then f (i, k) else 1 := by
            apply Finset.prod_congr rfl
            intro k hk
            by_cases h : labelOf N ((i.val : ℤ) + k) ∈ I <;>
              simp [h, (Finset.mem_erase.mp hk).1]
        _ = _ := Finset.prod_subset (Finset.erase_subset _ _) (by
            intro k hk hkn
            have hk0 : k = 0 := by simpa only [Finset.mem_erase, hk, and_true, not_not] using hkn
            simp only [hk0, ne_eq, not_true_eq_false, false_and, ↓reduceIte])

/-- Changing representatives does not change a lifted increment. -/
theorem varAlGap_lift_increment (N : ℕ+) (X : Fin (N : ℕ) → ℝ) (i k : ℤ) :
    gradLift N X (i + k) - gradLift N X i =
      gradLift N X (((gradIndex N i).val : ℤ) + k) - gradLift N X ((gradIndex N i).val : ℤ) := by
  have hi : i = ((gradIndex N i).val : ℤ) + (N : ℤ) * (i / (N : ℤ)) := by
    rw [varAlGap_index_eq, labelOf_val_int]
    exact (Int.emod_add_mul_ediv i (N : ℤ)).symm
  have hadd (j q : ℤ) : gradLift N X (j + (N : ℤ) * q) = gradLift N X j + q := by
    unfold gradLift
    rw [gradIndex_eq_of_sub (show j + (N : ℤ) * q = j + (N : ℤ) * q from rfl),
      Int.add_mul_ediv_left _ _ (by exact_mod_cast N.ne_zero)]
    push_cast
    ring
  conv_lhs => rw [hi]
  rw [show ((gradIndex N i).val : ℤ) + (N : ℤ) * (i / (N : ℤ)) + k =
    (((gradIndex N i).val : ℤ) + k) + (N : ℤ) * (i / (N : ℤ)) by ring,
    hadd, hadd]
  ring

/-- The residue map is injective on the auxiliary window representatives. -/
theorem varAlGap_index_injOn (N : ℕ+) (ℓ γ : ℝ) :
    Set.InjOn (gradIndex N) (gradLabels N ℓ γ : Set ℤ) := by
  intro i hi j hj hij
  apply gapRes_injOn hi hj
  have h := congrArg (fun e : Fin (N : ℕ) => (e.val : ℤ)) hij
  simpa only [varAlGap_index_eq, labelOf_val_int] using h

/-- The two cutoff products agree on every physical configuration. -/
theorem varAlGap_loopCutoff_eq_goodCutoff {N : ℕ+} {ℓ γ : ℝ}
    (hN : 2 ≤ (N : ℕ)) (hK : 1 ≤ (N : ℝ) * ℓ) (s ε : ℝ) (X : Configuration N) :
    loopCutoff s γ ε N ℓ X.val = goodCutoff N s ((N : ℝ) * ℓ) (2 * γ) ε X := by
  classical
  let K := (N : ℝ) * ℓ
  let I := gradLabels N ℓ (2 * γ)
  have hlift (j : ℤ) : cyclicLift X j = gradLift N X.val j := rfl
  have hidx (i k : ℤ) : labelOf N (((gradIndex N i).val : ℤ) + k) = gradIndex N (i + k) := by
    apply Fin.ext
    change ((((gradIndex N i).val : ℤ) + k) % (N : ℤ)).toNat = _
    rw [varAlGap_index_eq, labelOf_val_int, Int.add_emod, Int.emod_emod, ← Int.add_emod]
    rfl
  have hpair (i k : ℤ) : pairDev N X (gradIndex N i, k) =
      (N : ℝ) * (gradLift N X.val (i + k) - gradLift N X.val i) - k := by
    unfold pairDev
    simp only [hlift]
    rw [varAlGap_lift_increment N X.val i k]
  have hscale (i k : ℤ) : pairScale s K ε (gradIndex N i, k) = K ^ ε * |(k : ℝ)| ^ (s / 2) := by
    simp only [pairScale, Nat.cast_natAbs, Int.cast_abs]
  have hedge (i : ℤ) : gap X (((gradIndex N i).val : ℕ) : ℤ) =
      (N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i) := by
    unfold gap
    simp only [hlift]
    rw [varAlGap_lift_increment N X.val i 1]
  unfold goodCutoff
  rw [varAlGap_prod_pairs]
  conv_rhs =>
    lhs
    rw [varAlGap_window_eq hK, Finset.prod_image (varAlGap_index_injOn N ℓ (2 * γ))]
  have hnear : nearestPairs N (window N K (2 * γ)) =
      (I.filter (fun i => gradInWindow N ℓ (2 * γ) (i + 1))).image (gradIndex N) := by
    dsimp only [K, I]
    rw [varAlGap_window_eq hK]
    ext e
    simp only [nearestPairs, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hn⟩
      refine ⟨i, ⟨hi, ?_⟩, rfl⟩
      apply (varAlGap_endpoint_mem hK hi (k := 1) ⟨by omega, by omega⟩).2
      rw [← varAlGap_next_index]
      simpa only [varAlGap_window_eq hK, Finset.mem_image] using hn
    · rintro ⟨i, ⟨hi, hi1⟩, rfl⟩
      refine ⟨⟨i, hi, rfl⟩, ?_⟩
      rw [varAlGap_next_index]
      simpa only [varAlGap_window_eq hK, Finset.mem_image] using
        (varAlGap_endpoint_mem hK hi (k := 1) ⟨by omega, by omega⟩).1 hi1
  rw [hnear, Finset.prod_image ((varAlGap_index_injOn N ℓ (2 * γ)).mono (Finset.filter_subset _ _)),
    Finset.prod_filter]
  unfold loopCutoff
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    rw [hidx, hpair, hscale]
    have heq := varAlGap_endpoint_mem hK hi hk'
    rw [varAlGap_window_eq hK] at heq
    simp only [heq, cutoffC, scalarCutoff, K]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hedge]
    rfl

/-- In anchored coordinates the two cutoffs agree on the physical domain. -/
theorem varAlGap_loopCutoff_eq_anchoredCutoff {n : ℕ} {ℓ γ : ℝ}
    (hn : 1 ≤ n) (hK : 1 ≤ (n.succPNat : ℝ) * ℓ) (s ε : ℝ)
    {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n) :
    loopCutoff s γ ε n.succPNat ℓ (anchorVector y) =
      anchoredCutoff n.succPNat s ((n.succPNat : ℝ) * ℓ) (2 * γ) ε y := by
  let X : Configuration n.succPNat := ⟨anchorVector y, varAl_anchorVector_mem hy⟩
  have ha : anchorMap n.succPNat X = y := by
    rw [anchorMap_eq_anchorCoords]
    funext i
    simp only [anchorCoords, X, anchorVector_succ, anchorVector_zero, sub_zero]
  rw [varAlGap_loopCutoff_eq_goodCutoff (by simpa using hn) hK s ε X,
    ← anchoredCutoff_anchorMap, ha]

/-- The cutoff differentials also agree, since their formulas agree on an open chart. -/
theorem varAlGap_fderiv_cutoff {n : ℕ} {ℓ γ : ℝ}
    (hn : 1 ≤ n) (hK : 1 ≤ (n.succPNat : ℝ) * ℓ) (s ε : ℝ)
    {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n) :
    fderiv ℝ (fun z => loopCutoff s γ ε n.succPNat ℓ (anchorVector z)) y =
      fderiv ℝ (anchoredCutoff n.succPNat s ((n.succPNat : ℝ) * ℓ) (2 * γ) ε) y := by
  apply Filter.EventuallyEq.fderiv_eq
  exact Filter.eventually_of_mem ((isOpen_anchoredDomain n).mem_nhds hy)
    (fun z hz => varAlGap_loopCutoff_eq_anchoredCutoff hn hK s ε hz)

end Riesz1

end
