/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriComparisonSummation
public import Riesz1.Variance.APrioriCutoffChain

/-!
# The affine comparator on the good event

The comparator and the deterministic comparator estimate in the
proof of Lemma 5.2. Both choices of weights obey the
same bound. The last theorem gives the exact affine differential in
the anchored coordinates.
-/

@[expose] public section

noncomputable section

open Finset

namespace Riesz1

namespace APrioriComparison

/-- Weighted anchored errors on the good event. This helper permits any
nonnegative weights. The specific weights are supplied below. -/
theorem comparator_good_le {N : ℕ+} {K s γ ε : ℝ} (hK : 1 ≤ K)
    (J : Finset (Fin (N : ℕ))) (hJ : J ⊆ window N K γ)
    (w : Fin (N : ℕ) → ℝ) (hw : ∀ i ∈ J, 0 ≤ w i)
    (X : Configuration N) (hX : X ∈ goodEvent N s K γ ε) :
    |∑ i ∈ J, w i * (((N : ℕ) : ℝ) * (X.val i - X.val ⟨0, N.pos⟩) - (i : ℕ))| ≤
      K ^ ε * ∑ i ∈ J, w i * (labelDistToOne N i : ℝ) ^ (s / 2) := by
  calc _ ≤ ∑ i ∈ J, |w i * (((N : ℕ) : ℝ) * (X.val i - X.val ⟨0, N.pos⟩) - (i : ℕ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ J, w i * (K ^ ε * (labelDistToOne N i : ℝ) ^ (s / 2)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_of_nonneg (hw i hi)]
        exact mul_le_mul_of_nonneg_left (APG.anchored_error X hK hX (hJ hi)) (hw i hi)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

/-- Exact affine derivative for any fixed weights in the anchored chart. -/
theorem hasFDerivAt_comparator (n : ℕ) (J : Finset (Fin (n.succPNat : ℕ)))
    (w : Fin (n.succPNat : ℕ) → ℝ) (y : Fin n → ℝ) :
    HasFDerivAt (fun z : Fin n → ℝ => ∑ i ∈ J,
      w i * (((n : ℝ) + 1) * anchorVector z i - (i : ℕ)))
      (∑ i ∈ J, (w i * ((n : ℝ) + 1)) • anchorCoord n i) y := by
  have hd : ∀ i ∈ J, HasFDerivAt
      (fun z => w i * (((n : ℝ) + 1) * anchorVector z i - (i : ℕ)))
      ((w i * ((n : ℝ) + 1)) • anchorCoord n i) y := by
    intro i _
    have h := ((((anchorCoord n i).hasFDerivAt (x := y)).const_mul ((n : ℝ) + 1)).sub_const
      ((i : ℕ) : ℝ)).const_mul (w i)
    simpa only [anchorCoord_apply, smul_smul] using h
  convert HasFDerivAt.sum hd using 1
  ext z
  simp only [Finset.sum_apply]

/-- The differential of the original comparator. -/
theorem linearComparator_hasFDerivAt (n : ℕ) (K s lam ε : ℝ)
    (J : Finset (Fin (n.succPNat : ℕ))) (y : Fin n → ℝ) :
    HasFDerivAt (fun z => linearComparator n.succPNat K s lam ε J (anchorVector z))
      (∑ i ∈ J, (comparisonWeight n.succPNat K s lam ε i * ((n : ℝ) + 1)) • anchorCoord n i) y := by
  simpa only [linearComparator, Nat.succPNat_coe, Nat.cast_succ] using
    hasFDerivAt_comparator n J (comparisonWeight n.succPNat K s lam ε) y

/-- The differential of the augmented comparator. -/
theorem augmentedLinearComparator_hasFDerivAt (n : ℕ) (K s lam ε : ℝ)
    (J : Finset (Fin (n.succPNat : ℕ))) (y : Fin n → ℝ) :
    HasFDerivAt (fun z => augmentedLinearComparator n.succPNat K s lam ε J (anchorVector z))
      (∑ i ∈ J, (augmentedComparisonWeight n.succPNat K s lam ε i * ((n : ℝ) + 1)) •
        anchorCoord n i) y := by
  simpa only [augmentedLinearComparator, Nat.succPNat_coe, Nat.cast_succ] using
    hasFDerivAt_comparator n J (augmentedComparisonWeight n.succPNat K s lam ε) y

end APrioriComparison

/-- The comparator bound used in the proof of Lemma 5.2.
The power loss is `K^(3ε)` for both sets of weights, uniformly before
the particle number, the scale, the window subset and the configuration. -/
theorem a_priori_comparison_comparator (s lam γ : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hlam : 0 ≤ lam) (hγ : 1 < γ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (K : ℝ), 1 ≤ K →
      ∀ J : Finset (Fin (N : ℕ)), J ⊆ (window N K γ).erase ⟨0, N.pos⟩ →
      ∀ X : Configuration N, X ∈ goodEvent N s K γ ε →
        |linearComparator N K s lam ε J (fun i => X.val i - X.val ⟨0, N.pos⟩)| ≤
          C * K ^ (3 * ε) * (K ^ lam + K ^ (s / 2)) ∧
        |augmentedLinearComparator N K s lam ε J (fun i => X.val i - X.val ⟨0, N.pos⟩)| ≤
          C * K ^ (3 * ε) * (K ^ lam + K ^ (s / 2)) := by
  obtain ⟨C, hC, hsum⟩ := comparison_sums_le s lam γ hs hs1 hlam hγ ε hε hε1
  refine ⟨C, hC, fun N K hK J hJ X hX => ?_⟩
  have hK0 : 0 < K := by linarith
  have hJw : J ⊆ window N K γ := hJ.trans (erase_subset _ _)
  have hsums := hsum N K hK J hJ
  have heq : K ^ ε * (C * K ^ (2 * ε) * (K ^ lam + K ^ (s / 2))) =
      C * K ^ (3 * ε) * (K ^ lam + K ^ (s / 2)) := by
    rw [show 3 * ε = ε + 2 * ε by ring, Real.rpow_add hK0]
    ring
  constructor
  · exact (APrioriComparison.comparator_good_le hK J hJw (comparisonWeight N K s lam ε)
      (fun i _ => comparisonWeight_nonneg hK0.le i) X hX).trans
        ((mul_le_mul_of_nonneg_left hsums.1 (by positivity)).trans_eq heq)
  · exact (APrioriComparison.comparator_good_le hK J hJw (augmentedComparisonWeight N K s lam ε)
      (fun i _ => augmentedComparisonWeight_nonneg hK0.le i) X hX).trans
        ((mul_le_mul_of_nonneg_left hsums.2 (by positivity)).trans_eq heq)

end Riesz1

end
