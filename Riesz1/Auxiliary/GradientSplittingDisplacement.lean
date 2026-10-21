/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingDisplacementPair

/-!
# The displacement part of the gradient field: the main estimate

The displacement part of Lemma 5.7. The sum of the pair bounds
over the window, through the particle sums of the convolution part of Lemma 5.7, and the
main theorem `Riesz1.gradient_splitting_displacement`.
-/

@[expose] public section

open scoped ContDiff

namespace Riesz1

noncomputable section

/-! ## Lattice sums of the decay factor -/

/-- The residue map `j ↦ (j - i) mod N` is injective on the window. -/
lemma gradRes_injOn {ℓ γ : ℝ} {N : ℕ+} {i : ℤ} :
    Set.InjOn (gradRes N i) ↑(gradLabels N ℓ γ) := by
  intro j hj j' hj' hgj
  have hr : (j - i) % ((N : ℕ) : ℤ) = (j' - i) % ((N : ℕ) : ℤ) := by
    have h1 := gradRes_cast N i j
    have h2 := gradRes_cast N i j'
    rw [← h1, ← h2, hgj]
  exact emod_inj_of_abs_sub_lt hr (gradLabels_abs_sub_lt hj' hj)

/-- A sum over the window of a function of the residue is at most the sum over all residues. -/
lemma sum_labels_le_range {ℓ γ : ℝ} {N : ℕ+} {i : ℤ} (f : ℕ → ℝ) (hf : ∀ r, 0 ≤ f r) :
    ∑ j ∈ gradLabels N ℓ γ, f (gradRes N i j) ≤ ∑ r ∈ Finset.range (N : ℕ), f r := by
  rw [← Finset.sum_image (f := f) (g := gradRes N i) gradRes_injOn]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    obtain ⟨j, _, hjr⟩ := Finset.mem_image.mp hr
    rw [← hjr]
    exact Finset.mem_range.mpr (gradRes_lt N i j)
  · intro r _ _
    exact hf r

/-- The series `∑_m (1 + m)^{-p}` is summable for `p > 1`. -/
lemma summable_one_add_rpow_neg {p : ℝ} (hp : 1 < p) :
    Summable (fun m : ℕ => (1 + (m : ℝ)) ^ (-p)) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr hp)
  refine h.congr (fun n => ?_)
  rw [Real.rpow_neg (by positivity), Nat.cast_succ, add_comm]

/-- Uniform lattice bound on the decay factor over the window:
`∑_{j ∈ I} (1 + d(i,j))^{-(1+s/2)} ≤ C` with `C` depending on `s` only. -/
lemma sum_labels_decay_le {s : ℝ} (hs0 : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ : ℝ) (i : ℤ), 2 ≤ (N : ℕ) → i ∈ gradLabels N ℓ γ →
      ∑ j ∈ gradLabels N ℓ γ, (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2)) ≤ C := by
  have hp : 1 < 1 + s / 2 := by linarith
  have hsum := summable_one_add_rpow_neg hp
  have hTnn : 0 ≤ ∑' m : ℕ, (1 + (m : ℝ)) ^ (-(1 + s / 2)) :=
    tsum_nonneg (fun m => Real.rpow_nonneg (by positivity) _)
  refine ⟨2 * (∑' m : ℕ, (1 + (m : ℝ)) ^ (-(1 + s / 2))) + 1, by linarith, fun N ℓ γ i hN hi => ?_⟩
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hsum_eq : ∑ j ∈ gradLabels N ℓ γ, (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2))
      = ∑ j ∈ gradLabels N ℓ γ,
          (1 + circDist ((N : ℕ) : ℝ) ((gradRes N i j : ℕ) : ℝ)) ^ (-(1 + s / 2)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [gradLabelDist_eq_circDist (gradLabels_abs_sub_lt hi hj)]
    rfl
  have hnonneg : ∀ r : ℕ, 0 ≤ (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2)) :=
    fun r => Real.rpow_nonneg (by linarith [circDist_nonneg ((N : ℕ) : ℝ) (r : ℝ)]) _
  have hlab := sum_labels_le_range (N := N) (ℓ := ℓ) (γ := γ) (i := i)
    (fun r : ℕ => (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2))) hnonneg
  rw [hsum_eq]
  refine le_trans hlab ?_
  -- the pointwise domination by two shifted copies of the series
  have hpoint : ∀ r ∈ Finset.range (N : ℕ),
      (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2))
        ≤ (1 + (r : ℝ)) ^ (-(1 + s / 2)) + (1 + (((N : ℕ) - r : ℕ) : ℝ)) ^ (-(1 + s / 2)) := by
    intro r hr
    have hr' : r < (N : ℕ) := Finset.mem_range.mp hr
    have hrR : (r : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast hr'
    have hcast : (((N : ℕ) - r : ℕ) : ℝ) = ((N : ℕ) : ℝ) - (r : ℝ) := Nat.cast_sub hr'.le
    have h1 : (1 + (r : ℝ)) ^ (-(1 + s / 2)) ≥ 0 := Real.rpow_nonneg (by positivity) _
    have h2 : (1 + (((N : ℕ) - r : ℕ) : ℝ)) ^ (-(1 + s / 2)) ≥ 0 :=
      Real.rpow_nonneg (by positivity) _
    rw [circDist_of_range (by exact hNpos) (Nat.cast_nonneg r) hrR]
    rcases min_choice (r : ℝ) (((N : ℕ) : ℝ) - (r : ℝ)) with h | h
    · rw [h]
      linarith
    · rw [h, ← hcast]
      linarith
  have hsum1 : ∑ r ∈ Finset.range (N : ℕ), (1 + (r : ℝ)) ^ (-(1 + s / 2))
      ≤ ∑' m : ℕ, (1 + (m : ℝ)) ^ (-(1 + s / 2)) :=
    hsum.sum_le_tsum _ (fun m _ => Real.rpow_nonneg (by positivity) _)
  have hinj : Set.InjOn (fun r : ℕ => (N : ℕ) - r) ↑(Finset.range (N : ℕ)) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only at hab
    omega
  have hsum2 : ∑ r ∈ Finset.range (N : ℕ), (1 + (((N : ℕ) - r : ℕ) : ℝ)) ^ (-(1 + s / 2))
      ≤ ∑' m : ℕ, (1 + (m : ℝ)) ^ (-(1 + s / 2)) := by
    rw [← Finset.sum_image (f := fun m : ℕ => (1 + (m : ℝ)) ^ (-(1 + s / 2)))
      (g := fun r : ℕ => (N : ℕ) - r) hinj]
    exact hsum.sum_le_tsum _ (fun m _ => Real.rpow_nonneg (by positivity) _)
  calc ∑ r ∈ Finset.range (N : ℕ), (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2))
      ≤ ∑ r ∈ Finset.range (N : ℕ), ((1 + (r : ℝ)) ^ (-(1 + s / 2))
          + (1 + (((N : ℕ) - r : ℕ) : ℝ)) ^ (-(1 + s / 2))) := Finset.sum_le_sum hpoint
    _ = ∑ r ∈ Finset.range (N : ℕ), (1 + (r : ℝ)) ^ (-(1 + s / 2))
          + ∑ r ∈ Finset.range (N : ℕ), (1 + (((N : ℕ) - r : ℕ) : ℝ)) ^ (-(1 + s / 2)) :=
        Finset.sum_add_distrib
    _ ≤ 2 * (∑' m : ℕ, (1 + (m : ℝ)) ^ (-(1 + s / 2))) + 1 := by linarith

/-! ## Conversions between the weights and the path lift -/

/-- The microscopic weight at `N x` is the weight `w_2(x/ℓ)`. -/
lemma gradW2_eq_micro (s a : ℝ) (N : ℕ+) {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) :
    gradWeightTwo s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) = gradW2 s a N ℓ (((N : ℕ) : ℝ) * x) := by
  have hN : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  unfold gradW2
  rw [show ((N : ℕ) : ℝ) / (((N : ℕ) : ℝ) * ℓ) = ℓ⁻¹ by field_simp,
    show ((N : ℕ) : ℝ) * x / (((N : ℕ) : ℝ) * ℓ) = x / ℓ by field_simp]

/-- The weight at the lattice point `x + k/N` is the microscopic weight at `N x + k`. -/
lemma gradW2_eq_micro_shift (s a : ℝ) (N : ℕ+) {ℓ : ℝ} (hℓ : 0 < ℓ) (x k : ℝ) :
    gradWeightTwo s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + k / ((N : ℕ) : ℝ)) / ℓ)
      = gradW2 s a N ℓ (((N : ℕ) : ℝ) * x + k) := by
  have hN : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have h := gradW2_eq_micro s a N hℓ (x + k / ((N : ℕ) : ℝ))
  rw [h]
  congr 1
  field_simp

/-- The microscopic weight at a path lift `x_{i+k}` equals the one at the particle `x_j`, when
`j = i + k + N m` (periodicity of `W_2`). -/
lemma gradW2_gradLift_eq {s a : ℝ} {N : ℕ+} {ℓ : ℝ} (hℓ : 0 < ℓ) (X : Fin (N : ℕ) → ℝ)
    (l j m : ℤ) (hj : j = l + ((N : ℕ) : ℤ) * m) :
    gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X j)
      = gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X l) := by
  have hl : gradLift N X j = gradLift N X l + (m : ℝ) := by
    rw [hj, gradLift_add_mul]
  rw [hl, mul_add, ← gradW2_add_mul s a N hℓ (((N : ℕ) : ℝ) * gradLift N X l) m]
  congr 1
  ring

/-- The power `κ^{-1-s/2}` at `κ ≥ 1` is at most `2^{1+s/2}` times `(1 + κ)^{-(1+s/2)}`. -/
lemma rpow_neg_le_two_pow_one_add {s κa : ℝ} (hs0 : 0 < s) (h1 : 1 ≤ κa) :
    κa ^ (-1 - s / 2) ≤ (2 : ℝ) ^ (1 + s / 2) * (1 + κa) ^ (-(1 + s / 2)) := by
  have he : -1 - s / 2 = -(1 + s / 2) := by ring
  rw [he]
  have h := rpow_le_two_pow_mul_rpow (x := κa) (y := 1 + κa) (e := -(1 + s / 2))
    (by linarith) (by linarith) (by linarith) (by linarith)
  rw [neg_neg] at h
  exact h

/-- The displacement field is the sum over `j ≠ i` of the pair terms. -/
lemma gradV1lab_eq_sum (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) (i : ℤ) :
    gradV1lab s ψ N ℓ γ X i
      = ∑ j ∈ (gradLabels N ℓ γ).erase i,
          (2 * (N : ℝ) ^ (-s) * (gradZx ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
              * gradKernelH s (gradSep N ℓ γ X i j)
            - gradZx ψ ℓ (gradLift N X i) (gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / N)
              * gradKernelH s ((gradPathIncr N ℓ γ i j : ℝ) / N))
          - 2 * (N : ℝ) ^ (-s) * (gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
              - gradZ ψ ℓ (gradLift N X i) (gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / N))
            * deriv (gradKernelH s) ((gradPathIncr N ℓ γ i j : ℝ) / N)) := by
  rw [gradV1lab_eq]
  unfold gradVdisc gradVdisc2
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- The path increment reaches the label `j` up to a whole number of turns:
`j = i + k_{ij} + N m`. -/
lemma exists_path_shift (N : ℕ+) (ℓ γ : ℝ) (i j : ℤ) :
    ∃ m : ℤ, j = i + gradPathIncr N ℓ γ i j + ((N : ℕ) : ℤ) * m := by
  obtain ⟨m0, hm0⟩ := gradPathIncr_emod N ℓ γ i j
  have hdef := Int.emod_def (j - i) ((N : ℕ) : ℤ)
  refine ⟨(j - i) / ((N : ℕ) : ℤ) - m0, ?_⟩
  rw [hm0]
  linarith

/-- The weights of the displacement pair term, expressed through the microscopic `W_2`: the
sum over `j ≠ i` of `(W_x + W_y + W_z) (1 + d)^{-p}` is at most `W_x C_L` plus the particle sum. -/
lemma sum_erase_weight_le {s α γ ε Ca C_L : ℝ} {N : ℕ+} {ℓ : ℝ} {X : Fin (N : ℕ) → ℝ} (_hs0 : 0 < s)
    (hℓ : 0 < ℓ) (_hC_L : 0 ≤ C_L) (hdecay : ∀ i : ℤ, i ∈ gradLabels N ℓ γ →
      ∑ j ∈ gradLabels N ℓ γ, (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2)) ≤ C_L)
    {i : ℤ} (hi : i ∈ gradLabels N ℓ γ) (_hW : 0 ≤ Ca)
    (hpart : ∑ j ∈ gradLabels N ℓ γ,
        (gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X j)
          + gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X i
              + (gradPathIncr N ℓ γ i j : ℝ))) * (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2))
      ≤ Ca * (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε) * (1 + Real.log (((N : ℕ) : ℝ) * ℓ))
        * (gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
          + (((N : ℕ) : ℝ) * ℓ) ^ (1 + (1 - s + α))
            * (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (-(1 + s / 2)))) :
    ∑ j ∈ (gradLabels N ℓ γ).erase i,
        (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
              ((gradLift N X i + gradSep N ℓ γ X i j) / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
              ((gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)) / ℓ))
          * (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2))
      ≤ gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) * C_L
        + Ca * (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε) * (1 + Real.log (((N : ℕ) : ℝ) * ℓ))
          * (gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
            + (((N : ℕ) : ℝ) * ℓ) ^ (1 + (1 - s + α))
              * (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (-(1 + s / 2))) := by
  have hWxnn : 0 ≤ gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) :=
    gradWeightTwo_nonneg_unconditional _ _ _ _ _
  have hterm : ∀ j ∈ (gradLabels N ℓ γ).erase i,
      (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
              ((gradLift N X i + gradSep N ℓ γ X i j) / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
              ((gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)) / ℓ))
          * (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2))
        = gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
            * (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2))
          + (gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X j)
            + gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X i
                + (gradPathIncr N ℓ γ i j : ℝ)))
            * (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2)) := by
    intro j _
    obtain ⟨m, hm⟩ := exists_path_shift N ℓ γ i j
    have hsep : gradLift N X i + gradSep N ℓ γ X i j
        = gradLift N X (i + gradPathIncr N ℓ γ i j) := by
      unfold gradSep
      ring
    have hWy : gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
        ((gradLift N X i + gradSep N ℓ γ X i j) / ℓ)
        = gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X j) := by
      rw [hsep, gradW2_eq_micro s (1 - s + α) N hℓ]
      exact (gradW2_gradLift_eq hℓ X _ j m hm).symm
    have hWz := gradW2_eq_micro_shift s (1 - s + α) N hℓ (gradLift N X i)
      ((gradPathIncr N ℓ γ i j : ℝ))
    rw [hWy, hWz, gradW2_eq_micro s (1 - s + α) N hℓ]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : ∑ j ∈ (gradLabels N ℓ γ).erase i,
      (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2)) ≤ C_L := by
    refine le_trans ?_ (hdecay i hi)
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    intro j hjI _
    have hd : (0 : ℝ) ≤ (gradLabelDist N i j : ℝ) := by
      exact_mod_cast gradLabelDist_nonneg (gradLabels_abs_sub_lt hi hjI)
    exact Real.rpow_nonneg (by linarith) _
  have h2 : ∑ j ∈ (gradLabels N ℓ γ).erase i,
      (gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X j)
        + gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X i
            + (gradPathIncr N ℓ γ i j : ℝ)))
        * (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2))
      ≤ ∑ j ∈ gradLabels N ℓ γ,
        (gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X j)
          + gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X i
              + (gradPathIncr N ℓ γ i j : ℝ))) * (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    intro j hjI _
    have hd : (0 : ℝ) ≤ (gradLabelDist N i j : ℝ) := by
      exact_mod_cast gradLabelDist_nonneg (gradLabels_abs_sub_lt hi hjI)
    exact mul_nonneg (add_nonneg (gradW2_nonneg _ _ _ _ _) (gradW2_nonneg _ _ _ _ _))
      (Real.rpow_nonneg (by linarith) _)
  exact add_le_add (mul_le_mul_of_nonneg_left h1 hWxnn) (le_trans h2 hpart)

/-- The pair term in the decay form: the pair bound with `|k|^{-1-s/2}` replaced by
`2^{1+s/2} (1 + d(i,j))^{-(1+s/2)}`, since `|k_{ij}| = d(i,j)`. -/
lemma pair_decay_le {s α γ ε C₁ C0 ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} {ψ : ℝ → ℝ}
    {i j : ℤ} (hs0 : 0 < s) (hs1 : s < 1) (hα0 : s - 1 ≤ α) (hα1 : α < s / 2) (hC0 : 0 ≤ C0)
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hK : 1 ≤ ((N : ℕ) : ℝ) * ℓ) (hN : 2 ≤ (N : ℕ))
    (hψ : ContDiff ℝ ∞ ψ) (hper : Function.Periodic ψ ℓ⁻¹)
    (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ t)
    (hbd2 : ∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ t)
    (hC₁0 : 0 ≤ C₁)
    (hC_val : ∀ u : ℝ, 0 < |u| → |u| ≤ 3 / 4 → |gradKernelH s u| ≤ C₁ * |u| ^ (-s))
    (hC_der : ∀ u : ℝ, 0 < |u| → |u| ≤ 3 / 4 →
      |iteratedDeriv 1 (gradKernelH s) u| ≤ C₁ * |u| ^ (-s - 1))
    (hε : 0 < ε) (hεs : ε < (1 - s / 2) / 8) (hγ : 1 < γ)
    (hX : gradEvent s γ ε N ℓ X) (hi : i ∈ gradLabels N ℓ γ) (hj : j ∈ gradLabels N ℓ γ)
    (hne : j ≠ i) :
    |2 * ((N : ℕ) : ℝ) ^ (-s) * (gradZx ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
          * gradKernelH s (gradSep N ℓ γ X i j)
        - gradZx ψ ℓ (gradLift N X i) (gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ))
          * gradKernelH s ((gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)))
      - 2 * ((N : ℕ) : ℝ) ^ (-s) * (gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
          - gradZ ψ ℓ (gradLift N X i) (gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)))
          * deriv (gradKernelH s) ((gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ))|
      ≤ (2 * (gradZConst (1 - s + α) s + 1)
            * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2))
          + 6 * (gradZConst (1 - s + α) s + 1) * C₁) * 2 ^ (1 + s / 2) * (C0 * ℓ⁻¹)
        * ((((N : ℕ) : ℝ) * ℓ) ^ ε) ^ (s + 2)
        * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
              ((gradLift N X i + gradSep N ℓ γ X i j) / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
              ((gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)) / ℓ))
        * (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2)) := by
  have hb := gradV1_pair_bound hs0 hs1 hα0 hα1 hC0 hℓ hℓ1 hK hN hψ hper hbd hbd2 hC₁0 hC_val
    hC_der hε hεs hγ hX hi hj hne
  have hκ1 : (1 : ℝ) ≤ |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| := by
    have h := Int.one_le_abs (gradPathIncr_ne_zero hi hj hne)
    have h' : ((1 : ℤ) : ℝ) ≤ ((|(gradPathIncr N ℓ γ i j : ℤ)| : ℤ) : ℝ) := by exact_mod_cast h
    rw [Int.cast_abs] at h'
    simpa using h'
  have hd : |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| = ((gradLabelDist N i j : ℤ) : ℝ) := by
    rw [← Int.cast_abs, abs_gradPathIncr_eq hi hj]
  have hpow' : |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ^ (-1 - s / 2)
      ≤ (2 : ℝ) ^ (1 + s / 2) * (1 + ((gradLabelDist N i j : ℤ) : ℝ)) ^ (-(1 + s / 2)) := by
    have h := rpow_neg_le_two_pow_one_add hs0 hκ1
    rw [hd] at h ⊢
    exact h
  have hA : 0 ≤ (2 * (gradZConst (1 - s + α) s + 1)
            * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2))
          + 6 * (gradZConst (1 - s + α) s + 1) * C₁) := by
    have hg := gradZConst_nonneg (a := 1 - s + α) (s := s) (by linarith) hs1
    have hC2 : 0 ≤ C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2) :=
      mul_nonneg (mul_nonneg hC₁0 (by positivity)) (Real.rpow_nonneg (Real.rpow_nonneg (by norm_num) _) _)
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (gradZConst (1 - s + α) s + 1)) hC2
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 6 * (gradZConst (1 - s + α) s + 1)) hC₁0
    linarith
  have hCS : 0 ≤ (C0 * ℓ⁻¹) * ((((N : ℕ) : ℝ) * ℓ) ^ ε) ^ (s + 2) := by
    have hK0 : (0 : ℝ) ≤ ((N : ℕ) : ℝ) * ℓ := by linarith
    have := Real.rpow_nonneg (Real.rpow_nonneg hK0 ε) (s + 2)
    exact mul_nonneg (mul_nonneg hC0 (inv_nonneg.mpr hℓ.le)) this
  calc _ ≤ (2 * (gradZConst (1 - s + α) s + 1)
            * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2))
          + 6 * (gradZConst (1 - s + α) s + 1) * C₁) * (C0 * ℓ⁻¹)
        * ((((N : ℕ) : ℝ) * ℓ) ^ ε) ^ (s + 2) * |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ^ (-1 - s / 2)
        * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
              ((gradLift N X i + gradSep N ℓ γ X i j) / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
              ((gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)) / ℓ)) := hb
    _ ≤ (2 * (gradZConst (1 - s + α) s + 1)
            * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2))
          + 6 * (gradZConst (1 - s + α) s + 1) * C₁) * (C0 * ℓ⁻¹)
        * ((((N : ℕ) : ℝ) * ℓ) ^ ε) ^ (s + 2)
        * ((2 : ℝ) ^ (1 + s / 2) * (1 + ((gradLabelDist N i j : ℤ) : ℝ)) ^ (-(1 + s / 2)))
        * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
              ((gradLift N X i + gradSep N ℓ γ X i j) / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
              ((gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)) / ℓ)) := by
        have hS : 0 ≤ (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
              ((gradLift N X i + gradSep N ℓ γ X i j) / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
              ((gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)) / ℓ)) := by
          have h1 := gradWeightTwo_nonneg_unconditional s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
            (gradLift N X i / ℓ)
          have h2 := gradWeightTwo_nonneg_unconditional s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
            ((gradLift N X i + gradSep N ℓ γ X i j) / ℓ)
          have h3 := gradWeightTwo_nonneg_unconditional s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
            ((gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)) / ℓ)
          linarith
        have hm := mul_le_mul_of_nonneg_left hpow' (mul_nonneg hA hCS)
        calc _ = _ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hm hS
          _ = _ := by ring
    _ = _ := by ring

/-- The final numerical comparison of the displacement bound: the product of the pair constant, the
lattice powers and the sums is at most the claimed bound with constant `CEf (CL + Ca (1 + 1/ε))`. -/
lemma disp_numeric {CEf C0 ℓinv M Q P L CL Ca ε Wx Y : ℝ} (hCEf : 0 ≤ CEf) (hC0 : 0 ≤ C0)
    (hℓinv : 0 ≤ ℓinv) (hM : 0 ≤ M) (hQ : 1 ≤ Q) (hP : 1 ≤ P) (_hL0 : 0 ≤ L)
    (hL : L ≤ (1 + 1 / ε) * P) (hCL : 0 ≤ CL) (hCa : 0 ≤ Ca) (_hε : 0 < ε) (hWx : 0 ≤ Wx)
    (hY : 0 ≤ Y) :
    CEf * C0 * ℓinv * M * (Wx * CL + Ca * Q * L * (Wx + Y))
      ≤ CEf * (CL + Ca * (1 + 1 / ε)) * C0 * (M * Q * P) * (ℓinv * (Wx + Y)) := by
  have hQP : 1 ≤ Q * P := by nlinarith
  have hcoef : 0 ≤ CEf * C0 * ℓinv * M := by positivity
  have hA : Wx * CL ≤ Wx * CL * (Q * P) := le_mul_of_one_le_right (mul_nonneg hWx hCL) hQP
  have hB : Ca * Q * L * (Wx + Y) ≤ Ca * Q * ((1 + 1 / ε) * P) * (Wx + Y) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_left hL (mul_nonneg hCa (by linarith))
  have hC : Wx * CL + Ca * Q * L * (Wx + Y)
      ≤ Wx * CL * (Q * P) + Ca * Q * ((1 + 1 / ε) * P) * (Wx + Y) := by linarith
  have h1 := mul_le_mul_of_nonneg_left hC hcoef
  have h2 : Wx * CL + Ca * (1 + 1 / ε) * (Wx + Y)
      ≤ (CL + Ca * (1 + 1 / ε)) * (Wx + Y) := by nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ CEf * C0 * ℓinv * (M * Q * P))
  calc CEf * C0 * ℓinv * M * (Wx * CL + Ca * Q * L * (Wx + Y))
      ≤ CEf * C0 * ℓinv * M * (Wx * CL * (Q * P) + Ca * Q * ((1 + 1 / ε) * P) * (Wx + Y)) := h1
    _ = CEf * C0 * ℓinv * (M * Q * P) * (Wx * CL + Ca * (1 + 1 / ε) * (Wx + Y)) := by ring
    _ ≤ CEf * C0 * ℓinv * (M * Q * P) * ((CL + Ca * (1 + 1 / ε)) * (Wx + Y)) := h3
    _ = CEf * (CL + Ca * (1 + 1 / ε)) * C0 * (M * Q * P) * (ℓinv * (Wx + Y)) := by ring

/-- The displacement part of Lemma 5.7. For `s ∈ (0,1)` and `s - 1 ≤ α < s/2`, with
`a = 1 - s + α` and `γ ≥ 4`, there are `ε_* > 0` and `κ > 0` (depending on `s, α, γ`) such that for
every `0 < ε < ε_*` and `C₀ ≥ 0` there is `C` with: on `𝒜_{ε,γ}` and the anchor bound
`|N x_0| ≤ K^ε`, for every label `i ∈ I`,
`|V^{(1)}_i| ≤ C C₀ K^{κε} (ℓ^{-1} W_2(x_i/ℓ) + N K^a / (1 + N|x_i|)^{1+s/2})`. The partial window
vanishing hypothesis on `ψ` concerns the background part only, which cancels in `V^{(1)}`. -/
theorem gradient_splitting_displacement {s α γ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα0 : s - 1 ≤ α) (hα1 : α < s / 2) (hγ : 4 ≤ γ) :
    ∃ εstar : ℝ, 0 < εstar ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < εstar →
      ∃ C : ℝ, 0 < C ∧ ∀ C0 : ℝ, 0 ≤ C0 → ∀ (N : ℕ+) (ℓ : ℝ) (X : Fin (N : ℕ) → ℝ) (ψ : ℝ → ℝ) (i : ℤ),
        2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ ((N : ℕ) : ℝ) * ℓ →
        ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
        (∀ t : ℝ, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ t) →
        (∀ t : ℝ, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ t) →
        (GradPartial N ℓ γ → ∀ x : ℝ, gradT N ℓ γ / 4 ≤ |x| → ψ (x / ℓ) = 0) →
        gradEvent s γ ε N ℓ X →
        |((N : ℕ) : ℝ) * gradLift N X 0| ≤ (((N : ℕ) : ℝ) * ℓ) ^ ε →
        i ∈ gradLabels N ℓ γ →
        |gradV1lab s ψ N ℓ γ X i| ≤
          C * C0 * (((N : ℕ) : ℝ) * ℓ) ^ (κ * ε) *
            (ℓ⁻¹ * gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) +
              ((N : ℕ) : ℝ) * (((N : ℕ) : ℝ) * ℓ) ^ (1 - s + α) /
                (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := (gradient_splitting_kernel s hs0 hs1).2.2.1
  have hC_val : ∀ u : ℝ, 0 < |u| → |u| ≤ 3 / 4 → |gradKernelH s u| ≤ C₁ * |u| ^ (-s) := by
    intro u hu hu34
    have h := (hC₁ u hu hu34).2 0 (Nat.zero_le _)
    simpa using h
  have hC_der : ∀ u : ℝ, 0 < |u| → |u| ≤ 3 / 4 →
      |iteratedDeriv 1 (gradKernelH s) u| ≤ C₁ * |u| ^ (-s - 1) := by
    intro u hu hu34
    have h := (hC₁ u hu hu34).2 1 (by norm_num)
    simpa using h
  obtain ⟨_, _, hpartG⟩ := gradient_splitting_particle_sum_two (a := 1 - s + α) hs0 hs1
    (by linarith) (by linarith)
  obtain ⟨CL, hCL, hdecayG⟩ := sum_labels_decay_le (s := s) hs0
  refine ⟨(1 - s / 2) / 8, by linarith, (s + 2) + (2 + s / 2) + 1, by positivity,
    fun ε hε hεs => ?_⟩
  obtain ⟨Ca, hCa, hpartε⟩ := hpartG ε hε hεs
  have hA1 : 0 < gradZConst (1 - s + α) s + 1 := by
    have := gradZConst_nonneg (a := 1 - s + α) (s := s) (by linarith) hs1
    linarith
  have hN₀pos : (0 : ℝ) < ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2) :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _
  have hp1 : (0 : ℝ) < 2 ^ s + 1 := by
    have := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) s
    linarith
  have hCp : (0 : ℝ) < C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2) :=
    mul_pos (mul_pos hC₁pos hp1) hN₀pos
  have hCEf : (0 : ℝ) < (2 * (gradZConst (1 - s + α) s + 1)
            * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2))
          + 6 * (gradZConst (1 - s + α) s + 1) * C₁) * 2 ^ (1 + s / 2) := by
    have h1 : 0 < 2 * (gradZConst (1 - s + α) s + 1)
        * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2)) :=
      mul_pos (mul_pos (by norm_num) hA1) hCp
    have h2 : 0 < 6 * (gradZConst (1 - s + α) s + 1) * C₁ :=
      mul_pos (mul_pos (by norm_num) hA1) hC₁pos
    exact mul_pos (by linarith) (Real.rpow_pos_of_pos (by norm_num) _)
  have hone : (0 : ℝ) < 1 + 1 / ε := by
    have := one_div_pos.mpr hε
    linarith
  have hCL' : (0 : ℝ) < CL + Ca * (1 + 1 / ε) := by
    have := mul_pos hCa hone
    linarith
  refine ⟨(2 * (gradZConst (1 - s + α) s + 1)
            * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2))
          + 6 * (gradZConst (1 - s + α) s + 1) * C₁) * 2 ^ (1 + s / 2) * (CL + Ca * (1 + 1 / ε)),
    mul_pos hCEf hCL', fun C0 hC0 N ℓ X ψ i hN hℓ hℓ1 hK hψ hper hbd hbd2 _ hX hanch hi => ?_⟩
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hK0 : 0 < ((N : ℕ) : ℝ) * ℓ := by linarith
  have hγ1 : 1 < γ := by linarith
  have hα_a0 : 0 ≤ 1 - s + α := by linarith
  have hα_a1 : 1 - s + α < 1 := by linarith
  have hlam1 : 1 ≤ (((N : ℕ) : ℝ) * ℓ) ^ ε := Real.one_le_rpow hK hε.le
  have hlampos : 0 < (((N : ℕ) : ℝ) * ℓ) ^ ε := Real.rpow_pos_of_pos hK0 _
  have hL : 1 + Real.log (((N : ℕ) : ℝ) * ℓ) ≤ (1 + 1 / ε) * (((N : ℕ) : ℝ) * ℓ) ^ ε := by
    have h := Real.log_le_rpow_div hK0.le hε
    have e : (1 + 1 / ε) * (((N : ℕ) : ℝ) * ℓ) ^ ε
        = (((N : ℕ) : ℝ) * ℓ) ^ ε + (((N : ℕ) : ℝ) * ℓ) ^ ε / ε := by ring
    linarith
  have hL0 : 0 ≤ 1 + Real.log (((N : ℕ) : ℝ) * ℓ) := by
    have := Real.log_nonneg hK
    linarith
  -- the pair terms
  rw [gradV1lab_eq_sum]
  have hterm : ∀ j ∈ (gradLabels N ℓ γ).erase i,
      |2 * ((N : ℕ) : ℝ) ^ (-s) * (gradZx ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
          * gradKernelH s (gradSep N ℓ γ X i j)
        - gradZx ψ ℓ (gradLift N X i) (gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ))
          * gradKernelH s ((gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)))
      - 2 * ((N : ℕ) : ℝ) ^ (-s) * (gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
          - gradZ ψ ℓ (gradLift N X i) (gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)))
          * deriv (gradKernelH s) ((gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ))|
      ≤ ((2 * (gradZConst (1 - s + α) s + 1)
            * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2))
          + 6 * (gradZConst (1 - s + α) s + 1) * C₁) * 2 ^ (1 + s / 2) * (C0 * ℓ⁻¹)
        * (((((N : ℕ) : ℝ) * ℓ) ^ ε)) ^ (s + 2))
        * ((gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
              ((gradLift N X i + gradSep N ℓ γ X i j) / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
              ((gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)) / ℓ))
          * (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2))) := by
    intro j hj
    have hjI := Finset.mem_of_mem_erase hj
    have hne := Finset.ne_of_mem_erase hj
    have h := pair_decay_le hs0 hs1 hα0 hα1 hC0 hℓ hℓ1 hK hN hψ hper hbd hbd2 hC₁pos.le hC_val
      hC_der hε hεs hγ1 hX hi hjI hne
    exact le_of_le_of_eq h (by ring)
  -- the particle sum, in multiplicative form
  have hyX : 0 ≤ 1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i) := by
    have h1 : 0 ≤ circDist 1 (gradLift N X i) := circDist_nonneg _ _
    have h2 : 0 ≤ ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i) := mul_nonneg hN0.le h1
    linarith
  have hdn : ∀ j ∈ gradLabels N ℓ γ, 0 ≤ 1 + (gradLabelDist N i j : ℝ) := by
    intro j hj
    have h : (0 : ℝ) ≤ (gradLabelDist N i j : ℝ) := by
      exact_mod_cast gradLabelDist_nonneg (gradLabels_abs_sub_lt hi hj)
    linarith
  have hpart' : ∑ j ∈ gradLabels N ℓ γ,
        (gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X j)
          + gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ)))
          * (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2))
      ≤ Ca * (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε) * (1 + Real.log (((N : ℕ) : ℝ) * ℓ))
        * (gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
          + (((N : ℕ) : ℝ) * ℓ) ^ (1 + (1 - s + α))
            * (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (-(1 + s / 2))) := by
    have hpartε' := hpartε γ N ℓ X i hγ1 hN hℓ hℓ1 hK hX hi
    have e1 : ∑ j ∈ gradLabels N ℓ γ,
          (gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X j)
            + gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ)))
            * (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2))
        = ∑ j ∈ gradLabels N ℓ γ,
          (gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X j)
            + gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ)))
            / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [div_rpow_eq_mul_rpow_neg (hdn j hj)]
    have e2 : (((N : ℕ) : ℝ) * ℓ) ^ (1 + (1 - s + α))
        / (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)
        = (((N : ℕ) : ℝ) * ℓ) ^ (1 + (1 - s + α))
          * (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (-(1 + s / 2)) :=
      div_rpow_eq_mul_rpow_neg hyX
    rw [e1]
    refine le_trans hpartε' ?_
    rw [e2]
  have hWx_eq : gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
      = gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) :=
    (gradW2_eq_micro s (1 - s + α) N hℓ (gradLift N X i)).symm
  have hW := sum_erase_weight_le (s := s) (α := α) (γ := γ) (ε := ε) (Ca := Ca) (C_L := CL)
    (N := N) (ℓ := ℓ) (X := X) hs0 hℓ hCL.le (fun i' hi' => hdecayG N ℓ γ i' hN hi') hi hCa.le hpart'
  rw [hWx_eq] at hW
  have hKκ : (((N : ℕ) : ℝ) * ℓ) ^ (((s + 2) + (2 + s / 2) + 1) * ε)
      = (((N : ℕ) : ℝ) * ℓ) ^ (ε * (s + 2)) * (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε)
        * (((N : ℕ) : ℝ) * ℓ) ^ ε := by
    rw [← Real.rpow_add hK0, ← Real.rpow_add hK0]
    congr 1
    ring
  have hMeq : (((N : ℕ) : ℝ) * ℓ) ^ (ε * (s + 2)) = ((((N : ℕ) : ℝ) * ℓ) ^ ε) ^ (s + 2) :=
    Real.rpow_mul hK0.le ε (s + 2)
  have hQ1 : 1 ≤ (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε) :=
    Real.one_le_rpow hK (mul_nonneg (by linarith) hε.le)
  have hWxnn : 0 ≤ gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) :=
    gradWeightTwo_nonneg_unconditional _ _ _ _ _
  have hYnn : 0 ≤ (((N : ℕ) : ℝ) * ℓ) ^ (1 + (1 - s + α))
      * (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (-(1 + s / 2)) :=
    mul_nonneg (Real.rpow_nonneg hK0.le _) (Real.rpow_nonneg hyX _)
  have hY : ℓ⁻¹ * ((((N : ℕ) : ℝ) * ℓ) ^ (1 + (1 - s + α))
      * (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (-(1 + s / 2)))
      = ((N : ℕ) : ℝ) * (((N : ℕ) : ℝ) * ℓ) ^ (1 - s + α)
        / (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2) := by
    rw [div_rpow_eq_mul_rpow_neg hyX, Real.rpow_add hK0, Real.rpow_one]
    field_simp
  have hK1 : 0 ≤ ((2 * (gradZConst (1 - s + α) s + 1)
            * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2))
          + 6 * (gradZConst (1 - s + α) s + 1) * C₁) * 2 ^ (1 + s / 2)) * (C0 * ℓ⁻¹)
        * ((((N : ℕ) : ℝ) * ℓ) ^ ε) ^ (s + 2) :=
    mul_nonneg (mul_nonneg hCEf.le (mul_nonneg hC0 (inv_nonneg.mpr hℓ.le)))
      (Real.rpow_nonneg hlampos.le _)
  have hsum1 := le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
  rw [← Finset.mul_sum] at hsum1
  have hfin1 := le_trans hsum1 (mul_le_mul_of_nonneg_left hW hK1)
  set Wx := gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) with hWx_def
  set Y := (((N : ℕ) : ℝ) * ℓ) ^ (1 + (1 - s + α))
      * (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (-(1 + s / 2)) with hY_def
  set M := ((((N : ℕ) : ℝ) * ℓ) ^ ε) ^ (s + 2) with hM_def
  set Q := (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε) with hQ_def
  set Pp := (((N : ℕ) : ℝ) * ℓ) ^ ε with hPp_def
  set L := 1 + Real.log (((N : ℕ) : ℝ) * ℓ) with hL_def
  set CEf := (2 * (gradZConst (1 - s + α) s + 1)
            * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2))
          + 6 * (gradZConst (1 - s + α) s + 1) * C₁) * 2 ^ (1 + s / 2) with hCEf_def
  calc _ ≤ CEf * (C0 * ℓ⁻¹) * M * (Wx * CL + Ca * Q * L * (Wx + Y)) := hfin1
    _ = CEf * C0 * ℓ⁻¹ * M * (Wx * CL + Ca * Q * L * (Wx + Y)) := by ring
    _ ≤ CEf * (CL + Ca * (1 + 1 / ε)) * C0 * (M * Q * Pp) * (ℓ⁻¹ * (Wx + Y)) :=
        disp_numeric hCEf.le hC0 (inv_nonneg.mpr hℓ.le) (Real.rpow_nonneg hlampos.le _) hQ1 hlam1
          hL0 hL hCL.le hCa.le hε hWxnn hYnn
    _ = (CEf * (CL + Ca * (1 + 1 / ε))) * C0 * ((((N : ℕ) : ℝ) * ℓ) ^ (((s + 2) + (2 + s / 2) + 1) * ε))
          * (ℓ⁻¹ * Wx + ((N : ℕ) : ℝ) * (((N : ℕ) : ℝ) * ℓ) ^ (1 - s + α)
            / (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)) := by
        rw [hKκ, hMeq, mul_add ℓ⁻¹ Wx Y, hY]

end

end Riesz1
