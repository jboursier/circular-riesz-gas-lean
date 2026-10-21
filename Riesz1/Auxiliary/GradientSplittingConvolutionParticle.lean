/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingConvolutionCell
public import Riesz1.Auxiliary.GradientSplittingConvolutionEvent

/-!
# Particle sums of the gradient-splitting weights

The convolution part of Lemma 5.7, the particle-level claims on
the event `𝒜_{ε,γ}`:

* `Riesz1.gradient_splitting_particle_sum_two`: for `i ∈ I`, the sum over `j ∈ I` of
  `(W_2(Nx_j) + W_2(Nx_i + k_{ij})) / (1 + d(i,j))^{1+s/2}` is at most
  `C K^{κε} (1 + log K) (W_2(Nx_i) + K^{1+a} / (1 + N|x_i|)^{1+s/2})`.
* `Riesz1.gradient_splitting_particle_sum_sq`: the sum over `j ∈ I` of `W_1(Nx_j)^2` is at most
  `C K^{κε} (K + K^{2a}) (1 + log K)`.

Here `K = Nℓ`, `d(i,j) = gradLabelDist N i j`, `k_{ij} = gradPathIncr N ℓ γ i j`, and the weights
`W_m` are `gradW2`, `gradW1` of `Riesz1/Auxiliary/GradientSplittingConvolutionCell.lean`.

Proof outline. Each particle `j` is assigned to the cell `r = gradCell N w x_j ∈ {0, …, N-1}`, where
`w = ⌊Nx_i⌋`. The packing bound `gradient_splitting_packing` gives at most `2 + K^ε` particles per
cell. Within a cell, the weights and the distance factor are compared with their values at the
lattice point `w + r` (`Riesz1.gradW2_cell_le`, `gradLabel_rpow_le`). The lattice sums of
the convolution part of Lemma 5.7 then bound the cell sum. For the second term, the labels
`j ∈ I` give distinct residues `(j - i) mod N`, and the sum is bounded by the lattice sum at `Nx_i`.
-/

@[expose] public section

open Finset

namespace Riesz1

noncomputable section

/-! ## Circular distance and labels -/

/-- The circular distance on a range `[0, L)`: it is `min(u, L - u)`. -/
lemma circDist_of_range {L u : ℝ} (hL : 0 < L) (h0 : 0 ≤ u) (h1 : u < L) :
    circDist L u = min u (L - u) := by
  rcases le_total (2 * u) L with h | h
  · rw [circDist_of_mem_Icc hL h0 (by linarith), min_eq_left (by linarith)]
  · have e : circDist L u = circDist L (L - u) := by
      have h' := circDist_add_int_mul hL (-(L - u)) 1
      rw [show -(L - u) + ((1 : ℤ) : ℝ) * L = u by push_cast; ring, circDist_neg hL] at h'
      exact h'
    rw [e, circDist_of_mem_Icc hL (by linarith) (by linarith), min_eq_right (by linarith)]

/-- Rescaling: `circDist M (M u) = M · circDist 1 u`. -/
lemma circDist_mul_self_scale {M : ℝ} (hM : 0 < M) (u : ℝ) :
    circDist M (M * u) = M * circDist 1 u := by
  have h := circDist_scale hM M (M * u)
  rw [div_self hM.ne', mul_div_cancel_left₀ u hM.ne'] at h
  rw [h]
  field_simp

/-- A label `j` of the window satisfies `|j - i| < N` when `i` is also a label. -/
lemma gradLabels_abs_sub_lt {ℓ γ : ℝ} {N : ℕ+} {i j : ℤ} (hi : i ∈ gradLabels N ℓ γ)
    (hj : j ∈ gradLabels N ℓ γ) : |j - i| < ((N : ℕ) : ℤ) := by
  by_cases hP : GradPartial N ℓ γ
  · rw [mem_gradLabels_partial hP] at hi hj
    have hPN : gradM N ℓ γ < (N : ℝ) / 8 := hP
    have hM : ((⌊gradM N ℓ γ⌋ : ℤ) : ℝ) ≤ gradM N ℓ γ := Int.floor_le _
    have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
    have hlt : 2 * ⌊gradM N ℓ γ⌋ < ((N : ℕ) : ℤ) := by
      have h2 : (2 * (⌊gradM N ℓ γ⌋ : ℝ)) < ((N : ℕ) : ℝ) := by linarith
      exact_mod_cast h2
    rw [abs_lt]
    constructor <;> omega
  · rw [mem_gradLabels_full hP] at hi hj
    rw [abs_lt]
    constructor <;> omega

/-- The label distance is nonnegative on the window. -/
lemma gradLabelDist_nonneg {N : ℕ+} {i j : ℤ} (h : |j - i| < ((N : ℕ) : ℤ)) :
    0 ≤ gradLabelDist N i j := by
  unfold gradLabelDist
  exact le_min (abs_nonneg _) (by linarith)

/-- The label distance is the circular distance of the residue of `j - i` modulo `N`. -/
lemma gradLabelDist_eq_circDist {N : ℕ+} {i j : ℤ} (h : |j - i| < ((N : ℕ) : ℤ)) :
    ((gradLabelDist N i j : ℤ) : ℝ)
      = circDist ((N : ℕ) : ℝ) ((((j - i) % ((N : ℕ) : ℤ)).toNat : ℕ) : ℝ) := by
  have hNz : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  have hr0 : 0 ≤ (j - i) % ((N : ℕ) : ℤ) := Int.emod_nonneg _ hNz.ne'
  have hr1 : (j - i) % ((N : ℕ) : ℤ) < ((N : ℕ) : ℤ) := Int.emod_lt_of_pos _ hNz
  have hcast : ((((j - i) % ((N : ℕ) : ℤ)).toNat : ℕ) : ℝ)
      = ((((j - i) % ((N : ℕ) : ℤ)) : ℤ) : ℝ) := by
    have h' := Int.toNat_of_nonneg hr0
    exact_mod_cast h'
  have hint : gradLabelDist N i j
      = min ((j - i) % ((N : ℕ) : ℤ)) (((N : ℕ) : ℤ) - (j - i) % ((N : ℕ) : ℤ)) := by
    unfold gradLabelDist
    rcases lt_or_ge (j - i) 0 with ht | ht
    · have hgt : -((N : ℕ) : ℤ) < j - i := (abs_lt.mp h).1
      have hr : (j - i) % ((N : ℕ) : ℤ) = (j - i) + ((N : ℕ) : ℤ) := by
        have h1 : ((j - i) + ((N : ℕ) : ℤ) * 1) % ((N : ℕ) : ℤ) = (j - i) % ((N : ℕ) : ℤ) :=
          Int.add_mul_emod_self_left (j - i) ((N : ℕ) : ℤ) 1
        rw [← h1, mul_one]
        exact Int.emod_eq_of_lt (by linarith) (by linarith)
      rw [hr, abs_of_neg ht]
      simp only [min_def]
      split_ifs <;> omega
    · have hlt : j - i < ((N : ℕ) : ℤ) := (abs_lt.mp h).2
      rw [Int.emod_eq_of_lt ht hlt, abs_of_nonneg ht]
  have hR := circDist_of_range (L := ((N : ℕ) : ℝ))
    (u := (((j - i) % ((N : ℕ) : ℤ) : ℤ) : ℝ)) (by exact_mod_cast N.pos)
    (by exact_mod_cast hr0) (by exact_mod_cast hr1)
  rw [hcast, hR, hint]
  push_cast
  ring_nf

/-- Injectivity of the residue of `j - i` on labels at distance less than `N`. -/
lemma emod_inj_of_abs_sub_lt {N : ℕ+} {i j j' : ℤ} (h : (j - i) % ((N : ℕ) : ℤ)
    = (j' - i) % ((N : ℕ) : ℤ)) (hj : |j - j'| < ((N : ℕ) : ℤ)) : j = j' := by
  have h2 : ((j - i) - (j' - i)) % ((N : ℕ) : ℤ) = 0 := by
    rw [Int.sub_emod, h, sub_self, Int.zero_emod]
  have hd := Int.dvd_of_emod_eq_zero h2
  have h3 := Int.eq_zero_of_abs_lt_dvd hd (by rw [show (j - i) - (j' - i) = j - j' by ring]; exact hj)
  linarith

/-- The residue of the path increment: `k_{ij} ≡ j - i` modulo `N`. -/
lemma gradPathIncr_emod (N : ℕ+) (ℓ γ : ℝ) (i j : ℤ) :
    ∃ m : ℤ, gradPathIncr N ℓ γ i j = (j - i) % ((N : ℕ) : ℤ) + ((N : ℕ) : ℤ) * m := by
  unfold gradPathIncr
  split_ifs
  · exact ⟨(j - i) / ((N : ℕ) : ℤ), by rw [Int.emod_def]; ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨-1, by ring⟩
  · refine ⟨0, ?_⟩
    generalize (j - i) % ((N : ℕ) : ℤ) = r at *
    omega
  · refine ⟨-1, ?_⟩
    generalize (j - i) % ((N : ℕ) : ℤ) = r at *
    omega

/-! ## Microscopic weights at path lifts -/

/-- The microscopic `W_2` at the path lift `N x_i + k_{ij}` equals its value at the residue
`N x_i + ((j - i) mod N)`. -/
lemma gradW2_path (s a γ : ℝ) (N : ℕ+) {ℓ : ℝ} (hℓ : 0 < ℓ) (z : ℝ) (i j : ℤ) :
    gradW2 s a N ℓ (z + ((gradPathIncr N ℓ γ i j : ℤ) : ℝ))
      = gradW2 s a N ℓ (z + (((j - i) % ((N : ℕ) : ℤ) : ℤ) : ℝ)) := by
  obtain ⟨m, hm⟩ := gradPathIncr_emod N ℓ γ i j
  have e : z + ((gradPathIncr N ℓ γ i j : ℤ) : ℝ)
      = (z + (((j - i) % ((N : ℕ) : ℤ) : ℤ) : ℝ)) + (m : ℝ) * ((N : ℕ) : ℝ) := by
    rw [hm]
    push_cast
    ring
  rw [e, gradW2_add_mul s a N hℓ]

/-- The microscopic `W_2` is nonnegative. -/
lemma gradW2_nonneg (s a : ℝ) (N : ℕ+) (ℓ z : ℝ) : 0 ≤ gradW2 s a N ℓ z := by
  unfold gradW2
  exact gradWeightTwo_nonneg_unconditional _ _ _ _ _

/-- The microscopic `W_1` is nonnegative. -/
lemma gradW1_nonneg (s a : ℝ) (N : ℕ+) (ℓ z : ℝ) : 0 ≤ gradW1 s a N ℓ z := by
  unfold gradW1
  exact gradWeightOne_nonneg_unconditional _ _ _ _ _

/-- Division by a real power is multiplication by the power with the negative exponent. -/
lemma div_rpow_eq_mul_rpow_neg {x y p : ℝ} (hy : 0 ≤ y) : x / y ^ p = x * y ^ (-p) := by
  rw [Real.rpow_neg hy, div_eq_mul_inv]

/-! ## Cells -/

/-- The cell of a point `x` of the circle relative to the origin `w`: the residue of
`⌊N x⌋ - w` modulo `N`, as a natural number in `{0, …, N-1}`. -/
def gradCell (N : ℕ+) (w : ℤ) (x : ℝ) : ℕ :=
  ((⌊((N : ℕ) : ℝ) * x⌋ - w) % ((N : ℕ) : ℤ)).toNat

/-- A cell index is less than `N`. -/
lemma gradCell_lt (N : ℕ+) (w : ℤ) (x : ℝ) : gradCell N w x < (N : ℕ) := by
  unfold gradCell
  have hN : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  exact (Int.toNat_lt (Int.emod_nonneg _ hN.ne')).mpr (Int.emod_lt_of_pos _ hN)

/-- The particles of the window, sorted by their cell, sum to the total. -/
lemma sum_cell_fiber {ℓ γ : ℝ} {N : ℕ+} (X : Fin (N : ℕ) → ℝ) (w : ℤ) (F : ℤ → ℝ) :
    ∑ j ∈ gradLabels N ℓ γ, F j
      = ∑ r ∈ Finset.range (N : ℕ),
          ∑ j ∈ (gradLabels N ℓ γ).filter (fun j => gradCell N w (gradLift N X j) = r), F j :=
  (Finset.sum_fiberwise_of_maps_to
    (g := fun j => gradCell N w (gradLift N X j)) (t := Finset.range (N : ℕ))
    (fun _ _ => Finset.mem_range.mpr (gradCell_lt N w _)) F).symm

/-- Packing per cell: at most `2 + K^ε` labels of the window lie in one cell
(convolution part of Lemma 5.7). -/
lemma card_filter_cell_le {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} (hs0 : 0 < s)
    (hγ : 1 < γ) (hε : 0 < ε) (hεs : ε < (1 - s / 2) / 8) (hK : 1 ≤ ((N : ℕ) : ℝ) * ℓ)
    (hN : 2 ≤ (N : ℕ)) (hX : gradEvent s γ ε N ℓ X) (w : ℤ) (r : ℕ) :
    (((gradLabels N ℓ γ).filter (fun j => gradCell N w (gradLift N X j) = r)).card : ℝ)
      ≤ 2 + (((N : ℕ) : ℝ) * ℓ) ^ ε := by
  have hT : (gradLabels N ℓ γ).filter (fun j => gradCell N w (gradLift N X j) = r)
      ⊆ gradLabels N ℓ γ := Finset.filter_subset _ _
  refine gradient_splitting_packing hs0 hγ hε hεs hK hN hX ((w : ℝ) + (r : ℝ)) hT ?_
  intro j hj
  obtain ⟨_, hjc⟩ := Finset.mem_filter.mp hj
  have hNz : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  have hnn := Int.emod_nonneg (⌊((N : ℕ) : ℝ) * gradLift N X j⌋ - w) hNz.ne'
  have hmod : (⌊((N : ℕ) : ℝ) * gradLift N X j⌋ - w) % ((N : ℕ) : ℤ) = (r : ℤ) := by
    unfold gradCell at hjc
    have h' := Int.toNat_of_nonneg hnn
    rw [hjc] at h'
    exact h'.symm
  have hdef := Int.emod_def (⌊((N : ℕ) : ℝ) * gradLift N X j⌋ - w) ((N : ℕ) : ℤ)
  rw [hmod] at hdef
  have hid : (⌊((N : ℕ) : ℝ) * gradLift N X j⌋ : ℤ)
      = w + (r : ℤ) + ((N : ℕ) : ℤ) * ((⌊((N : ℕ) : ℝ) * gradLift N X j⌋ - w) / ((N : ℕ) : ℤ)) := by
    linarith
  have hidR : ((⌊((N : ℕ) : ℝ) * gradLift N X j⌋ : ℤ) : ℝ)
      = ((w : ℝ) + (r : ℝ)) + ((N : ℕ) : ℝ) * (((⌊((N : ℕ) : ℝ) * gradLift N X j⌋ - w)
          / ((N : ℕ) : ℤ) : ℤ) : ℝ) := by
    have h' := congrArg (fun z : ℤ => (z : ℝ)) hid
    push_cast at h'
    linarith
  refine ⟨(⌊((N : ℕ) : ℝ) * gradLift N X j⌋ - w) / ((N : ℕ) : ℤ), ?_, ?_⟩
  · rw [← hidR]
    exact Int.floor_le _
  · rw [← hidR]
    exact Int.lt_floor_add_one _

/-! ## Distance comparison -/

/-- The label-distance factor of the particle sum is bounded by the microscopic one:
`(1 + d(i,j))^{-p} ≤ K^{εp} (1 + D)^{-p}` with `D = circDist N (N(x_j - x_i))`, on `𝒜_{ε,γ}`. -/
lemma gradLabel_rpow_le {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} (hs0 : 0 < s)
    (hγ : 1 < γ) (hε : 0 < ε) (hεs : ε < (1 - s / 2) / 8) (hK : 1 ≤ ((N : ℕ) : ℝ) * ℓ)
    (hX : gradEvent s γ ε N ℓ X) {i j : ℤ} (hi : i ∈ gradLabels N ℓ γ)
    (hj : j ∈ gradLabels N ℓ γ) :
    (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2))
      ≤ (((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2))
        * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * (gradLift N X j - gradLift N X i))) ^ (-(1 + s / 2)) := by
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hK0 : 0 < ((N : ℕ) : ℝ) * ℓ := by linarith
  obtain ⟨h1, h2⟩ := gradient_splitting_comparison hs0 hγ hε hεs hK hX hi hj
  have hDeq := circDist_mul_self_scale hN0 (gradLift N X j - gradLift N X i)
  rw [← hDeq] at h1 h2
  have hd0 : (0 : ℝ) ≤ (gradLabelDist N i j : ℝ) := by
    have := gradLabelDist_nonneg (N := N) (i := i) (j := j)
      (gradLabels_abs_sub_lt hi hj)
    exact_mod_cast this
  have hD0 : 0 ≤ circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * (gradLift N X j - gradLift N X i)) :=
    circDist_nonneg _ _
  have hKe : (((N : ℕ) : ℝ) * ℓ) ^ (-ε) * (((N : ℕ) : ℝ) * ℓ) ^ ε = 1 := by
    rw [← Real.rpow_add hK0, neg_add_cancel, Real.rpow_zero]
  have hKle : (((N : ℕ) : ℝ) * ℓ) ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hK (by linarith)
  have hKpos : 0 < (((N : ℕ) : ℝ) * ℓ) ^ (-ε) := Real.rpow_pos_of_pos hK0 _
  -- the key comparison `K^{-ε}(1 + D) ≤ 1 + d`
  have h3 : (((N : ℕ) : ℝ) * ℓ) ^ (-ε)
      * circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * (gradLift N X j - gradLift N X i))
      ≤ (gradLabelDist N i j : ℝ) := by
    calc (((N : ℕ) : ℝ) * ℓ) ^ (-ε)
          * circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * (gradLift N X j - gradLift N X i))
        ≤ (((N : ℕ) : ℝ) * ℓ) ^ (-ε)
          * ((((N : ℕ) : ℝ) * ℓ) ^ ε * (gradLabelDist N i j : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 hKpos.le
      _ = ((((N : ℕ) : ℝ) * ℓ) ^ (-ε) * (((N : ℕ) : ℝ) * ℓ) ^ ε) * (gradLabelDist N i j : ℝ) := by
          ring
      _ = (gradLabelDist N i j : ℝ) := by rw [hKe, one_mul]
  have h4 : (((N : ℕ) : ℝ) * ℓ) ^ (-ε) * (1 + circDist ((N : ℕ) : ℝ)
      (((N : ℕ) : ℝ) * (gradLift N X j - gradLift N X i)))
      ≤ 1 + (gradLabelDist N i j : ℝ) := by
    have e : (((N : ℕ) : ℝ) * ℓ) ^ (-ε) * (1 + circDist ((N : ℕ) : ℝ)
        (((N : ℕ) : ℝ) * (gradLift N X j - gradLift N X i)))
        = (((N : ℕ) : ℝ) * ℓ) ^ (-ε) + (((N : ℕ) : ℝ) * ℓ) ^ (-ε)
          * circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * (gradLift N X j - gradLift N X i)) := by
      ring
    rw [e]
    linarith
  have h5 : (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2))
      ≤ ((((N : ℕ) : ℝ) * ℓ) ^ (-ε) * (1 + circDist ((N : ℕ) : ℝ)
        (((N : ℕ) : ℝ) * (gradLift N X j - gradLift N X i)))) ^ (-(1 + s / 2)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h4 (by linarith)
  have hsplit : ((((N : ℕ) : ℝ) * ℓ) ^ (-ε) * (1 + circDist ((N : ℕ) : ℝ)
      (((N : ℕ) : ℝ) * (gradLift N X j - gradLift N X i)))) ^ (-(1 + s / 2))
      = ((((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2))) * (1 + circDist ((N : ℕ) : ℝ)
        (((N : ℕ) : ℝ) * (gradLift N X j - gradLift N X i))) ^ (-(1 + s / 2)) := by
    rw [Real.mul_rpow hKpos.le (by linarith), ← Real.rpow_mul hK0.le]
    congr 2
    ring
  rw [hsplit] at h5
  exact h5

/-- The integer cell identity: `⌊N x⌋ = w + r + N m` with `r` the cell of `x`. -/
lemma gradCell_floor_eq (N : ℕ+) (w : ℤ) (x : ℝ) :
    ∃ m : ℤ, ⌊((N : ℕ) : ℝ) * x⌋ = w + ((gradCell N w x : ℕ) : ℤ) + ((N : ℕ) : ℤ) * m := by
  have hNz : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  have hnn := Int.emod_nonneg (⌊((N : ℕ) : ℝ) * x⌋ - w) hNz.ne'
  have h' := Int.toNat_of_nonneg hnn
  have hdef := Int.emod_def (⌊((N : ℕ) : ℝ) * x⌋ - w) ((N : ℕ) : ℤ)
  refine ⟨(⌊((N : ℕ) : ℝ) * x⌋ - w) / ((N : ℕ) : ℤ), ?_⟩
  unfold gradCell
  rw [← h'] at hdef
  linarith

/-! ## The first term: per cell -/

/-- Per-particle bound for the first term `W_2(Nx_j)/(1+d(i,j))^{1+s/2}`, for a particle `j` of cell
`r` relative to the origin `w`, when `|Nx_i - w| ≤ 1`. -/
lemma particle_first_term_le {s a γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (ha0 : 0 ≤ a) (hγ : 1 < γ) (hε : 0 < ε) (hεs : ε < (1 - s / 2) / 8)
    (hℓ : 0 < ℓ) (hK : 1 ≤ ((N : ℕ) : ℝ) * ℓ) (hX : gradEvent s γ ε N ℓ X) {i j : ℤ}
    (hi : i ∈ gradLabels N ℓ γ) (hj : j ∈ gradLabels N ℓ γ) (w : ℤ)
    (hw : |((N : ℕ) : ℝ) * gradLift N X i - (w : ℝ)| ≤ 1) (r : ℕ)
    (hr : gradCell N w (gradLift N X j) = r) :
    gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X j) / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2)
      ≤ 2 ^ (4 + a) * 2 ^ (1 + s / 2) * 2 ^ (1 + s / 2) * (((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2))
        * (gradW2 s a N ℓ ((w : ℝ) + (r : ℝ)) * (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2))) := by
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hd0 : (0 : ℝ) ≤ (gradLabelDist N i j : ℝ) := by
    exact_mod_cast gradLabelDist_nonneg (gradLabels_abs_sub_lt hi hj)
  obtain ⟨m, hm⟩ := gradCell_floor_eq N w (gradLift N X j)
  rw [hr] at hm
  have hqR : ((⌊((N : ℕ) : ℝ) * gradLift N X j⌋ : ℤ) : ℝ)
      = (w : ℝ) + (r : ℝ) + (m : ℝ) * ((N : ℕ) : ℝ) := by
    rw [hm]
    push_cast
    ring
  have hfl1 : ((⌊((N : ℕ) : ℝ) * gradLift N X j⌋ : ℤ) : ℝ) ≤ ((N : ℕ) : ℝ) * gradLift N X j :=
    Int.floor_le _
  have hfl2 : ((N : ℕ) : ℝ) * gradLift N X j < ((⌊((N : ℕ) : ℝ) * gradLift N X j⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hQ : |((⌊((N : ℕ) : ℝ) * gradLift N X j⌋ : ℤ) : ℝ) - ((N : ℕ) : ℝ) * gradLift N X j| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  -- Step 1: the cell comparison of the weight, and periodicity
  have hstep1 : gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X j)
      ≤ 2 ^ (4 + a) * gradW2 s a N ℓ ((w : ℝ) + (r : ℝ)) := by
    have h := gradW2_cell_le s a hs0 hs1 ha0 N hK
      (circDist_le_add_one_of_abs_sub_le hN0 hQ)
    rw [hqR, gradW2_add_mul s a N hℓ] at h
    exact h
  -- Step 2: the distance factor against the microscopic one
  have hdist := gradLabel_rpow_le hs0 hγ hε hεs hK hX hi hj
  -- Step 3: the microscopic distances `D` and `E` differ by at most one
  have hE : |circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * (gradLift N X j - gradLift N X i))
      - circDist ((N : ℕ) : ℝ) ((w : ℝ) + (r : ℝ) - ((N : ℕ) : ℝ) * gradLift N X i)| ≤ 1 := by
    have h1 := abs_circDist_sub_circDist_le (L := ((N : ℕ) : ℝ))
      (a := ((N : ℕ) : ℝ) * (gradLift N X j - gradLift N X i))
      (b := (w : ℝ) + (r : ℝ) - ((N : ℕ) : ℝ) * gradLift N X i) hN0
    have e : ((N : ℕ) : ℝ) * (gradLift N X j - gradLift N X i)
        - ((w : ℝ) + (r : ℝ) - ((N : ℕ) : ℝ) * gradLift N X i)
        = (((N : ℕ) : ℝ) * gradLift N X j - ((⌊((N : ℕ) : ℝ) * gradLift N X j⌋ : ℤ) : ℝ))
          + (m : ℝ) * ((N : ℕ) : ℝ) := by
      rw [hqR]
      ring
    rw [e, circDist_add_int_mul hN0] at h1
    have h2 := circDist_le_abs_self hN0
      (((N : ℕ) : ℝ) * gradLift N X j - ((⌊((N : ℕ) : ℝ) * gradLift N X j⌋ : ℤ) : ℝ))
    have h3 : |((N : ℕ) : ℝ) * gradLift N X j - ((⌊((N : ℕ) : ℝ) * gradLift N X j⌋ : ℤ) : ℝ)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hD0 : 0 ≤ circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * (gradLift N X j - gradLift N X i)) :=
    circDist_nonneg _ _
  have hE0 : 0 ≤ circDist ((N : ℕ) : ℝ) ((w : ℝ) + (r : ℝ) - ((N : ℕ) : ℝ) * gradLift N X i) :=
    circDist_nonneg _ _
  have hpow1 := rpow_one_add_neg_le_two_pow (p := 1 + s / 2) (by positivity) hD0 hE0 hE
  -- Step 4: the microscopic distance `E` against `circDist N r`
  have hF : |circDist ((N : ℕ) : ℝ) ((w : ℝ) + (r : ℝ) - ((N : ℕ) : ℝ) * gradLift N X i)
      - circDist ((N : ℕ) : ℝ) (r : ℝ)| ≤ 1 := by
    have h1 := abs_circDist_sub_circDist_le (L := ((N : ℕ) : ℝ))
      (a := (w : ℝ) + (r : ℝ) - ((N : ℕ) : ℝ) * gradLift N X i) (b := (r : ℝ)) hN0
    have e : (w : ℝ) + (r : ℝ) - ((N : ℕ) : ℝ) * gradLift N X i - (r : ℝ)
        = (w : ℝ) - ((N : ℕ) : ℝ) * gradLift N X i := by
      ring
    rw [e] at h1
    have h2 := circDist_le_abs_self hN0 ((w : ℝ) - ((N : ℕ) : ℝ) * gradLift N X i)
    have h3 : |(w : ℝ) - ((N : ℕ) : ℝ) * gradLift N X i| ≤ 1 := by
      rw [abs_sub_comm]
      exact hw
    linarith
  have hpow2 := rpow_one_add_neg_le_two_pow (p := 1 + s / 2) (by positivity) hE0
    (circDist_nonneg _ _) hF
  -- Step 5: combine the factors
  have hstep2 : (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2))
      ≤ (((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2)) * (2 ^ (1 + s / 2) * (2 ^ (1 + s / 2)
          * (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2)))) := by
    refine le_trans hdist ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_trans hpow1 (mul_le_mul_of_nonneg_left hpow2 (by positivity))
  rw [div_rpow_eq_mul_rpow_neg (by linarith)]
  have hG := gradW2_nonneg s a N ℓ ((w : ℝ) + (r : ℝ))
  have hX0 : 0 ≤ (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2)) :=
    Real.rpow_nonneg (by linarith [circDist_nonneg ((N : ℕ) : ℝ) (r : ℝ)]) _
  have hK0 : 0 ≤ (((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2)) := by positivity
  calc gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X j) * (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2))
      ≤ (2 ^ (4 + a) * gradW2 s a N ℓ ((w : ℝ) + (r : ℝ)))
          * ((((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2)) * (2 ^ (1 + s / 2) * (2 ^ (1 + s / 2)
          * (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2))))) :=
        mul_le_mul hstep1 hstep2 (by positivity) (by positivity)
    _ = 2 ^ (4 + a) * 2 ^ (1 + s / 2) * 2 ^ (1 + s / 2) * (((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2))
          * (gradW2 s a N ℓ ((w : ℝ) + (r : ℝ)) * (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2))) := by
        ring

/-! ## Cell sums -/

/-- The first term summed over the window is bounded by the lattice sum over the cells.
(The count `2 + K^ε` of particles per cell comes from packing.) -/
lemma sum_first_term_le {s a γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (ha0 : 0 ≤ a) (hγ : 1 < γ) (hε : 0 < ε) (hεs : ε < (1 - s / 2) / 8)
    (hℓ : 0 < ℓ) (hK : 1 ≤ ((N : ℕ) : ℝ) * ℓ) (hN : 2 ≤ (N : ℕ)) (hX : gradEvent s γ ε N ℓ X)
    {i : ℤ} (hi : i ∈ gradLabels N ℓ γ) (w : ℤ)
    (hw : |((N : ℕ) : ℝ) * gradLift N X i - (w : ℝ)| ≤ 1) :
    ∑ j ∈ gradLabels N ℓ γ,
        gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X j) / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2)
      ≤ 2 ^ (4 + a) * 2 ^ (1 + s / 2) * 2 ^ (1 + s / 2) * (((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2))
          * (2 + (((N : ℕ) : ℝ) * ℓ) ^ ε)
          * ∑ r ∈ Finset.range (N : ℕ),
              gradW2 s a N ℓ ((w : ℝ) + (r : ℝ)) * (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2)) := by
  have hK0 : 0 < ((N : ℕ) : ℝ) * ℓ := by linarith
  have hC : 0 ≤ 2 ^ (4 + a) * 2 ^ (1 + s / 2) * 2 ^ (1 + s / 2) * (((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2)) := by
    positivity
  rw [sum_cell_fiber X w, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  have hterm : ∀ j ∈ (gradLabels N ℓ γ).filter (fun j => gradCell N w (gradLift N X j) = r),
      gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X j) / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2)
        ≤ 2 ^ (4 + a) * 2 ^ (1 + s / 2) * 2 ^ (1 + s / 2) * (((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2))
          * (gradW2 s a N ℓ ((w : ℝ) + (r : ℝ)) * (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2))) := by
    intro j hj
    obtain ⟨hjI, hjc⟩ := Finset.mem_filter.mp hj
    exact particle_first_term_le hs0 hs1 ha0 hγ hε hεs hℓ hK hX hi hjI w hw r hjc
  have hcard := card_filter_cell_le (w := w) (r := r) hs0 hγ hε hεs hK hN hX
  have hHnn : 0 ≤ gradW2 s a N ℓ ((w : ℝ) + (r : ℝ)) * (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2)) := by
    apply mul_nonneg (gradW2_nonneg s a N ℓ _)
    exact Real.rpow_nonneg (by linarith [circDist_nonneg ((N : ℕ) : ℝ) (r : ℝ)]) _
  calc ∑ j ∈ (gradLabels N ℓ γ).filter (fun j => gradCell N w (gradLift N X j) = r),
          gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X j) / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2)
        ≤ ∑ j ∈ (gradLabels N ℓ γ).filter (fun j => gradCell N w (gradLift N X j) = r),
            2 ^ (4 + a) * 2 ^ (1 + s / 2) * 2 ^ (1 + s / 2) * (((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2))
              * (gradW2 s a N ℓ ((w : ℝ) + (r : ℝ)) * (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2))) :=
        Finset.sum_le_sum hterm
    _ = ((((gradLabels N ℓ γ).filter (fun j => gradCell N w (gradLift N X j) = r)).card : ℝ))
          * (2 ^ (4 + a) * 2 ^ (1 + s / 2) * 2 ^ (1 + s / 2) * (((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2))
              * (gradW2 s a N ℓ ((w : ℝ) + (r : ℝ)) * (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 + (((N : ℕ) : ℝ) * ℓ) ^ ε) * (2 ^ (4 + a) * 2 ^ (1 + s / 2) * 2 ^ (1 + s / 2)
          * (((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2))
          * (gradW2 s a N ℓ ((w : ℝ) + (r : ℝ)) * (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2)))) := by
        apply mul_le_mul_of_nonneg_right hcard
        exact mul_nonneg hC hHnn
    _ = 2 ^ (4 + a) * 2 ^ (1 + s / 2) * 2 ^ (1 + s / 2) * (((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2))
          * (2 + (((N : ℕ) : ℝ) * ℓ) ^ ε)
          * (gradW2 s a N ℓ ((w : ℝ) + (r : ℝ)) * (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2))) := by
        ring

/-! ## The second term: residues of the path increments -/

/-- The residue of the label `j` relative to `i`: `(j - i) mod N`, as a natural number in `[0, N)`. -/
def gradRes (N : ℕ+) (i j : ℤ) : ℕ := ((j - i) % ((N : ℕ) : ℤ)).toNat

/-- A residue is less than `N`. -/
lemma gradRes_lt (N : ℕ+) (i j : ℤ) : gradRes N i j < (N : ℕ) := by
  unfold gradRes
  have hNz : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  exact (Int.toNat_lt (Int.emod_nonneg _ hNz.ne')).mpr (Int.emod_lt_of_pos _ hNz)

/-- The residue, cast to the integers, is `(j - i) mod N`. -/
lemma gradRes_cast (N : ℕ+) (i j : ℤ) : ((gradRes N i j : ℕ) : ℤ) = (j - i) % ((N : ℕ) : ℤ) := by
  have hNz : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  unfold gradRes
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ hNz.ne')

/-- The second term summed over the window is bounded by the lattice sum at `Nx_i`. -/
lemma sum_second_term_le {s a γ ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} (hℓ : 0 < ℓ)
    {i : ℤ} (hi : i ∈ gradLabels N ℓ γ) :
    ∑ j ∈ gradLabels N ℓ γ,
        gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ))
          / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2)
      ≤ ∑ r ∈ Finset.range (N : ℕ),
          gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i + (r : ℝ))
            / (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (1 + s / 2) := by
  have hNz : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  have hterm : ∀ j ∈ gradLabels N ℓ γ,
      gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ))
          / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2)
        = gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i + ((gradRes N i j : ℕ) : ℝ))
          / (1 + circDist ((N : ℕ) : ℝ) ((gradRes N i j : ℕ) : ℝ)) ^ (1 + s / 2) := by
    intro j hj
    have hlt := gradLabels_abs_sub_lt hi hj
    have hcast : ((gradRes N i j : ℕ) : ℝ) = (((j - i) % ((N : ℕ) : ℤ) : ℤ) : ℝ) := by
      have h' := gradRes_cast N i j
      exact_mod_cast h'
    rw [gradW2_path s a γ N hℓ _ i j, gradLabelDist_eq_circDist hlt, ← hcast]
    rfl
  rw [Finset.sum_congr rfl hterm]
  have hinj : Set.InjOn (gradRes N i) ↑(gradLabels N ℓ γ) := by
    intro j hj j' hj' hgj
    have hr : (j - i) % ((N : ℕ) : ℤ) = (j' - i) % ((N : ℕ) : ℤ) := by
      have h1 := gradRes_cast N i j
      have h2 := gradRes_cast N i j'
      rw [← h1, ← h2, hgj]
    exact emod_inj_of_abs_sub_lt hr (gradLabels_abs_sub_lt hj' hj)
  calc ∑ j ∈ gradLabels N ℓ γ,
          gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i + ((gradRes N i j : ℕ) : ℝ))
            / (1 + circDist ((N : ℕ) : ℝ) ((gradRes N i j : ℕ) : ℝ)) ^ (1 + s / 2)
        = ∑ r ∈ (gradLabels N ℓ γ).image (gradRes N i),
            gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i + (r : ℝ))
              / (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (1 + s / 2) :=
          (Finset.sum_image (f := fun r : ℕ => gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i + (r : ℝ))
              / (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (1 + s / 2)) hinj).symm
      _ ≤ ∑ r ∈ Finset.range (N : ℕ),
            gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i + (r : ℝ))
              / (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (1 + s / 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro r hr
          obtain ⟨j, _, hjr⟩ := Finset.mem_image.mp hr
          rw [← hjr]
          exact Finset.mem_range.mpr (gradRes_lt N i j)
        · intro r _ _
          apply div_nonneg (gradW2_nonneg s a N ℓ _)
          exact Real.rpow_nonneg (by linarith [circDist_nonneg ((N : ℕ) : ℝ) (r : ℝ)]) _

/-! ## Lattice bridges -/

/-- The lattice sum of `W_2` against the decay `(1 + circDist N r)^{-(1+s/2)}`, at any real base
point `z` (convolution part of Lemma 5.7, third bound). -/
lemma lattice_w2_sum {s a : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a) (ha : a < 1 - s / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ z : ℝ), 2 ≤ (N : ℕ) → 1 ≤ ((N : ℕ) : ℝ) * ℓ → ℓ ≤ 1 →
      ∑ r ∈ Finset.range (N : ℕ),
          gradW2 s a N ℓ (z + (r : ℝ)) * (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2))
        ≤ C * (1 + Real.log (((N : ℕ) : ℝ) * ℓ))
          * (gradW2 s a N ℓ z
            + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a) * (1 + circDist ((N : ℕ) : ℝ) z) ^ (-(1 + s / 2))) := by
  obtain ⟨C, hC, hsum⟩ := gradient_splitting_lattice_sum_three hs0 hs1 ha0 ha
  refine ⟨C, hC, fun N ℓ z hN hK1 hℓ1 => ?_⟩
  have hN0 : (0 : ℝ) ≤ ((N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hKN : ((N : ℕ) : ℝ) * ℓ ≤ ((N : ℕ) : ℝ) := by nlinarith
  have key := hsum (N : ℕ) (((N : ℕ) : ℝ) * ℓ) z hN hK1 hKN
  have e1 : ∑ r ∈ Finset.range (N : ℕ),
      gradW2 s a N ℓ (z + (r : ℝ)) * (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2))
      = ∑ r ∈ Finset.range (N : ℕ),
          gradWeightTwo s a (((N : ℕ) : ℝ) * ℓ) (((N : ℕ) : ℝ) / (((N : ℕ) : ℝ) * ℓ))
            ((z + (r : ℝ)) / (((N : ℕ) : ℝ) * ℓ))
            / (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (1 + s / 2) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [div_rpow_eq_mul_rpow_neg (by linarith [circDist_nonneg ((N : ℕ) : ℝ) (r : ℝ)])]
    rfl
  have e2 : gradW2 s a N ℓ z
      + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a) * (1 + circDist ((N : ℕ) : ℝ) z) ^ (-(1 + s / 2))
      = gradWeightTwo s a (((N : ℕ) : ℝ) * ℓ) (((N : ℕ) : ℝ) / (((N : ℕ) : ℝ) * ℓ))
          (z / (((N : ℕ) : ℝ) * ℓ))
        + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a) / (1 + circDist ((N : ℕ) : ℝ) z) ^ (1 + s / 2) := by
    rw [div_rpow_eq_mul_rpow_neg (by linarith [circDist_nonneg ((N : ℕ) : ℝ) z])]
    rfl
  rw [e1, e2]
  exact key

/-- The lattice sum of `W_1^2` (convolution part of Lemma 5.7, second bound). -/
lemma lattice_w1_sq_sum {s a : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a) (ha : a < 1 - s / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ z : ℝ), 2 ≤ (N : ℕ) → 1 ≤ ((N : ℕ) : ℝ) * ℓ → ℓ ≤ 1 →
      ∑ r ∈ Finset.range (N : ℕ), gradW1 s a N ℓ (z + (r : ℝ)) ^ 2
        ≤ C * ((((N : ℕ) : ℝ) * ℓ) + (((N : ℕ) : ℝ) * ℓ) ^ (2 * a)) * (1 + Real.log (((N : ℕ) : ℝ) * ℓ)) := by
  obtain ⟨C, hC, hsum⟩ := gradient_splitting_lattice_sum_two hs0 hs1 ha0 ha
  refine ⟨C, hC, fun N ℓ z hN hK1 hℓ1 => ?_⟩
  have hN0 : (0 : ℝ) ≤ ((N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hKN : ((N : ℕ) : ℝ) * ℓ ≤ ((N : ℕ) : ℝ) := by nlinarith
  exact hsum (N : ℕ) (((N : ℕ) : ℝ) * ℓ) z hN hK1 hKN

/-! ## The squared first-order weight -/

/-- Per-particle bound for `W_1^2`: the particle of cell `r` has `W_1(Nx_j)^2` at most
`(2^(2+a))^2 W_1(w + r)^2`. -/
lemma particle_sq_term_le {s a ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (ha0 : 0 ≤ a) (hℓ : 0 < ℓ) (hK : 1 ≤ ((N : ℕ) : ℝ) * ℓ) (w : ℤ) (j : ℤ)
    (r : ℕ) (hr : gradCell N w (gradLift N X j) = r) :
    gradW1 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X j) ^ 2
      ≤ (2 ^ (2 + a)) ^ 2 * gradW1 s a N ℓ ((w : ℝ) + (r : ℝ)) ^ 2 := by
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  obtain ⟨m, hm⟩ := gradCell_floor_eq N w (gradLift N X j)
  rw [hr] at hm
  have hqR : ((⌊((N : ℕ) : ℝ) * gradLift N X j⌋ : ℤ) : ℝ)
      = (w : ℝ) + (r : ℝ) + (m : ℝ) * ((N : ℕ) : ℝ) := by
    rw [hm]
    push_cast
    ring
  have hfl1 : ((⌊((N : ℕ) : ℝ) * gradLift N X j⌋ : ℤ) : ℝ) ≤ ((N : ℕ) : ℝ) * gradLift N X j :=
    Int.floor_le _
  have hfl2 : ((N : ℕ) : ℝ) * gradLift N X j < ((⌊((N : ℕ) : ℝ) * gradLift N X j⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hQ : |((⌊((N : ℕ) : ℝ) * gradLift N X j⌋ : ℤ) : ℝ) - ((N : ℕ) : ℝ) * gradLift N X j| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have h := gradW1_cell_sq_le s a hs0 hs1 ha0 N hK (circDist_le_add_one_of_abs_sub_le hN0 hQ)
  rw [hqR, gradW1_add_mul s a N hℓ] at h
  exact h

/-- The squared first-order weight summed over the window, bounded by the lattice sum over the
cells. -/
lemma sum_sq_term_le {s a γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (ha0 : 0 ≤ a) (hγ : 1 < γ) (hε : 0 < ε) (hεs : ε < (1 - s / 2) / 8)
    (hℓ : 0 < ℓ) (hK : 1 ≤ ((N : ℕ) : ℝ) * ℓ) (hN : 2 ≤ (N : ℕ)) (hX : gradEvent s γ ε N ℓ X)
    (w : ℤ) :
    ∑ j ∈ gradLabels N ℓ γ, gradW1 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X j) ^ 2
      ≤ (2 ^ (2 + a)) ^ 2 * (2 + (((N : ℕ) : ℝ) * ℓ) ^ ε)
          * ∑ r ∈ Finset.range (N : ℕ), gradW1 s a N ℓ ((w : ℝ) + (r : ℝ)) ^ 2 := by
  rw [sum_cell_fiber X w, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  have hterm : ∀ j ∈ (gradLabels N ℓ γ).filter (fun j => gradCell N w (gradLift N X j) = r),
      gradW1 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X j) ^ 2
        ≤ (2 ^ (2 + a)) ^ 2 * gradW1 s a N ℓ ((w : ℝ) + (r : ℝ)) ^ 2 := by
    intro j hj
    obtain ⟨_, hjc⟩ := Finset.mem_filter.mp hj
    exact particle_sq_term_le hs0 hs1 ha0 hℓ hK w j r hjc
  have hcard := card_filter_cell_le (w := w) (r := r) hs0 hγ hε hεs hK hN hX
  have hG : 0 ≤ gradW1 s a N ℓ ((w : ℝ) + (r : ℝ)) ^ 2 := sq_nonneg _
  calc ∑ j ∈ (gradLabels N ℓ γ).filter (fun j => gradCell N w (gradLift N X j) = r),
          gradW1 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X j) ^ 2
        ≤ ∑ j ∈ (gradLabels N ℓ γ).filter (fun j => gradCell N w (gradLift N X j) = r),
            (2 ^ (2 + a)) ^ 2 * gradW1 s a N ℓ ((w : ℝ) + (r : ℝ)) ^ 2 := Finset.sum_le_sum hterm
    _ = ((((gradLabels N ℓ γ).filter (fun j => gradCell N w (gradLift N X j) = r)).card : ℝ))
          * ((2 ^ (2 + a)) ^ 2 * gradW1 s a N ℓ ((w : ℝ) + (r : ℝ)) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 + (((N : ℕ) : ℝ) * ℓ) ^ ε) * ((2 ^ (2 + a)) ^ 2 * gradW1 s a N ℓ ((w : ℝ) + (r : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg (sq_nonneg _) hG)
    _ = (2 ^ (2 + a)) ^ 2 * (2 + (((N : ℕ) : ℝ) * ℓ) ^ ε) * gradW1 s a N ℓ ((w : ℝ) + (r : ℝ)) ^ 2 := by
        ring

/-! ## Main statements -/

/-- The convolution part of Lemma 5.7, the particle sums on `𝒜_{ε,γ}`, first claim:
for `i ∈ I`, `∑_{j∈I} (W_2(Nx_j) + W_2(Nx_i + k_{ij})) / (1 + d(i,j))^{1+s/2}` is at most
`C K^{κε} (1 + log K) (W_2(Nx_i) + K^{1+a} / (1 + N|x_i|)^{1+s/2})`, with `κ = 2 + s/2` depending on
`s` only, and `C` depending on `s, a, ε` only. -/
theorem gradient_splitting_particle_sum_two {s a : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a)
    (ha : a < 1 - s / 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < (1 - s / 2) / 8 →
      ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (N : ℕ+) (ℓ : ℝ) (X : Fin (N : ℕ) → ℝ) (i : ℤ),
        1 < γ → 2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ ((N : ℕ) : ℝ) * ℓ →
        gradEvent s γ ε N ℓ X → i ∈ gradLabels N ℓ γ →
        ∑ j ∈ gradLabels N ℓ γ,
            (gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X j)
              + gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ)))
              / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2)
          ≤ C * (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε) * (1 + Real.log (((N : ℕ) : ℝ) * ℓ))
            * (gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
              + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
                / (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)) := by
  obtain ⟨C₃, hC₃, hL3⟩ := lattice_w2_sum hs0 hs1 ha0 ha
  refine ⟨2 + s / 2, by positivity, fun ε hε hεs => ?_⟩
  refine ⟨3 * (2 ^ (4 + a) * 2 ^ (1 + s / 2) * 2 ^ (1 + s / 2)) * C₃ * (2 ^ (4 + a) * 2 ^ (1 + s / 2))
    + C₃, by positivity, fun γ N ℓ X i hγ hN hℓ hℓ1 hK hX hi => ?_⟩
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hK0 : 0 < ((N : ℕ) : ℝ) * ℓ := by linarith
  have hLg : 0 ≤ 1 + Real.log (((N : ℕ) : ℝ) * ℓ) := by
    have := Real.log_nonneg hK
    linarith
  have hKκ : 1 ≤ (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε) := Real.one_le_rpow hK (by positivity)
  -- the floor `w = ⌊Nx_i⌋`
  have hfl1 := Int.floor_le (((N : ℕ) : ℝ) * gradLift N X i)
  have hfl2 := Int.lt_floor_add_one (((N : ℕ) : ℝ) * gradLift N X i)
  generalize ⌊((N : ℕ) : ℝ) * gradLift N X i⌋ = w at hfl1 hfl2
  have hw : |((N : ℕ) : ℝ) * gradLift N X i - (w : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hP0 : (0 : ℝ) ≤ 1 + s / 2 := by linarith
  -- the two first-term ingredients
  have hF1 := sum_first_term_le hs0 hs1 ha0 hγ hε hεs hℓ hK hN hX hi w hw
  have hF2 := sum_second_term_le (s := s) (a := a) (γ := γ) (X := X) hℓ hi
  have e2 : ∑ r ∈ Finset.range (N : ℕ),
        gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i + (r : ℝ))
          / (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (1 + s / 2)
      = ∑ r ∈ Finset.range (N : ℕ),
          gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i + (r : ℝ))
            * (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2)) := by
    apply Finset.sum_congr rfl
    intro r _
    exact div_rpow_eq_mul_rpow_neg (by linarith [circDist_nonneg ((N : ℕ) : ℝ) (r : ℝ)])
  have hL2 := hL3 N ℓ (((N : ℕ) : ℝ) * gradLift N X i) hN hK hℓ1
  have hL1 := hL3 N ℓ (w : ℝ) hN hK hℓ1
  -- the weight and distance comparisons at `w`
  have hcw : gradW2 s a N ℓ (w : ℝ) ≤ 2 ^ (4 + a) * gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i) :=
    gradW2_cell_le s a hs0 hs1 ha0 N hK (circDist_le_add_one_of_abs_sub_le hN0 hw)
  have hcirc : |circDist ((N : ℕ) : ℝ) (w : ℝ)
      - circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)| ≤ 1 := by
    have h1 := abs_circDist_sub_circDist_le (L := ((N : ℕ) : ℝ)) (a := (w : ℝ))
      (b := ((N : ℕ) : ℝ) * gradLift N X i) hN0
    have h2 := circDist_le_abs_self hN0 ((w : ℝ) - ((N : ℕ) : ℝ) * gradLift N X i)
    have h3 : |(w : ℝ) - ((N : ℕ) : ℝ) * gradLift N X i| ≤ 1 := by
      rw [abs_sub_comm]
      exact hw
    linarith
  have hpw := rpow_one_add_neg_le_two_pow (p := 1 + s / 2) hP0 (circDist_nonneg _ _)
    (circDist_nonneg _ _) hcirc
  -- abbreviations for the two endpoint quantities
  have hWi : 0 ≤ gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i) := gradW2_nonneg _ _ _ _ _
  have hXi0 : 0 ≤ (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2)) :=
    Real.rpow_nonneg (by linarith [circDist_nonneg ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)]) _
  have hKa : 0 ≤ (((N : ℕ) : ℝ) * ℓ) ^ (1 + a) := Real.rpow_nonneg hK0.le _
  have hb1 : (1 : ℝ) ≤ 2 ^ (4 + a) := Real.one_le_rpow (by norm_num) (by linarith)
  have hb2 : (1 : ℝ) ≤ 2 ^ (1 + s / 2) := Real.one_le_rpow (by norm_num) hP0
  -- `∑_r H(r) ≤ C₃ Lg (2^(4+a) 2^P) (W_i + K^{1+a} X_i)`
  have hH : ∑ r ∈ Finset.range (N : ℕ),
        gradW2 s a N ℓ ((w : ℝ) + (r : ℝ)) * (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2))
      ≤ C₃ * (1 + Real.log (((N : ℕ) : ℝ) * ℓ)) * (2 ^ (4 + a) * 2 ^ (1 + s / 2))
          * (gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
            + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
              * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2))) := by
    have hinner : gradW2 s a N ℓ (w : ℝ) + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
          * (1 + circDist ((N : ℕ) : ℝ) (w : ℝ)) ^ (-(1 + s / 2))
        ≤ (2 ^ (4 + a) * 2 ^ (1 + s / 2)) * (gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
            + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
              * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2))) := by
      have A2 : (((N : ℕ) : ℝ) * ℓ) ^ (1 + a) * (1 + circDist ((N : ℕ) : ℝ) (w : ℝ)) ^ (-(1 + s / 2))
          ≤ (((N : ℕ) : ℝ) * ℓ) ^ (1 + a) * (2 ^ (1 + s / 2)
            * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2))) :=
        mul_le_mul_of_nonneg_left hpw hKa
      have c1 : 2 ^ (4 + a) * gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
          ≤ 2 ^ (4 + a) * 2 ^ (1 + s / 2) * gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i) := by
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb2 (by positivity : (0 : ℝ) ≤ 2 ^ (4 + a))) hWi
        linarith
      have c2 : 2 ^ (1 + s / 2) * ((((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
            * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2)))
          ≤ 2 ^ (4 + a) * 2 ^ (1 + s / 2) * ((((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
            * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2))) := by
        have hY : 0 ≤ (((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
            * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2)) :=
          mul_nonneg hKa hXi0
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb1 (by positivity : (0 : ℝ) ≤ 2 ^ (1 + s / 2))) hY
        linarith
      have hgw : gradW2 s a N ℓ (w : ℝ) ≤ 2 ^ (4 + a) * gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i) := hcw
      linarith [A2, c1, c2, hgw]
    refine le_trans hL1 ?_
    calc C₃ * (1 + Real.log (((N : ℕ) : ℝ) * ℓ)) * (gradW2 s a N ℓ (w : ℝ)
            + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a) * (1 + circDist ((N : ℕ) : ℝ) (w : ℝ)) ^ (-(1 + s / 2)))
        ≤ C₃ * (1 + Real.log (((N : ℕ) : ℝ) * ℓ)) * ((2 ^ (4 + a) * 2 ^ (1 + s / 2))
            * (gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
              + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
                * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2)))) :=
          mul_le_mul_of_nonneg_left hinner (mul_nonneg hC₃.le hLg)
      _ = C₃ * (1 + Real.log (((N : ℕ) : ℝ) * ℓ)) * (2 ^ (4 + a) * 2 ^ (1 + s / 2))
            * (gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
              + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
                * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2))) := by
          ring
  -- the first claim's first term: `K^{εP}(2 + K^ε) ≤ 3 K^{κε}`
  have hKe : (((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2)) * (2 + (((N : ℕ) : ℝ) * ℓ) ^ ε)
      ≤ 3 * (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε) := by
    have hKε1 : 1 ≤ (((N : ℕ) : ℝ) * ℓ) ^ ε := Real.one_le_rpow hK hε.le
    have hsplit : (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε)
        = (((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2)) * (((N : ℕ) : ℝ) * ℓ) ^ ε := by
      rw [← Real.rpow_add hK0]
      congr 1
      ring
    rw [hsplit]
    have hpos : 0 ≤ (((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2)) := Real.rpow_nonneg hK0.le _
    have := mul_le_mul_of_nonneg_left hKε1 hpos
    linarith
  have hW2 : 0 ≤ gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
      + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
        * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2)) :=
    add_nonneg hWi (mul_nonneg hKa hXi0)
  have hT1 : 0 ≤ C₃ * (1 + Real.log (((N : ℕ) : ℝ) * ℓ)) * (2 ^ (4 + a) * 2 ^ (1 + s / 2))
      * (gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
        + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
          * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2))) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC₃.le hLg) (by positivity)) hW2
  have hC1 : (0 : ℝ) ≤ 2 ^ (4 + a) * 2 ^ (1 + s / 2) * 2 ^ (1 + s / 2) := by positivity
  have hF1' : ∑ j ∈ gradLabels N ℓ γ,
        gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X j) / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2)
      ≤ 3 * (2 ^ (4 + a) * 2 ^ (1 + s / 2) * 2 ^ (1 + s / 2)) * C₃ * (2 ^ (4 + a) * 2 ^ (1 + s / 2))
          * (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε) * (1 + Real.log (((N : ℕ) : ℝ) * ℓ))
          * (gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
            + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
              * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2))) := by
    calc ∑ j ∈ gradLabels N ℓ γ,
          gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X j) / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2)
        ≤ 2 ^ (4 + a) * 2 ^ (1 + s / 2) * 2 ^ (1 + s / 2) * (((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2))
            * (2 + (((N : ℕ) : ℝ) * ℓ) ^ ε)
            * ∑ r ∈ Finset.range (N : ℕ),
                gradW2 s a N ℓ ((w : ℝ) + (r : ℝ)) * (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2)) :=
          hF1
      _ = (2 ^ (4 + a) * 2 ^ (1 + s / 2) * 2 ^ (1 + s / 2))
            * ((((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2)) * (2 + (((N : ℕ) : ℝ) * ℓ) ^ ε))
            * ∑ r ∈ Finset.range (N : ℕ),
                gradW2 s a N ℓ ((w : ℝ) + (r : ℝ)) * (1 + circDist ((N : ℕ) : ℝ) (r : ℝ)) ^ (-(1 + s / 2)) := by
          ring
      _ ≤ (2 ^ (4 + a) * 2 ^ (1 + s / 2) * 2 ^ (1 + s / 2))
            * ((((N : ℕ) : ℝ) * ℓ) ^ (ε * (1 + s / 2)) * (2 + (((N : ℕ) : ℝ) * ℓ) ^ ε))
            * (C₃ * (1 + Real.log (((N : ℕ) : ℝ) * ℓ)) * (2 ^ (4 + a) * 2 ^ (1 + s / 2))
              * (gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
                + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
                  * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2)))) :=
          mul_le_mul_of_nonneg_left hH (by positivity)
      _ ≤ (2 ^ (4 + a) * 2 ^ (1 + s / 2) * 2 ^ (1 + s / 2)) * (3 * (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε))
            * (C₃ * (1 + Real.log (((N : ℕ) : ℝ) * ℓ)) * (2 ^ (4 + a) * 2 ^ (1 + s / 2))
              * (gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
                + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
                  * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2)))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKe hC1) hT1
      _ = 3 * (2 ^ (4 + a) * 2 ^ (1 + s / 2) * 2 ^ (1 + s / 2)) * C₃ * (2 ^ (4 + a) * 2 ^ (1 + s / 2))
            * (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε) * (1 + Real.log (((N : ℕ) : ℝ) * ℓ))
            * (gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
              + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
                * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2))) := by
          ring
  have hF2' : ∑ j ∈ gradLabels N ℓ γ,
        gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ))
          / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2)
      ≤ C₃ * (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε) * (1 + Real.log (((N : ℕ) : ℝ) * ℓ))
          * (gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
            + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
              * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2))) := by
    have hnn : 0 ≤ C₃ * (1 + Real.log (((N : ℕ) : ℝ) * ℓ))
        * (gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
          + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
            * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2))) :=
      mul_nonneg (mul_nonneg hC₃.le hLg) hW2
    calc _ ≤ _ := hF2
      _ = _ := e2
      _ ≤ _ := hL2
      _ ≤ C₃ * (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε) * (1 + Real.log (((N : ℕ) : ℝ) * ℓ))
          * (gradW2 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
            + (((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
              * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2))) := by
          linarith [mul_nonneg (sub_nonneg.mpr hKκ) hnn]
  simp only [add_div]
  rw [Finset.sum_add_distrib]
  rw [← circDist_mul_self_scale hN0 (gradLift N X i)]
  have hdiv : (((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
      / (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (1 + s / 2)
      = (((N : ℕ) : ℝ) * ℓ) ^ (1 + a)
        * (1 + circDist ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)) ^ (-(1 + s / 2)) :=
    div_rpow_eq_mul_rpow_neg (by linarith [circDist_nonneg ((N : ℕ) : ℝ) (((N : ℕ) : ℝ) * gradLift N X i)])
  rw [hdiv]
  refine le_trans (add_le_add hF1' hF2') (le_of_eq ?_)
  ring

/-- The convolution part of Lemma 5.7, the particle sums on `𝒜_{ε,γ}`, second claim:
`∑_{j∈I} W_1(Nx_j)^2 ≤ C K^{κε} (K + K^{2a}) (1 + log K)`, with `κ = 1`. -/
theorem gradient_splitting_particle_sum_sq {s a : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a)
    (ha : a < 1 - s / 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < (1 - s / 2) / 8 →
      ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (N : ℕ+) (ℓ : ℝ) (X : Fin (N : ℕ) → ℝ),
        1 < γ → 2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ ((N : ℕ) : ℝ) * ℓ →
        gradEvent s γ ε N ℓ X →
        ∑ j ∈ gradLabels N ℓ γ, gradW1 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X j) ^ 2
          ≤ C * (((N : ℕ) : ℝ) * ℓ) ^ (κ * ε)
            * ((((N : ℕ) : ℝ) * ℓ) + (((N : ℕ) : ℝ) * ℓ) ^ (2 * a))
            * (1 + Real.log (((N : ℕ) : ℝ) * ℓ)) := by
  obtain ⟨C₂, hC₂, hL⟩ := lattice_w1_sq_sum hs0 hs1 ha0 ha
  refine ⟨1, one_pos, fun ε hε hεs => ?_⟩
  refine ⟨3 * (2 ^ (2 + a)) ^ 2 * C₂, by positivity, fun γ N ℓ X hγ hN hℓ hℓ1 hK hX => ?_⟩
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hK0 : 0 < ((N : ℕ) : ℝ) * ℓ := by linarith
  have hS := sum_sq_term_le hs0 hs1 ha0 hγ hε hεs hℓ hK hN hX 0
  have hL0 := hL N ℓ 0 hN hK hℓ1
  simp only [Int.cast_zero, zero_add] at hS hL0
  rw [one_mul]
  have hKε1 : 1 ≤ (((N : ℕ) : ℝ) * ℓ) ^ ε := Real.one_le_rpow hK hε.le
  have h2 : 2 + (((N : ℕ) : ℝ) * ℓ) ^ ε ≤ 3 * (((N : ℕ) : ℝ) * ℓ) ^ ε := by linarith
  have hLg : 0 ≤ 1 + Real.log (((N : ℕ) : ℝ) * ℓ) := by
    have := Real.log_nonneg hK
    linarith
  have hLnn : 0 ≤ C₂ * ((((N : ℕ) : ℝ) * ℓ) + (((N : ℕ) : ℝ) * ℓ) ^ (2 * a))
      * (1 + Real.log (((N : ℕ) : ℝ) * ℓ)) := by
    apply mul_nonneg (mul_nonneg hC₂.le _) hLg
    have : 0 ≤ (((N : ℕ) : ℝ) * ℓ) ^ (2 * a) := Real.rpow_nonneg hK0.le _
    linarith
  calc ∑ j ∈ gradLabels N ℓ γ, gradW1 s a N ℓ (((N : ℕ) : ℝ) * gradLift N X j) ^ 2
      ≤ (2 ^ (2 + a)) ^ 2 * (2 + (((N : ℕ) : ℝ) * ℓ) ^ ε)
          * ∑ r ∈ Finset.range (N : ℕ), gradW1 s a N ℓ (r : ℝ) ^ 2 := hS
    _ ≤ (2 ^ (2 + a)) ^ 2 * (2 + (((N : ℕ) : ℝ) * ℓ) ^ ε)
          * (C₂ * ((((N : ℕ) : ℝ) * ℓ) + (((N : ℕ) : ℝ) * ℓ) ^ (2 * a))
            * (1 + Real.log (((N : ℕ) : ℝ) * ℓ))) :=
        mul_le_mul_of_nonneg_left hL0 (by positivity)
    _ ≤ (2 ^ (2 + a)) ^ 2 * (3 * (((N : ℕ) : ℝ) * ℓ) ^ ε)
          * (C₂ * ((((N : ℕ) : ℝ) * ℓ) + (((N : ℕ) : ℝ) * ℓ) ^ (2 * a))
            * (1 + Real.log (((N : ℕ) : ℝ) * ℓ))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) hLnn
    _ = 3 * (2 ^ (2 + a)) ^ 2 * C₂ * (((N : ℕ) : ℝ) * ℓ) ^ ε
          * ((((N : ℕ) : ℝ) * ℓ) + (((N : ℕ) : ℝ) * ℓ) ^ (2 * a))
          * (1 + Real.log (((N : ℕ) : ℝ) * ℓ)) := by
        ring

end

end Riesz1
