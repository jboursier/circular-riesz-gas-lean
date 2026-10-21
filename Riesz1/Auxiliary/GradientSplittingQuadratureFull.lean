/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingQuadratureCells
public import Riesz1.Auxiliary.GradientSplittingQuadratureLabels
public import Riesz1.Auxiliary.GradientSplittingQuadratureWeights
public import Riesz1.Auxiliary.GradientSplittingQuadratureReduce

/-!
# The full-window bound of the reference field

The quadrature part of Lemma 5.7, full window. For a full
window `¬GradPartial` the reference field `V^{(2)}_i = gradVdisc2 + gradVbg` decomposes (by
`gradV2_eq_split`) into a kernel term `ψ'(x/ℓ) · ∑_j h'(k_{ij}/N)` and a remainder
`∑_j R_x(k_{ij}) - ∫_{-N/2}^{N/2} R_x`. This module proves the two estimates of the decomposition:

* the odd cancellation of `∑_j h'(k_{ij}/N)`, which leaves at most the antipodal term.
* the remainder bound, from the cell bounds of `GradientSplittingQuadratureCells`.
-/

@[expose] public section

open Set MeasureTheory Finset
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The kernel derivative sum `∑_{j ≠ i} h'(k_{ij}/N)` of a full window is at most the antipodal
value `|h'(1/2)|`: the odd part cancels on the signed set `gradFullDiscs N`, and the single
antipodal term remains for even `N` (quadrature part of Lemma 5.7, full window). -/
theorem full_odd_sum_bound {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+} {ℓ γ : ℝ}
    (hP : ¬GradPartial N ℓ γ) {i : ℤ} (hi : i ∈ gradLabels N ℓ γ) :
    |∑ j ∈ (gradLabels N ℓ γ).erase i,
        deriv (gradKernelH s) (((gradPathIncr N ℓ γ i j : ℤ) : ℝ) / ((N : ℕ) : ℝ))|
      ≤ |deriv (gradKernelH s) (1 / 2)| := by
  have hNR : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hodd : ∀ k ∈ gradFullDiscs N,
      deriv (gradKernelH s) (((-k : ℤ) : ℝ) / ((N : ℕ) : ℝ))
        = -deriv (gradKernelH s) ((k : ℝ) / ((N : ℕ) : ℝ)) := by
    intro k hk
    obtain ⟨hk0, hk2⟩ := mem_gradFullDiscs.mp hk
    have hkabs : 0 < |(k : ℝ)| := by
      have : (0 : ℝ) < |(k : ℝ)| := by
        rw [abs_pos]
        exact_mod_cast hk0
      exact this
    have hk2R : 2 * |(k : ℝ)| < ((N : ℕ) : ℝ) := by
      have h : ((2 * |k| : ℤ) : ℝ) < (((N : ℕ) : ℤ) : ℝ) := by exact_mod_cast hk2
      push_cast at h
      linarith
    have hne : ((((k : ℝ)) / ((N : ℕ) : ℝ) : ℝ) : UnitAddCircle) ≠ 0 := by
      apply gradSplit_coe_ne_zero
      · rw [abs_div, abs_of_pos hNR]
        exact div_pos hkabs hNR
      · rw [abs_div, abs_of_pos hNR, div_lt_one hNR]
        linarith
    rw [show (((-k : ℤ) : ℝ)) / ((N : ℕ) : ℝ) = -(((k : ℝ)) / ((N : ℕ) : ℝ)) by push_cast; ring,
      ← iteratedDeriv_one]
    rw [gradSplit_iteratedDeriv_one_gradKernelH_neg s hs0 hs1 hne, iteratedDeriv_one]
  rw [sum_labels_erase_full hP hi (fun k : ℤ => deriv (gradKernelH s) ((k : ℝ) / ((N : ℕ) : ℝ)))]
  rw [sum_gradFullDiscs_eq_zero (fun k : ℤ => deriv (gradKernelH s) ((k : ℝ) / ((N : ℕ) : ℝ))) hodd,
    zero_add]
  split_ifs with heven
  · rcases gradPathIncr_anti_eq hP heven with h | h
    · rw [h]
      have h2 : (2 : ℝ) * (((((N : ℕ) : ℤ) / 2 : ℤ)) : ℝ) = ((N : ℕ) : ℝ) := by
        have : (2 : ℤ) * (((N : ℕ) : ℤ) / 2) = ((N : ℕ) : ℤ) := by omega
        exact_mod_cast this
      rw [show ((((N : ℕ) : ℤ) / 2 : ℤ) : ℝ) / ((N : ℕ) : ℝ) = 1 / 2 by
        field_simp
        linarith]
    · rw [h, show ((-((((N : ℕ) : ℤ)) / 2) : ℤ) : ℝ) / ((N : ℕ) : ℝ) = -(1 / 2) by
        have h2 : (2 : ℝ) * (((((N : ℕ) : ℤ) / 2 : ℤ)) : ℝ) = ((N : ℕ) : ℝ) := by
          have : (2 : ℤ) * (((N : ℕ) : ℤ) / 2) = ((N : ℕ) : ℤ) := by omega
          exact_mod_cast this
        push_cast
        field_simp
        linarith]
      rw [← iteratedDeriv_one, gradSplit_iteratedDeriv_one_gradKernelH_neg s hs0 hs1
        (gradSplit_coe_ne_zero (by norm_num) (by norm_num)), iteratedDeriv_one, abs_neg]
  · simp

/-- The cell weight at the two antipodal increments `±m`, `m = N/2`, is the same: the weight `w_2`
is periodic with period `ℓ^{-1}`, and the two points `(x ± m/N)/ℓ` differ by `ℓ^{-1}`. -/
lemma gradQuadCell_neg_antipode (s a : ℝ) {N : ℕ} {ℓ C₁ C0 x : ℝ} (hN : 2 ≤ N) (hℓ : 0 < ℓ)
    {m : ℤ} (hm : (m : ℝ) = (N : ℝ) / 2) :
    gradQuadCell s a N ℓ C₁ C0 x (-m) = gradQuadCell s a N ℓ C₁ C0 x m := by
  have hNR : (N : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    intro h
    linarith
  have hkey : (x + ((-m : ℤ) : ℝ) / N) / ℓ
      = (x + (m : ℝ) / N) / ℓ + ((-1 : ℤ) : ℝ) * ℓ⁻¹ := by
    rw [Int.cast_neg, hm]
    push_cast
    field_simp
    ring
  have hw : gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + (m : ℝ) / N) / ℓ + ((-1 : ℤ) : ℝ) * ℓ⁻¹)
      = gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + (m : ℝ) / N) / ℓ) :=
    gradWeightTwo_congr (circDist_add_int_mul (inv_pos.mpr hℓ) _ (-1))
  unfold gradQuadCell
  rw [Int.cast_neg, abs_neg, ← Int.cast_neg, hkey, hw]

/-- The unit cell of an antipode `c = ±N/2` lies in `gradCellSet N`. -/
lemma mem_gradCellSet_of_antipode_cell {N : ℕ} (hN : 2 ≤ N) {c : ℝ}
    (hc : c = (N : ℝ) / 2 ∨ c = -((N : ℝ) / 2)) {v : ℝ} (hv : v ∈ uIcc (c - 1 / 2) (c + 1 / 2)) :
    v ∈ gradCellSet N := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hle : c - 1 / 2 ≤ c + 1 / 2 := by linarith
  rw [uIcc_of_le hle, Set.mem_Icc] at hv
  apply mem_gradCellSet_of_le hN
  · rcases hc with rfl | rfl
    · rw [abs_of_pos (by linarith [hv.1])]
      linarith [hv.1]
    · rw [abs_of_neg (by linarith [hv.2])]
      linarith [hv.2]
  · rcases hc with rfl | rfl
    · rw [abs_of_pos (by linarith [hv.1])]
      linarith [hv.2]
    · rw [abs_of_neg (by linarith [hv.2])]
      linarith [hv.1]

/-- The antipodal term of the remainder: at `σ = ±N/2`, the value `R_x(σ)` differs from the two
half cells at the ends by `N^{-s} |ψ'(x/ℓ)| |h'(1/2)|` plus the weight of the cell at `N/2`. -/
lemma full_antipode_remainder_bound {s α : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {N : ℕ} {ℓ C₁ C0 x : ℝ} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hper : Function.Periodic ψ ℓ⁻¹) (hN : 2 ≤ N) (heven : N % 2 = 0) (hℓ : 0 < ℓ)
    (hD : ∀ k : ℤ, 1 ≤ |(k : ℝ)| → |(k : ℝ)| ≤ (N : ℝ) / 2 →
      ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), |deriv (gradCellR s N ℓ ψ x) v|
        ≤ gradQuadCell s (1 - s + α) N ℓ C₁ C0 x k)
    {σ : ℤ} (hσ : σ = (N : ℤ) / 2 ∨ σ = -((N : ℤ) / 2)) :
    |gradCellR s N ℓ ψ x (σ : ℝ)
        - ((∫ v in (-((N : ℝ) / 2))..(-((N : ℝ) / 2) + 1 / 2), gradCellR s N ℓ ψ x v)
          + (∫ v in ((N : ℝ) / 2 - 1 / 2)..((N : ℝ) / 2), gradCellR s N ℓ ψ x v))|
      ≤ (N : ℝ) ^ (-s) * |deriv ψ (x / ℓ)| * |iteratedDeriv 1 (gradKernelH s) (1 / 2)|
        + gradQuadCell s (1 - s + α) N ℓ C₁ C0 x ((N : ℤ) / 2) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h2m : (2 : ℤ) * ((N : ℤ) / 2) = (N : ℤ) := by omega
  have hmR : (((N : ℤ) / 2 : ℤ) : ℝ) = (N : ℝ) / 2 := by
    have h : (2 : ℝ) * (((N : ℤ) / 2 : ℤ) : ℝ) = (N : ℝ) := by exact_mod_cast h2m
    linarith
  have hm1 : (1 : ℤ) ≤ (N : ℤ) / 2 := by omega
  have hmabs : |(((N : ℤ) / 2 : ℤ) : ℝ)| = (N : ℝ) / 2 := by
    rw [hmR, abs_of_pos (by linarith)]
  -- the antipode of the remainder, at `σ = ±N/2`
  have hσR : (σ : ℝ) = (N : ℝ) / 2 ∨ (σ : ℝ) = -((N : ℝ) / 2) := by
    rcases hσ with h | h
    · left
      rw [h, hmR]
    · right
      rw [h, Int.cast_neg, hmR]
  have hA := gradCellR_antipode_avg hs0 hs1 hψ hℓ hper hN x hσR
  -- the two half cells at the ends
  have hcellP : ∀ v ∈ uIcc ((N : ℝ) / 2 - 1 / 2) ((N : ℝ) / 2 + 1 / 2),
      v ∈ gradCellSet N := fun v hv =>
    mem_gradCellSet_of_antipode_cell hN (c := (N : ℝ) / 2) (Or.inl rfl) hv
  have hcellM : ∀ v ∈ uIcc (-((N : ℝ) / 2) - 1 / 2) (-((N : ℝ) / 2) + 1 / 2),
      v ∈ gradCellSet N := fun v hv =>
    mem_gradCellSet_of_antipode_cell hN (c := -((N : ℝ) / 2)) (Or.inr rfl) hv
  have hHp := (gradCellR_half_cell_avg hs0 hs1 hψ hℓ x hcellP).1
  have hHm := (gradCellR_half_cell_avg hs0 hs1 hψ hℓ x hcellM).2
  -- the cell weights at `±N/2`
  have hIp := hD ((N : ℤ) / 2) (by exact_mod_cast hm1) (by rw [hmabs])
  have hIp' : ∫ v in ((N : ℝ) / 2 - 1 / 2)..((N : ℝ) / 2 + 1 / 2),
      |deriv (gradCellR s N ℓ ψ x) v| ≤ gradQuadCell s (1 - s + α) N ℓ C₁ C0 x ((N : ℤ) / 2) := by
    rw [← hmR]
    exact hIp
  have hIm := hD (-((N : ℤ) / 2)) (by rw [Int.cast_neg, abs_neg]; exact_mod_cast hm1)
    (by rw [Int.cast_neg, abs_neg, hmabs])
  have hgM : ∫ v in (-((N : ℝ) / 2) - 1 / 2)..(-((N : ℝ) / 2) + 1 / 2),
      |deriv (gradCellR s N ℓ ψ x) v| ≤ gradQuadCell s (1 - s + α) N ℓ C₁ C0 x ((N : ℤ) / 2) := by
    have hcast : (((-((N : ℤ) / 2)) : ℤ) : ℝ) = -((N : ℝ) / 2) := by
      rw [Int.cast_neg, hmR]
    rw [hcast] at hIm
    rw [gradQuadCell_neg_antipode s (1 - s + α) hN hℓ hmR] at hIm
    exact hIm
  -- combine the three pieces
  set Hm := ∫ v in (-((N : ℝ) / 2))..(-((N : ℝ) / 2) + 1 / 2), gradCellR s N ℓ ψ x v with hHmdef
  set Hp := ∫ v in ((N : ℝ) / 2 - 1 / 2)..((N : ℝ) / 2), gradCellR s N ℓ ψ x v with hHpdef
  set Rm := gradCellR s N ℓ ψ x (-((N : ℝ) / 2)) with hRmdef
  set Rp := gradCellR s N ℓ ψ x ((N : ℝ) / 2) with hRpdef
  set Xv := gradCellR s N ℓ ψ x (σ : ℝ) - (Rp + Rm) / 2 with hXv
  set G := gradQuadCell s (1 - s + α) N ℓ C₁ C0 x ((N : ℤ) / 2) with hGdef
  have hgp : |Hp - Rp / 2| ≤ (1 / 2) * G := by
    have h := hHp
    linarith [hIp']
  have hgm : |Hm - Rm / 2| ≤ (1 / 2) * G := by
    have h := hHm
    linarith [hgM]
  have key : gradCellR s N ℓ ψ x (σ : ℝ) - (Hm + Hp) = Xv - (Hm - Rm / 2) - (Hp - Rp / 2) := by
    rw [hXv]
    ring
  have h3 : ∀ X Y Z : ℝ, |X - Y - Z| ≤ |X| + |Y| + |Z| := by
    intro X Y Z
    have e : X - Y - Z = X + (-Y) + (-Z) := by ring
    rw [e]
    calc |X + -Y + -Z| ≤ |X + -Y| + |-Z| := abs_add_le _ _
      _ ≤ |X| + |-Y| + |-Z| := add_le_add (abs_add_le X (-Y)) le_rfl
      _ = |X| + |Y| + |Z| := by rw [abs_neg, abs_neg]
  have hXb : |Xv| = (N : ℝ) ^ (-s) * |deriv ψ (x / ℓ)| * |iteratedDeriv 1 (gradKernelH s) (1 / 2)| :=
    hA
  rw [key]
  calc |Xv - (Hm - Rm / 2) - (Hp - Rp / 2)| ≤ |Xv| + |Hm - Rm / 2| + |Hp - Rp / 2| := h3 _ _ _
    _ ≤ (N : ℝ) ^ (-s) * |deriv ψ (x / ℓ)| * |iteratedDeriv 1 (gradKernelH s) (1 / 2)|
        + G := by
      rw [hXb]
      linarith [hgm, hgp]

/-- The remainder of the full-window reference field: the sum of `R_x` over the increments
`k_{ij}` minus its integral over `[-N/2, N/2]`, bounded by the cell weights of the increments, the
central cell, and (for even `N`) the antipodal term (quadrature part of Lemma 5.7,
full window). -/
theorem full_remainder_bound {s α : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hα0 : s - 1 ≤ α)
    (hα1 : α < s / 2) {N : ℕ+} {ℓ γ C₁ C0 x Kc : ℝ} {ψ : ℝ → ℝ} {i : ℤ}
    (hψ : ContDiff ℝ ∞ ψ) (hper : Function.Periodic ψ ℓ⁻¹) (hN : 2 ≤ (N : ℕ))
    (hP : ¬GradPartial N ℓ γ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hK : 1 ≤ (N : ℝ) * ℓ) (hC0 : 0 ≤ C0)
    (h1 : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℕ) * ℓ) ℓ⁻¹ t)
    (h2 : ∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℕ) * ℓ) ℓ⁻¹ t)
    (hi : i ∈ gradLabels N ℓ γ)
    (hD : ∀ k : ℤ, 1 ≤ |(k : ℝ)| → |(k : ℝ)| ≤ ((N : ℕ) : ℝ) / 2 →
      ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), |deriv (gradCellR s (N : ℕ) ℓ ψ x) v|
        ≤ gradQuadCell s (1 - s + α) (N : ℕ) ℓ C₁ C0 x k)
    (hcen : |∫ v in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), gradCellR s (N : ℕ) ℓ ψ x v| ≤ Kc) :
    |(∑ j ∈ (gradLabels N ℓ γ).erase i, gradCellR s (N : ℕ) ℓ ψ x ((gradPathIncr N ℓ γ i j : ℤ) : ℝ))
        - ∫ v in (-(((N : ℕ) : ℝ) / 2))..(((N : ℕ) : ℝ) / 2), gradCellR s (N : ℕ) ℓ ψ x v|
      ≤ ∑ j ∈ (gradLabels N ℓ γ).erase i, gradQuadCell s (1 - s + α) (N : ℕ) ℓ C₁ C0 x
          (gradPathIncr N ℓ γ i j)
        + Kc + (if (N : ℕ) % 2 = 0 then
          ((N : ℕ) : ℝ) ^ (-s) * |deriv ψ (x / ℓ)| * |iteratedDeriv 1 (gradKernelH s) (1 / 2)|
          else 0) := by
  have hNR : (2 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hN
  have hint := intervalIntegrable_gradCellR_half (x := x) hs0 hs1 hα0 hα1 hN hℓ hℓ1 hK hC0 hψ hper h1 h2
  have hm : ((N : ℕ) : ℤ) = 2 * ((((N : ℕ) : ℤ) - 1) / 2) + 1
      ∨ ((N : ℕ) : ℤ) = 2 * ((((N : ℕ) : ℤ) - 1) / 2) + 2 := by omega
  have hsplit := integral_gradCellR_split s hN ℓ ψ x ((((N : ℕ) : ℤ) - 1) / 2) hm hint
  have hm0 : 0 ≤ (((N : ℕ) : ℤ) - 1) / 2 := by omega
  have hIco : Finset.Ico (-((((N : ℕ) : ℤ) - 1) / 2)) ((((N : ℕ) : ℤ) - 1) / 2 + 1)
      = Finset.Icc (-((((N : ℕ) : ℤ) - 1) / 2)) ((((N : ℕ) : ℤ) - 1) / 2) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hmem0 : (0 : ℤ) ∈ Finset.Icc (-((((N : ℕ) : ℤ) - 1) / 2)) ((((N : ℕ) : ℤ) - 1) / 2) :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hsumIcc : ∑ k ∈ Finset.Icc (-((((N : ℕ) : ℤ) - 1) / 2)) ((((N : ℕ) : ℤ) - 1) / 2),
      (∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), gradCellR s (N : ℕ) ℓ ψ x v)
      = (∫ v in (((0 : ℤ) : ℝ) - 1 / 2)..(((0 : ℤ) : ℝ) + 1 / 2), gradCellR s (N : ℕ) ℓ ψ x v)
        + ∑ k ∈ gradFullDiscs N, (∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2),
            gradCellR s (N : ℕ) ℓ ψ x v) := by
    unfold gradFullDiscs
    exact (Finset.add_sum_erase _ _ hmem0).symm
  have hsumR := sum_labels_erase_full hP hi (fun k : ℤ => gradCellR s (N : ℕ) ℓ ψ x (k : ℝ))
  have hsumG := sum_labels_erase_full hP hi
    (fun k : ℤ => gradQuadCell s (1 - s + α) (N : ℕ) ℓ C₁ C0 x k)
  rw [hIco] at hsplit
  -- the identity: the discrete sum minus the integral, cell by cell
  have hE : (∑ j ∈ (gradLabels N ℓ γ).erase i,
        gradCellR s (N : ℕ) ℓ ψ x ((gradPathIncr N ℓ γ i j : ℤ) : ℝ))
      - ∫ v in (-(((N : ℕ) : ℝ) / 2))..(((N : ℕ) : ℝ) / 2), gradCellR s (N : ℕ) ℓ ψ x v
      = (∑ k ∈ gradFullDiscs N, (gradCellR s (N : ℕ) ℓ ψ x (k : ℝ)
            - ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), gradCellR s (N : ℕ) ℓ ψ x v))
        - (∫ v in (((0 : ℤ) : ℝ) - 1 / 2)..(((0 : ℤ) : ℝ) + 1 / 2), gradCellR s (N : ℕ) ℓ ψ x v)
        + (if (N : ℕ) % 2 = 0 then
            gradCellR s (N : ℕ) ℓ ψ x (gradPathIncr N ℓ γ i (gradAntiLabel N i) : ℤ)
              - ((∫ v in (-(((N : ℕ) : ℝ) / 2))..(-(((N : ℕ) : ℝ) / 2) + 1 / 2),
                    gradCellR s (N : ℕ) ℓ ψ x v)
                + (∫ v in ((((N : ℕ) : ℝ) / 2) - 1 / 2)..(((N : ℕ) : ℝ) / 2),
                    gradCellR s (N : ℕ) ℓ ψ x v))
          else 0) := by
    rw [hsumR, hsplit, hsumIcc, Finset.sum_sub_distrib]
    split_ifs <;> ring
  -- the signed sum of the cell differences
  have hDbound : |∑ k ∈ gradFullDiscs N, (gradCellR s (N : ℕ) ℓ ψ x (k : ℝ)
        - ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), gradCellR s (N : ℕ) ℓ ψ x v)|
      ≤ ∑ k ∈ gradFullDiscs N, gradQuadCell s (1 - s + α) (N : ℕ) ℓ C₁ C0 x k := by
    obtain ⟨_, _, hcells⟩ := gradient_splitting_cells hs0 hs1 hα0 hα1
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k hk => ?_))
    obtain ⟨hk0, hk2⟩ := mem_gradFullDiscs.mp hk
    have hk1 : (1 : ℤ) ≤ |k| := by
      have := abs_pos.mpr hk0
      omega
    have hk1R : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast hk1
    have hkN : |(k : ℝ)| ≤ ((N : ℕ) : ℝ) / 2 := by
      have h : ((2 * |k| : ℤ) : ℝ) < (((N : ℕ) : ℤ) : ℝ) := by exact_mod_cast hk2
      push_cast at h
      linarith
    have hc6 := (hcells (N : ℕ) ℓ C0 x ψ hN hℓ hℓ1 hK hC0 hψ hper h1 h2).2.2.2.2.2 k
      (by linarith) hkN
    exact hc6.trans (hD k hk1R hkN)
  -- the central cell
  have hcell0 : |∫ v in (((0 : ℤ) : ℝ) - 1 / 2)..(((0 : ℤ) : ℝ) + 1 / 2),
      gradCellR s (N : ℕ) ℓ ψ x v| ≤ Kc := by
    simpa using hcen
  -- the sum of three terms
  have htri3 : ∀ X Y Z : ℝ, |X - Y + Z| ≤ |X| + |Y| + |Z| := by
    intro X Y Z
    rw [sub_eq_add_neg]
    calc |X + -Y + Z| ≤ |X + -Y| + |Z| := abs_add_le _ _
      _ ≤ |X| + |-Y| + |Z| := add_le_add (abs_add_le X (-Y)) le_rfl
      _ = |X| + |Y| + |Z| := by rw [abs_neg]
  by_cases heven : (N : ℕ) % 2 = 0
  · -- even `N`: the antipodal term and its symmetric weight
    have hmR : ((((N : ℕ) : ℤ) / 2 : ℤ) : ℝ) = ((N : ℕ) : ℝ) / 2 := by
      have h2m : (2 : ℤ) * (((N : ℕ) : ℤ) / 2) = ((N : ℕ) : ℤ) := by omega
      have h : (2 : ℝ) * ((((N : ℕ) : ℤ) / 2 : ℤ) : ℝ) = ((N : ℕ) : ℝ) := by
        exact_mod_cast h2m
      linarith
    have hσ : gradPathIncr N ℓ γ i (gradAntiLabel N i) = ((N : ℕ) : ℤ) / 2
        ∨ gradPathIncr N ℓ γ i (gradAntiLabel N i) = -(((N : ℕ) : ℤ) / 2) :=
      gradPathIncr_anti_eq hP heven
    have hAnt := full_antipode_remainder_bound hs0 hs1 hψ hper hN heven hℓ hD hσ
    have hgσ : gradQuadCell s (1 - s + α) (N : ℕ) ℓ C₁ C0 x
        (gradPathIncr N ℓ γ i (gradAntiLabel N i))
        = gradQuadCell s (1 - s + α) (N : ℕ) ℓ C₁ C0 x (((N : ℕ) : ℤ) / 2) := by
      rcases hσ with h | h
      · rw [h]
      · rw [h]
        exact gradQuadCell_neg_antipode s (1 - s + α) hN hℓ hmR
    rw [hE]
    simp only [heven, ↓reduceIte]
    rw [hsumG]
    simp only [heven, ↓reduceIte]
    rw [hgσ]
    calc |∑ k ∈ gradFullDiscs N, (gradCellR s (N : ℕ) ℓ ψ x (k : ℝ)
            - ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), gradCellR s (N : ℕ) ℓ ψ x v)
          - (∫ v in (((0 : ℤ) : ℝ) - 1 / 2)..(((0 : ℤ) : ℝ) + 1 / 2),
              gradCellR s (N : ℕ) ℓ ψ x v)
          + (gradCellR s (N : ℕ) ℓ ψ x (gradPathIncr N ℓ γ i (gradAntiLabel N i) : ℤ)
              - ((∫ v in (-(((N : ℕ) : ℝ) / 2))..(-(((N : ℕ) : ℝ) / 2) + 1 / 2),
                    gradCellR s (N : ℕ) ℓ ψ x v)
                + (∫ v in ((((N : ℕ) : ℝ) / 2) - 1 / 2)..(((N : ℕ) : ℝ) / 2),
                    gradCellR s (N : ℕ) ℓ ψ x v)))|
        ≤ |∑ k ∈ gradFullDiscs N, (gradCellR s (N : ℕ) ℓ ψ x (k : ℝ)
            - ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), gradCellR s (N : ℕ) ℓ ψ x v)|
          + |(∫ v in (((0 : ℤ) : ℝ) - 1 / 2)..(((0 : ℤ) : ℝ) + 1 / 2),
              gradCellR s (N : ℕ) ℓ ψ x v)|
          + |(gradCellR s (N : ℕ) ℓ ψ x (gradPathIncr N ℓ γ i (gradAntiLabel N i) : ℤ)
              - ((∫ v in (-(((N : ℕ) : ℝ) / 2))..(-(((N : ℕ) : ℝ) / 2) + 1 / 2),
                    gradCellR s (N : ℕ) ℓ ψ x v)
                + (∫ v in ((((N : ℕ) : ℝ) / 2) - 1 / 2)..(((N : ℕ) : ℝ) / 2),
                    gradCellR s (N : ℕ) ℓ ψ x v)))| := htri3 _ _ _
      _ ≤ (∑ k ∈ gradFullDiscs N, gradQuadCell s (1 - s + α) (N : ℕ) ℓ C₁ C0 x k) + Kc
          + (((N : ℕ) : ℝ) ^ (-s) * |deriv ψ (x / ℓ)| * |iteratedDeriv 1 (gradKernelH s) (1 / 2)|
            + gradQuadCell s (1 - s + α) (N : ℕ) ℓ C₁ C0 x (((N : ℕ) : ℤ) / 2)) := by
        have := hAnt
        linarith [hDbound, hcell0]
      _ = (∑ k ∈ gradFullDiscs N, gradQuadCell s (1 - s + α) (N : ℕ) ℓ C₁ C0 x k
            + gradQuadCell s (1 - s + α) (N : ℕ) ℓ C₁ C0 x (((N : ℕ) : ℤ) / 2)) + Kc
          + ((N : ℕ) : ℝ) ^ (-s) * |deriv ψ (x / ℓ)| * |iteratedDeriv 1 (gradKernelH s) (1 / 2)| := by
        ring
  · -- odd `N`: no antipodal term
    rw [hE]
    simp only [heven, ↓reduceIte, add_zero]
    rw [hsumG]
    simp only [heven, ↓reduceIte, add_zero]
    calc |∑ k ∈ gradFullDiscs N, (gradCellR s (N : ℕ) ℓ ψ x (k : ℝ)
            - ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), gradCellR s (N : ℕ) ℓ ψ x v)
          - (∫ v in (((0 : ℤ) : ℝ) - 1 / 2)..(((0 : ℤ) : ℝ) + 1 / 2),
              gradCellR s (N : ℕ) ℓ ψ x v)|
        ≤ |∑ k ∈ gradFullDiscs N, (gradCellR s (N : ℕ) ℓ ψ x (k : ℝ)
            - ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), gradCellR s (N : ℕ) ℓ ψ x v)|
          + |(∫ v in (((0 : ℤ) : ℝ) - 1 / 2)..(((0 : ℤ) : ℝ) + 1 / 2),
              gradCellR s (N : ℕ) ℓ ψ x v)| := abs_sub _ _
      _ ≤ (∑ k ∈ gradFullDiscs N, gradQuadCell s (1 - s + α) (N : ℕ) ℓ C₁ C0 x k) + Kc := by
        linarith [hDbound, hcell0]

/-- The decomposition of the full-window reference field: the kernel term with coefficient
`ψ'(x/ℓ)`, and the remainder. The two boundary values of the kernel `h = gradKernelH s` at `±1/2`
vanish, so the displacement term of `gradV2_eq_split` drops out. -/
theorem full_V_decomp {s : ℝ} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hper : Function.Periodic ψ ℓ⁻¹) (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hP : ¬GradPartial N ℓ γ) (X : Fin (N : ℕ) → ℝ) {i : ℤ} (hi : i ∈ gradLabels N ℓ γ)
    (hR : IntervalIntegrable (gradCellR s (N : ℕ) ℓ ψ (gradLift N X i)) volume
      (((N : ℕ) : ℝ) * (-1 / 2)) (((N : ℕ) : ℝ) * (1 / 2))) :
    gradVdisc2 s ψ N ℓ γ X i + gradVbg s ψ N ℓ γ X i
      = 2 * deriv ψ (gradLift N X i / ℓ) * (-(((N : ℕ) : ℝ) ^ (-s))
          * ∑ j ∈ (gradLabels N ℓ γ).erase i,
              deriv (gradKernelH s) (((gradPathIncr N ℓ γ i j : ℤ) : ℝ) / ((N : ℕ) : ℝ)))
        + 2 * ((∑ j ∈ (gradLabels N ℓ γ).erase i,
              gradCellR s (N : ℕ) ℓ ψ (gradLift N X i) ((gradPathIncr N ℓ γ i j : ℤ) : ℝ))
            - ∫ w in (-(((N : ℕ) : ℝ) / 2))..(((N : ℕ) : ℝ) / 2),
                gradCellR s (N : ℕ) ℓ ψ (gradLift N X i) w) := by
  have hp : Function.Periodic ψ (1 / ℓ) := by
    rw [one_div]
    exact hper
  have hK : ∀ j ∈ (gradLabels N ℓ γ).erase i,
      2 * |(gradPathIncr N ℓ γ i j : ℤ)| ≤ ((N : ℕ) : ℤ) ∧ gradPathIncr N ℓ γ i j ≠ 0 := by
    intro j hj
    obtain ⟨hne, hjl⟩ := Finset.mem_erase.mp hj
    exact ⟨two_abs_gradPathIncr_le hi hjl, gradPathIncr_ne_zero hi hjl hne⟩
  have ha : gradBLo N ℓ γ (gradLift N X i) - gradLift N X i = -1 / 2 := by
    unfold gradBLo
    simp only [hP, ↓reduceIte]
    ring
  have hb : gradBHi N ℓ γ (gradLift N X i) - gradLift N X i = 1 / 2 := by
    unfold gradBHi
    simp only [hP, ↓reduceIte]
    ring
  have hsplit := gradV2_eq_split hψ hℓ0 hp hs0 hs1 (N := N) (fun h => absurd h hP) X i
    (-1 / 2) (1 / 2) ha hb (by norm_num) (by norm_num [abs_of_neg]) (by norm_num)
    (fun h => by norm_num at h) (fun h => by norm_num at h) hR hK
  have hH : gradKernelH s (1 / 2) = 0 := gradKernelH_half s
  have hHm : gradKernelH s (-1 / 2) = 0 := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, gradSplit_gradKernelH_even, hH]
  have e1 : ((N : ℕ) : ℝ) * (-1 / 2) = -(((N : ℕ) : ℝ) / 2) := by ring
  have e2 : ((N : ℕ) : ℝ) * (1 / 2) = ((N : ℕ) : ℝ) / 2 := by ring
  rw [e1, e2] at hsplit
  rw [hsplit, hH, hHm]
  ring

/-- The power comparison `N^{-s} K^a ≤ N K^a (1 + N|x|)^{-(1+s/2)}` for `|x| ≤ 1/2`. -/
lemma full_rpow_le {s a : ℝ} (hs0 : 0 < s) {N : ℕ} (hN : 2 ≤ N) (K x : ℝ) (hK : 0 ≤ K)
    (hx : 0 ≤ x) (hx2 : x ≤ 1 / 2) :
    ((N : ℝ) ^ (-s)) * K ^ a ≤ (N : ℝ) * K ^ a / (1 + (N : ℝ) * x) ^ (1 + s / 2) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hbase : 1 + (N : ℝ) * x ≤ N := by nlinarith
  have hbase0 : (0 : ℝ) ≤ 1 + (N : ℝ) * x := by positivity
  have hD1 : (1 + (N : ℝ) * x) ^ (1 + s / 2) ≤ (N : ℝ) ^ (1 + s / 2) :=
    Real.rpow_le_rpow hbase0 hbase (by linarith)
  have hD2 : (N : ℝ) ^ (1 + s / 2) ≤ (N : ℝ) ^ (1 + s) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hD : 0 < (1 + (N : ℝ) * x) ^ (1 + s / 2) := by
    apply Real.rpow_pos_of_pos
    linarith [mul_nonneg hNpos.le hx]
  have hprod : (N : ℝ) ^ (-s) * (N : ℝ) ^ (1 + s) = N := by
    rw [← Real.rpow_add hNpos]
    rw [show -s + (1 + s) = 1 by ring, Real.rpow_one]
  have hNs : (N : ℝ) ^ (-s) * (1 + (N : ℝ) * x) ^ (1 + s / 2) ≤ N := by
    calc (N : ℝ) ^ (-s) * (1 + (N : ℝ) * x) ^ (1 + s / 2)
        ≤ (N : ℝ) ^ (-s) * (N : ℝ) ^ (1 + s) :=
          mul_le_mul_of_nonneg_left (hD1.trans hD2) (Real.rpow_nonneg hNpos.le _)
      _ = N := hprod
  have hKa : 0 ≤ K ^ a := Real.rpow_nonneg hK _
  rw [le_div_iff₀ hD]
  have : (N : ℝ) ^ (-s) * (1 + (N : ℝ) * x) ^ (1 + s / 2) * K ^ a ≤ (N : ℝ) * K ^ a :=
    mul_le_mul_of_nonneg_right hNs hKa
  linarith [this]

/-- Logarithmic losses are absorbed into a power: `1 + log K ≤ (1 + 1/ε) K^ε` for `K ≥ 1`. -/
lemma one_add_log_le_rpow {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 < ε) :
    1 + Real.log K ≤ (1 + 1 / ε) * K ^ ε := by
  have hlog : Real.log K ≤ K ^ ε / ε := Real.log_le_rpow_div (by linarith) hε
  have h1 : 1 ≤ K ^ ε := Real.one_le_rpow hK hε.le
  have h2 : K ^ ε / ε = 1 / ε * K ^ ε := by ring
  nlinarith

/-- The circular distance scales with the period: `circDist N (N x) = N · circDist 1 x`. -/
lemma circDist_nat_mul_self {N : ℕ} (hN : 0 < N) (x : ℝ) :
    circDist (N : ℝ) ((N : ℝ) * x) = (N : ℝ) * circDist 1 x := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold circDist
  rw [show (N : ℝ) * x / (N : ℝ) = x by field_simp, one_mul, div_one]
  rw [show (N : ℝ) * x - (N : ℝ) * round x = (N : ℝ) * (x - round x) by ring, abs_mul,
    abs_of_pos (by exact_mod_cast hN)]

/-- The quadrature part of Lemma 5.7, full window: the reference field
`V^{(2)}_i` is bounded by `C C_0 K^ε (ℓ^{-1} w_2(x_i/ℓ) + N K^a (1 + N|x_i|)^{-(1+s/2)})`, with
`κ = 1`, `K = Nℓ`, `a = 1 - s + α`, and `|x_i|` the circular distance from `0`. The constant `C`
depends on `s, α, ε` only. -/
theorem gradV2_full_bound {s α : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hα0 : s - 1 ≤ α)
    (hα1 : α < s / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ C0 : ℝ) (ψ : ℝ → ℝ) (X : Fin (N : ℕ) → ℝ) (i : ℤ),
      2 ≤ (N : ℕ) → ¬GradPartial N ℓ γ → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → 0 ≤ C0 →
      ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      i ∈ gradLabels N ℓ γ →
      |gradVdisc2 s ψ N ℓ γ X i + gradVbg s ψ N ℓ γ X i|
        ≤ C * C0 * ((N : ℝ) * ℓ) ^ ε *
          (ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
            + (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α)
              / (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)) := by
  have ha0 : 0 ≤ 1 - s + α := by linarith
  have ha1 : 1 - s + α < 1 - s / 2 := by linarith
  obtain ⟨Cc, hCc, hcells⟩ := gradient_splitting_cells hs0 hs1 hα0 hα1
  obtain ⟨C₁, hC₁, hC1⟩ := cell_abs_deriv_integral_le hs0 hs1 hα0 hα1
  obtain ⟨CQ, hCQ, hQ⟩ := sum_erase_gradQuadCell_le hs0 hs1 ha0 ha1
  have hA1 : 0 ≤ |deriv (gradKernelH s) (1 / 2)| := abs_nonneg _
  have hpos1 : 0 < 1 + 1 / ε := by positivity
  refine ⟨4 * |deriv (gradKernelH s) (1 / 2)| + 2 * (CQ * C₁ * (1 + 1 / ε)) + 2 * Cc,
    by have := mul_pos (mul_pos hCQ hC₁) hpos1; linarith, ?_⟩
  intro N ℓ γ C0 ψ X i hN hP hℓ hℓ1 hK hC0 hψ hper h1 h2 hi
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hK1 : (1 : ℝ) ≤ ((N : ℕ) : ℝ) * ℓ := hK
  set x := gradLift N X i with hxdef
  -- the cell weights and the central cell
  have hD : ∀ k : ℤ, 1 ≤ |(k : ℝ)| → |(k : ℝ)| ≤ ((N : ℕ) : ℝ) / 2 →
      ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), |deriv (gradCellR s (N : ℕ) ℓ ψ x) v|
        ≤ gradQuadCell s (1 - s + α) (N : ℕ) ℓ C₁ C0 x k :=
    fun k hk1 hkN => hC1 (N : ℕ) ℓ C0 x ψ k hN hℓ hℓ1 hK hC0 hψ hper h1 h2 hk1 hkN
  have hint := intervalIntegrable_gradCellR_half (x := x) hs0 hs1 hα0 hα1 hN hℓ hℓ1 hK hC0 hψ
    hper h1 h2
  have hR : IntervalIntegrable (gradCellR s (N : ℕ) ℓ ψ x) volume
      (((N : ℕ) : ℝ) * (-1 / 2)) (((N : ℕ) : ℝ) * (1 / 2)) := by
    rw [show ((N : ℕ) : ℝ) * (-1 / 2) = -(((N : ℕ) : ℝ) / 2) by ring,
      show ((N : ℕ) : ℝ) * (1 / 2) = ((N : ℕ) : ℝ) / 2 by ring]
    exact hint
  have hcen : |∫ v in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), gradCellR s (N : ℕ) ℓ ψ x v|
      ≤ Cc * C0 * ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℕ) * ℓ) ℓ⁻¹ (x / ℓ) := by
    have h5 := (hcells (N : ℕ) ℓ C0 x ψ hN hℓ hℓ1 hK hC0 hψ hper h1 h2).2.2.2.2.1
    have habs := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
      (f := fun v => gradCellR s (N : ℕ) ℓ ψ x v) (a := -(1 / 2 : ℝ)) (b := 1 / 2) (by norm_num)
    exact habs.trans h5
  have hrem := full_remainder_bound hs0 hs1 hα0 hα1 hψ hper hN hP hℓ hℓ1 hK hC0 h1 h2 hi hD hcen
  have hodd := full_odd_sum_bound hs0 hs1 hP hi
  have hV := full_V_decomp hψ hℓ hper hs0 hs1 hP X hi hR
  -- the kernel coefficient
  have hpsi : |deriv ψ (x / ℓ)| ≤ C0 * ((N : ℝ) * ℓ) ^ (1 - s + α) :=
    le_trans (h1 _) (mul_le_mul_of_nonneg_left (gradWeightOne_le_K_pow hs1 ha0 hK) hC0)
  -- the remainder and the odd sum, with the kernel term at `±1/2` made explicit
  simp only [iteratedDeriv_one] at hrem hV
  have hNps0 : (0 : ℝ) ≤ ((N : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg hNpos.le _
  have hK0 : (0 : ℝ) ≤ ((N : ℕ) : ℝ) * ℓ := by positivity
  have hKa0 : (0 : ℝ) ≤ (((N : ℕ) : ℝ) * ℓ) ^ (1 - s + α) := Real.rpow_nonneg hK0 _
  have hKε1 : (1 : ℝ) ≤ (((N : ℕ) : ℝ) * ℓ) ^ ε := Real.one_le_rpow hK1 hε.le
  have hKε0 : (0 : ℝ) ≤ (((N : ℕ) : ℝ) * ℓ) ^ ε := by linarith
  have hc0 : 0 ≤ circDist 1 x := gradCell_circDist_nonneg 1 x
  have hT0 : 0 ≤ ℓ⁻¹ * gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) :=
    mul_nonneg (inv_nonneg.mpr hℓ.le) (gradWeightTwo_nonneg_unconditional _ _ _ _ _)
  have hY0 : 0 ≤ ((N : ℕ) : ℝ) * (((N : ℕ) : ℝ) * ℓ) ^ (1 - s + α)
      / (1 + ((N : ℕ) : ℝ) * circDist 1 x) ^ (1 + s / 2) :=
    div_nonneg (mul_nonneg hNpos.le hKa0) (Real.rpow_nonneg (by nlinarith) _)
  have hlogK := one_add_log_le_rpow hK1 hε
  have hxhalf : circDist 1 x ≤ 1 / 2 := by
    have := circDist_le_half (L := 1) one_pos x
    linarith
  -- the kernel coefficient times the odd sum
  have hS : |∑ j ∈ (gradLabels N ℓ γ).erase i,
      deriv (gradKernelH s) (((gradPathIncr N ℓ γ i j : ℤ) : ℝ) / ((N : ℕ) : ℝ))|
        ≤ |deriv (gradKernelH s) (1 / 2)| := hodd
  have hE := hrem
  have hQ' := hQ (N : ℕ+) ℓ γ x C₁ C0 i hN hP hℓ hℓ1 hK hC₁.le hC0 hi
  rw [circDist_nat_mul_self (N := (N : ℕ)) N.pos x] at hQ'
  have hNx := full_rpow_le (a := 1 - s + α) hs0 hN (((N : ℕ) : ℝ) * ℓ) (circDist 1 x) hK0 hc0 hxhalf
  -- abbreviations for the pieces of the decomposition
  set S := ∑ j ∈ (gradLabels N ℓ γ).erase i,
    deriv (gradKernelH s) (((gradPathIncr N ℓ γ i j : ℤ) : ℝ) / ((N : ℕ) : ℝ)) with hSdef
  set G := ∑ j ∈ (gradLabels N ℓ γ).erase i,
    gradQuadCell s (1 - s + α) (N : ℕ) ℓ C₁ C0 x (gradPathIncr N ℓ γ i j) with hGdef
  set E := (∑ j ∈ (gradLabels N ℓ γ).erase i, gradCellR s (N : ℕ) ℓ ψ x ((gradPathIncr N ℓ γ i j : ℤ) : ℝ))
    - ∫ w in (-(((N : ℕ) : ℝ) / 2))..(((N : ℕ) : ℝ) / 2), gradCellR s (N : ℕ) ℓ ψ x w with hEdef
  set Kc := Cc * C0 * ℓ⁻¹ * gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) with hKcdef
  set Nps := ((N : ℕ) : ℝ) ^ (-s) with hNpsdef
  set Ka := (((N : ℕ) : ℝ) * ℓ) ^ (1 - s + α) with hKadef
  set Kε := (((N : ℕ) : ℝ) * ℓ) ^ ε with hKεdef
  set A1 := |deriv (gradKernelH s) (1 / 2)| with hA1def
  set T := ℓ⁻¹ * gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) with hTdef
  set Y := ((N : ℕ) : ℝ) * Ka / (1 + ((N : ℕ) : ℝ) * circDist 1 x) ^ (1 + s / 2) with hYdef
  set P := deriv ψ (x / ℓ) with hPdef
  set Ev := (if (N : ℕ) % 2 = 0 then Nps * |P| * A1 else 0) with hEvdef
  -- the kernel term with the odd sum, and the remainder
  have hterm1 : |2 * P * (-Nps * S)| ≤ 2 * (Nps * (C0 * Ka) * A1) := by
    have e : |2 * P * (-Nps * S)| = 2 * Nps * (|P| * |S|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg hNps0, abs_two]
      ring
    rw [e]
    have hPS : |P| * |S| ≤ (C0 * Ka) * A1 := mul_le_mul hpsi hS (abs_nonneg _) (mul_nonneg hC0 hKa0)
    have h2N : 0 ≤ 2 * Nps := by positivity
    calc 2 * Nps * (|P| * |S|) ≤ 2 * Nps * ((C0 * Ka) * A1) := mul_le_mul_of_nonneg_left hPS h2N
      _ = 2 * (Nps * (C0 * Ka) * A1) := by ring
  have hterm2 : |2 * E| ≤ 2 * (G + Kc + Ev) := by
    rw [abs_mul, abs_two]
    linarith [hrem]
  have hA1nonneg : 0 ≤ A1 := abs_nonneg _
  have hEv_bound : Ev ≤ Nps * (C0 * Ka) * A1 := by
    rw [hEvdef]
    split_ifs
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpsi hNps0) hA1nonneg
    · exact mul_nonneg (mul_nonneg hNps0 (mul_nonneg hC0 hKa0)) hA1nonneg
  have hfin_total : |2 * P * (-Nps * S) + 2 * E| ≤ 2 * (Nps * (C0 * Ka) * A1) + 2 * (G + Kc + Ev) :=
    (abs_add_le _ _).trans (add_le_add hterm1 hterm2)
  -- the three comparisons
  have hTY : 0 ≤ T + Y := add_nonneg hT0 hY0
  have hNx' : Nps * Ka ≤ Y := hNx
  have hfa : 4 * (Nps * (C0 * Ka) * A1) ≤ 4 * (C0 * A1 * Kε) * Y := by
    have h1 : C0 * A1 ≤ C0 * A1 * Kε := le_mul_of_one_le_right (mul_nonneg hC0 hA1nonneg) hKε1
    calc 4 * (Nps * (C0 * Ka) * A1) = 4 * (C0 * A1) * (Nps * Ka) := by ring
      _ ≤ 4 * (C0 * A1) * Y := mul_le_mul_of_nonneg_left hNx' (by positivity)
      _ ≤ 4 * (C0 * A1 * Kε) * Y :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) hY0
  have hfd : 4 * (C0 * A1 * Kε) * Y ≤ 4 * (C0 * A1 * Kε) * (T + Y) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hfb : 2 * G ≤ 2 * (CQ * C₁ * C0 * ((1 + 1 / ε) * Kε)) * (T + Y) := by
    have hlog' : CQ * C₁ * C0 * (1 + Real.log (((N : ℕ) : ℝ) * ℓ))
        ≤ CQ * C₁ * C0 * ((1 + 1 / ε) * Kε) :=
      mul_le_mul_of_nonneg_left hlogK (mul_nonneg (mul_nonneg hCQ.le hC₁.le) hC0)
    have := mul_le_mul_of_nonneg_right hlog' hTY
    linarith [hQ', this]
  have hKcT : Kc = Cc * C0 * T := by
    rw [hKcdef, hTdef]
    ring
  have hfc : 2 * Kc ≤ 2 * (Cc * C0 * Kε) * (T + Y) := by
    have hT_le : T ≤ Kε * (T + Y) := by
      calc T ≤ T + Y := by linarith
        _ ≤ Kε * (T + Y) := le_mul_of_one_le_left hTY hKε1
    have := mul_le_mul_of_nonneg_left hT_le (mul_nonneg hCc.le hC0)
    rw [hKcT]
    linarith [this]
  have hsum_eq : (4 * A1 + 2 * (CQ * C₁ * (1 + 1 / ε)) + 2 * Cc) * C0 * Kε * (T + Y)
      = 4 * (C0 * A1 * Kε) * (T + Y) + 2 * (CQ * C₁ * C0 * ((1 + 1 / ε) * Kε)) * (T + Y)
        + 2 * (Cc * C0 * Kε) * (T + Y) := by
    ring
  rw [hV]
  calc |2 * P * (-Nps * S) + 2 * E| ≤ 2 * (Nps * (C0 * Ka) * A1) + 2 * (G + Kc + Ev) :=
        hfin_total
    _ ≤ (4 * A1 + 2 * (CQ * C₁ * (1 + 1 / ε)) + 2 * Cc) * C0 * Kε * (T + Y) := by
        rw [hsum_eq]
        linarith [hEv_bound, hfa, hfb, hfc, hfd]

end

end Riesz1
