/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingGapIdentity
public import Riesz1.Auxiliary.GradientSplittingDisplacementEvent
public import Riesz1.ToMathlib.Calculus.PowerSumFromPoint

/-!
# Path counting for the gap representative

The gap part of Lemma 5.7, the combinatorial step of the bound
on `W^gap`. For a fixed edge `e` (the residue `e mod N` of a label of the window) and a fixed label
`l`, the positive pairs `(l, m)` whose path contains `e` have lengths `k_{lm} ≥ (e - l) mod N + 1`,
and distinct partners have distinct lengths. Hence `∑_m k_{lm}^{-q} ≤ C (1 + d(e,l))^{1-q}`, where
`d` is the label distance. Symmetrically, the same bound holds for a fixed `m`. With `q = 2 + s/2`,
the exponent `q - 1 = 1 + s/2` is the exponent of the paper.
-/

@[expose] public section

open Finset
open scoped Classical

namespace Riesz1

noncomputable section

/-! ## Residues and the label distance -/

/-- Two integers with equal residues differ by a multiple of `N`. -/
lemma gapInt_sub_eq_mul {a b N : ℤ} (h : a % N = b % N) : ∃ c : ℤ, a - b = N * c := by
  refine ⟨a / N - b / N, ?_⟩
  rw [mul_sub]
  linarith [Int.emod_def a N, Int.emod_def b N]

/-- The label distance is the minimum of the residue of the separation and its complement. -/
lemma gradLabelDist_eq_min {N : ℕ+} {i j : ℤ} (h : |j - i| < ((N : ℕ) : ℤ)) :
    gradLabelDist N i j
      = min ((j - i) % ((N : ℕ) : ℤ)) (((N : ℕ) : ℤ) - (j - i) % ((N : ℕ) : ℤ)) := by
  unfold gradLabelDist
  rw [abs_lt] at h
  rcases le_or_gt 0 (j - i) with h0 | h0
  · rw [abs_of_nonneg h0, Int.emod_eq_of_lt h0 (by omega)]
  · have hr : (j - i) % ((N : ℕ) : ℤ) = (j - i) + ((N : ℕ) : ℤ) := by
      have h2 : (j - i + ((N : ℕ) : ℤ)) % ((N : ℕ) : ℤ) = (j - i + ((N : ℕ) : ℤ)) :=
        Int.emod_eq_of_lt (by omega) (by omega)
      have h3 := Int.add_mul_emod_self_left (j - i + ((N : ℕ) : ℤ)) ((N : ℕ) : ℤ) (-1)
      rw [show (j - i + ((N : ℕ) : ℤ)) + ((N : ℕ) : ℤ) * -1 = j - i from by ring] at h3
      rw [h3, h2]
    rw [abs_of_neg h0, hr, min_comm]
    congr 1 <;> ring

/-- The label distance is nonnegative on the window. -/
lemma gapLabelDist_nonneg {ℓ γ : ℝ} {N : ℕ+} {i j : ℤ} (hi : i ∈ gradLabels N ℓ γ)
    (hj : j ∈ gradLabels N ℓ γ) : 0 ≤ (gradLabelDist N i j : ℝ) := by
  have h := gradLabels_abs_sub_lt hi hj
  have h2 : (0 : ℤ) ≤ gradLabelDist N i j := by
    unfold gradLabelDist
    exact le_min (abs_nonneg _) (by omega)
  exact_mod_cast h2

/-- The label distance from `j` to `i` is at most the residue `(i - j) mod N`. -/
lemma gradLabelDist_le_emod {ℓ γ : ℝ} {N : ℕ+} {i j : ℤ} (hi : i ∈ gradLabels N ℓ γ)
    (hj : j ∈ gradLabels N ℓ γ) : gradLabelDist N j i ≤ (i - j) % ((N : ℕ) : ℤ) := by
  rw [gradLabelDist_eq_min (gradLabels_abs_sub_lt hj hi)]
  exact min_le_left _ _

/-! ## The edge of a positive path -/

/-- For a path from `l` to `m` of positive length `k` with `2k ≤ N` containing the edge `e`, the
residue `(e - l) mod N` is the offset `t < k` of the edge. -/
lemma gapEdge_offset {ℓ γ : ℝ} {N : ℕ+} {l m e : ℤ}
    (hk2 : 2 * gradPathIncr N ℓ γ l m ≤ ((N : ℕ) : ℤ))
    (hedge : gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ))) :
    ∃ t : ℕ, (t : ℤ) < gradPathIncr N ℓ γ l m ∧ (e - l) % ((N : ℕ) : ℤ) = (t : ℤ) := by
  obtain ⟨t, htk, ht⟩ := hedge
  have hk0 : (0 : ℤ) ≤ (t : ℤ) := by positivity
  have htN : (t : ℤ) < ((N : ℕ) : ℤ) := by omega
  refine ⟨t, htk, ?_⟩
  obtain ⟨c, hc⟩ := gapInt_sub_eq_mul (a := e) (b := l + t) (N := ((N : ℕ) : ℤ)) ht.symm
  have hsplit : e - l = (t : ℤ) + ((N : ℕ) : ℤ) * c := by linear_combination hc
  rw [hsplit, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hk0 htN]

/-- For a path from `l` to `m` of positive length `k` with `2k ≤ N` containing the edge `e`, the
residue `(m - e) mod N` lies in `[1, k]`. -/
lemma gapEdge_right_bounds {ℓ γ : ℝ} {N : ℕ+} {l m e : ℤ} (hl : l ∈ gradLabels N ℓ γ)
    (hm : m ∈ gradLabels N ℓ γ) (hlm : l ≠ m)
    (hk2 : 2 * gradPathIncr N ℓ γ l m ≤ ((N : ℕ) : ℤ))
    (hedge : gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ))) :
    1 ≤ (m - e) % ((N : ℕ) : ℤ) ∧ (m - e) % ((N : ℕ) : ℤ) ≤ gradPathIncr N ℓ γ l m := by
  obtain ⟨t, htk, ht⟩ := hedge
  obtain ⟨c1, hc1⟩ := (gradPathIncr_spec hl hm hlm).2.2.2
  obtain ⟨c2, hc2⟩ := gapInt_sub_eq_mul (a := l + t) (b := e) (N := ((N : ℕ) : ℤ)) ht
  have hk0t : (0 : ℤ) ≤ (t : ℤ) := by positivity
  have hres : (m - e) % ((N : ℕ) : ℤ) = (gradPathIncr N ℓ γ l m - t) % ((N : ℕ) : ℤ) := by
    obtain ⟨c, hc⟩ : ∃ c : ℤ, (m - e) = (gradPathIncr N ℓ γ l m - t) + ((N : ℕ) : ℤ) * c :=
      ⟨c1 + c2, by linear_combination hc1 + hc2⟩
    rw [hc, Int.add_mul_emod_self_left]
  have hkt : (gradPathIncr N ℓ γ l m - t) % ((N : ℕ) : ℤ) = gradPathIncr N ℓ γ l m - t :=
    Int.emod_eq_of_lt (by omega) (by omega)
  rw [hres, hkt]
  constructor <;> omega

/-! ## Injectivity of the lengths -/

/-- Two partners `m, m'` of `l` with the same length `k` coincide. -/
lemma gapPartner_eq {ℓ γ : ℝ} {N : ℕ+} {l m m' : ℤ} (hm : m ∈ gradLabels N ℓ γ)
    (hm' : m' ∈ gradLabels N ℓ γ) (hl : l ∈ gradLabels N ℓ γ) (hlm : l ≠ m) (hlm' : l ≠ m')
    (hk : gradPathIncr N ℓ γ l m = gradPathIncr N ℓ γ l m') : m = m' := by
  obtain ⟨c, hc⟩ := (gradPathIncr_spec hl hm hlm).2.2.2
  obtain ⟨c', hc'⟩ := (gradPathIncr_spec hl hm' hlm').2.2.2
  rw [hk] at hc
  have hdvd : ((N : ℕ) : ℤ) ∣ m - m' := ⟨c - c', by linear_combination hc - hc'⟩
  have h0 := Int.eq_zero_of_abs_lt_dvd hdvd (gradLabels_abs_sub_lt hm' hm)
  linarith

/-- Two starts `l, l'` of `m` with the same length `k` coincide. -/
lemma gapStart_eq {ℓ γ : ℝ} {N : ℕ+} {l l' m : ℤ} (hl : l ∈ gradLabels N ℓ γ)
    (hl' : l' ∈ gradLabels N ℓ γ) (hm : m ∈ gradLabels N ℓ γ) (hlm : l ≠ m) (hlm' : l' ≠ m)
    (hk : gradPathIncr N ℓ γ l m = gradPathIncr N ℓ γ l' m) : l = l' := by
  obtain ⟨c, hc⟩ := (gradPathIncr_spec hl hm hlm).2.2.2
  obtain ⟨c', hc'⟩ := (gradPathIncr_spec hl' hm hlm').2.2.2
  rw [hk] at hc
  have hdvd : ((N : ℕ) : ℤ) ∣ l' - l := ⟨c - c', by linear_combination hc - hc'⟩
  have h0 := Int.eq_zero_of_abs_lt_dvd hdvd (gradLabels_abs_sub_lt hl hl')
  linarith

/-! ## Tail sums over the path lengths -/

/-- Power sums over a finite set of integers above `τ ≥ 0`: for `q > 1`, the sum of `k^{-q}` is at
most `(1 + 1/(q-1)) (1 + τ)^{1-q}`. -/
lemma gapTail_int {q : ℝ} (hq : 1 < q) {τ : ℤ} (hτ : 0 ≤ τ) (T : Finset ℤ)
    (hT : ∀ k ∈ T, τ < k) :
    ∑ k ∈ T, (k : ℝ) ^ (-q) ≤ (1 + 1 / (q - 1)) * (1 + (τ : ℝ)) ^ (1 - q) := by
  have hk0 : ∀ k ∈ T, 0 ≤ k := fun k hk => by have := hT k hk; omega
  have hinj : Set.InjOn Int.toNat (T : Set ℤ) := by
    intro k hk k' hk' h
    have h1 := hk0 k hk
    have h2 := hk0 k' hk'
    omega
  have hcast : ∀ k ∈ T, (k : ℝ) ^ (-q) = (((k.toNat : ℕ) : ℝ)) ^ (-q) := by
    intro k hk
    rw [show (((k.toNat : ℕ) : ℝ)) = (k : ℝ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (hk0 k hk)]]
  rw [Finset.sum_congr rfl hcast, ← Finset.sum_image (f := fun n : ℕ => (n : ℝ) ^ (-q)) hinj]
  have hJ : 1 ≤ τ.toNat + 1 := by omega
  have hS : ∀ n ∈ T.image Int.toNat, τ.toNat + 1 ≤ n := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    have := hT k hk
    have := hk0 k hk
    omega
  have key := sum_natCast_rpow_neg_le_of_ge (by linarith : 1 < q) hJ (T.image Int.toNat) hS
  have hτc : ((τ.toNat + 1 : ℕ) : ℝ) = 1 + (τ : ℝ) := by
    have h1 : ((τ.toNat : ℕ) : ℝ) = (τ : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hτ]
    push_cast
    rw [h1]
    ring
  rw [hτc] at key
  exact key

/-! ## The two one-sided path sums -/

/-- The partners of a fixed label `l`: the positive paths from `l` whose edges contain the edge
`e`, summed with weight `k^{-q}`. -/
lemma gapSum_left {ℓ γ q : ℝ} {N : ℕ+} (hq : 1 < q) {l e : ℤ}
    (hl : l ∈ gradLabels N ℓ γ) (he : e ∈ gradLabels N ℓ γ) :
    ∑ m ∈ (gradLabels N ℓ γ).erase l,
      (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then
        ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-q) else 0)
      ≤ 2 ^ (q - 1) * (1 + 1 / (q - 1)) * (1 + (gradLabelDist N e l : ℝ)) ^ (1 - q) := by
  rw [← Finset.sum_filter]
  set S := ((gradLabels N ℓ γ).erase l).filter
    (fun m => 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ))) with hS
  have hmem : ∀ m ∈ S, m ∈ gradLabels N ℓ γ ∧ m ≠ l ∧ 0 < gradPathIncr N ℓ γ l m ∧
      gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) := by
    intro m hm
    rw [hS, Finset.mem_filter, Finset.mem_erase] at hm
    exact ⟨hm.1.2, hm.1.1, hm.2.1, hm.2.2⟩
  have hNpos : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  set τ := (e - l) % ((N : ℕ) : ℤ) with hτdef
  have hτ0 : (0 : ℤ) ≤ τ := Int.emod_nonneg _ hNpos.ne'
  -- every edge offset is below the length
  have hτk : ∀ m ∈ S, τ < gradPathIncr N ℓ γ l m := by
    intro m hm
    obtain ⟨hmI, hne, hk0, hedge⟩ := hmem m hm
    have hk2 := two_abs_gradPathIncr_le hl hmI
    rw [abs_of_pos hk0] at hk2
    obtain ⟨t, htk, ht⟩ := gapEdge_offset hk2 hedge
    rw [hτdef, ht]
    exact htk
  have hinj : Set.InjOn (fun m : ℤ => gradPathIncr N ℓ γ l m) (S : Set ℤ) := by
    intro m hm m' hm' h
    have h1 := hmem m hm
    have h2 := hmem m' hm'
    exact gapPartner_eq h1.1 h2.1 hl (Ne.symm h1.2.1) (Ne.symm h2.2.1) h
  have hdist : (gradLabelDist N e l : ℝ) ≤ (τ : ℝ) := by
    have hrel := gradLabelDist_le_emod he hl
    rw [gradLabelDist_comm] at hrel
    exact_mod_cast hrel
  have hC : 0 ≤ 1 + 1 / (q - 1) := by
    have : 0 < q - 1 := by linarith
    positivity
  have hτR : (0 : ℝ) ≤ (τ : ℝ) := by exact_mod_cast hτ0
  have hd0 := gapLabelDist_nonneg he hl
  have hpow : (1 + (τ : ℝ)) ^ (1 - q) ≤ (1 + (gradLabelDist N e l : ℝ)) ^ (1 - q) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have h2 : (1 : ℝ) ≤ 2 ^ (q - 1) := Real.one_le_rpow (by norm_num) (by linarith)
  calc ∑ m ∈ S, ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-q)
      = ∑ k ∈ S.image (fun m => gradPathIncr N ℓ γ l m), (k : ℝ) ^ (-q) :=
        (Finset.sum_image (f := fun k : ℤ => (k : ℝ) ^ (-q)) hinj).symm
    _ ≤ (1 + 1 / (q - 1)) * (1 + (τ : ℝ)) ^ (1 - q) := by
        apply gapTail_int hq hτ0
        intro k hk
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
        exact hτk m hm
    _ ≤ (1 + 1 / (q - 1)) * (1 + (gradLabelDist N e l : ℝ)) ^ (1 - q) :=
        mul_le_mul_of_nonneg_left hpow hC
    _ ≤ 2 ^ (q - 1) * (1 + 1 / (q - 1)) * (1 + (gradLabelDist N e l : ℝ)) ^ (1 - q) := by
        have hp0 : 0 ≤ (1 + (gradLabelDist N e l : ℝ)) ^ (1 - q) :=
          Real.rpow_nonneg (by have := gapLabelDist_nonneg he hl; linarith) _
        calc (1 + 1 / (q - 1)) * (1 + (gradLabelDist N e l : ℝ)) ^ (1 - q)
            ≤ 2 ^ (q - 1) * ((1 + 1 / (q - 1)) * (1 + (gradLabelDist N e l : ℝ)) ^ (1 - q)) :=
              le_mul_of_one_le_left (mul_nonneg hC hp0) h2
          _ = _ := by ring

/-- The starts of a fixed label `m`: the positive paths ending at `m` whose edges contain the edge
`e`, summed with weight `k^{-q}`. -/
lemma gapSum_right {ℓ γ q : ℝ} {N : ℕ+} (hq : 1 < q) {m e : ℤ}
    (hm : m ∈ gradLabels N ℓ γ) (he : e ∈ gradLabels N ℓ γ) :
    ∑ l ∈ (gradLabels N ℓ γ).erase m,
      (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then
        ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-q) else 0)
      ≤ 2 ^ (q - 1) * (1 + 1 / (q - 1)) * (1 + (gradLabelDist N e m : ℝ)) ^ (1 - q) := by
  rw [← Finset.sum_filter]
  set S := ((gradLabels N ℓ γ).erase m).filter
    (fun l => 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ))) with hS
  have hmem : ∀ l ∈ S, l ∈ gradLabels N ℓ γ ∧ l ≠ m ∧ 0 < gradPathIncr N ℓ γ l m ∧
      gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) := by
    intro l hl
    rw [hS, Finset.mem_filter, Finset.mem_erase] at hl
    exact ⟨hl.1.2, hl.1.1, hl.2.1, hl.2.2⟩
  have hC1 : 0 ≤ 1 + 1 / (q - 1) := by
    have : 0 < q - 1 := by linarith
    positivity
  have hC : 0 ≤ 2 ^ (q - 1) * (1 + 1 / (q - 1)) := by
    have : (0 : ℝ) < 2 ^ (q - 1) := by positivity
    exact mul_nonneg this.le hC1
  have hpd : 0 ≤ (1 + (gradLabelDist N e m : ℝ)) ^ (1 - q) :=
    Real.rpow_nonneg (by have := gapLabelDist_nonneg he hm; linarith) _
  rcases Finset.eq_empty_or_nonempty S with hempty | ⟨l0, hl0⟩
  · rw [hempty, Finset.sum_empty]
    exact mul_nonneg hC hpd
  -- the offset `σ = (m - e) mod N` is common to all starts
  have hσ : ∀ l ∈ S, 1 ≤ (m - e) % ((N : ℕ) : ℤ) ∧
      (m - e) % ((N : ℕ) : ℤ) ≤ gradPathIncr N ℓ γ l m := by
    intro l hl
    obtain ⟨hlI, hne, hk0, hedge⟩ := hmem l hl
    have hk2 := two_abs_gradPathIncr_le hlI hm
    rw [abs_of_pos hk0] at hk2
    exact gapEdge_right_bounds hlI hm hne hk2 hedge
  have hk2 : 2 * gradPathIncr N ℓ γ l0 m ≤ ((N : ℕ) : ℤ) := by
    have := two_abs_gradPathIncr_le (hmem l0 hl0).1 hm
    rwa [abs_of_pos (hmem l0 hl0).2.2.1] at this
  set σ := (m - e) % ((N : ℕ) : ℤ) with hσdef
  have hσ1 : 1 ≤ σ := (hσ l0 hl0).1
  have hσk : σ ≤ gradPathIncr N ℓ γ l0 m := (hσ l0 hl0).2
  have hσ0 : (0 : ℤ) ≤ σ - 1 := by linarith
  -- on the nonempty sum the label distance is exactly `σ`
  have hd : (gradLabelDist N e m : ℝ) = (σ : ℝ) := by
    have hmin : gradLabelDist N e m = σ := by
      rw [gradLabelDist_eq_min (gradLabels_abs_sub_lt he hm), ← hσdef]
      exact min_eq_left (by linarith)
    rw [hmin]
  have hinj : Set.InjOn (fun l : ℤ => gradPathIncr N ℓ γ l m) (S : Set ℤ) := by
    intro l hl l' hl' h
    have h1 := hmem l hl
    have h2 := hmem l' hl'
    exact gapStart_eq h1.1 h2.1 hm h1.2.1 h2.2.1 h
  have hpow : (σ : ℝ) ^ (1 - q) ≤ 2 ^ (q - 1) * (1 + (σ : ℝ)) ^ (1 - q) := by
    have hσR : (1 : ℝ) ≤ (σ : ℝ) := by exact_mod_cast hσ1
    have h1 : (1 + (σ : ℝ)) / 2 ≤ (σ : ℝ) := by linarith
    have h2 : (σ : ℝ) ^ (1 - q) ≤ ((1 + (σ : ℝ)) / 2) ^ (1 - q) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) h1 (by linarith)
    have h2q : (2 : ℝ) ^ (1 - q) = ((2 : ℝ) ^ (q - 1))⁻¹ := by
      rw [show (1 : ℝ) - q = -(q - 1) by ring, Real.rpow_neg (by norm_num)]
    have h3 : ((1 + (σ : ℝ)) / 2) ^ (1 - q) = 2 ^ (q - 1) * (1 + (σ : ℝ)) ^ (1 - q) := by
      rw [Real.div_rpow (by linarith) (by norm_num), h2q, div_inv_eq_mul]
      ring
    linarith
  calc ∑ l ∈ S, ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-q)
      = ∑ k ∈ S.image (fun l => gradPathIncr N ℓ γ l m), (k : ℝ) ^ (-q) :=
        (Finset.sum_image (f := fun k : ℤ => (k : ℝ) ^ (-q)) hinj).symm
    _ ≤ (1 + 1 / (q - 1)) * (1 + ((σ - 1 : ℤ) : ℝ)) ^ (1 - q) := by
        apply gapTail_int hq hσ0
        intro k hk
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
        have := (hσ l hl).2
        omega
    _ = (1 + 1 / (q - 1)) * (σ : ℝ) ^ (1 - q) := by
        rw [show (1 + ((σ - 1 : ℤ) : ℝ)) = (σ : ℝ) by push_cast; ring]
    _ ≤ (1 + 1 / (q - 1)) * (2 ^ (q - 1) * (1 + (σ : ℝ)) ^ (1 - q)) :=
        mul_le_mul_of_nonneg_left hpow hC1
    _ = 2 ^ (q - 1) * (1 + 1 / (q - 1)) * (1 + (gradLabelDist N e m : ℝ)) ^ (1 - q) := by
        rw [hd]
        ring

end

end Riesz1
