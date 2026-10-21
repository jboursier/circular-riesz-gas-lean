/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlGapBounds
public import Riesz1.Variance.VarAlTransfer
public import Riesz1.Variance.APrioriCutoffSupport
public import Riesz1.Variance.APrioriCutoffChain
public import Riesz1.Variance.ConvexificationEnergyBound

/-!
# The selected edges of the loop gap field

The window and covector identifications used in Proposition 5.9.
All objects are the actual definitions, including the cyclic wrapping edge.
-/

@[expose] public section

noncomputable section

open Finset MeasureTheory
open scoped ContDiff

namespace Riesz1

theorem varAlGap_index_eq (N : ℕ+) (j : ℤ) : gradIndex N j = labelOf N j := rfl

/-- The auxiliary integer window represents exactly the variance window. -/
theorem varAlGap_window_eq {N : ℕ+} {ℓ γ : ℝ} (hK : 1 ≤ (N : ℝ) * ℓ) :
    window N ((N : ℝ) * ℓ) γ = (gradLabels N ℓ γ).image (gradIndex N) := by
  classical
  have hpow : 0 ≤ ((N : ℝ) * ℓ) ^ γ := Real.rpow_nonneg (by linarith) _
  by_cases hp : GradPartial N ℓ γ
  · rw [window_partial hpow hp]
    have hfloor : (⌊((N : ℝ) * ℓ) ^ γ⌋₊ : ℤ) = ⌊((N : ℝ) * ℓ) ^ γ⌋ :=
      Int.natCast_floor_eq_floor hpow
    simp only [gradLabels, hp, ↓reduceIte, gradM, hfloor]
    rfl
  · rw [window_full hp]
    ext i
    simp only [mem_univ, true_iff, mem_image]
    refine ⟨(i.val : ℤ), (mem_gradLabels_full hp _).2 ⟨by positivity, by exact_mod_cast i.isLt⟩, ?_⟩
    exact labelOf_natCast N i

theorem varAlGap_next_index (N : ℕ+) (j : ℤ) :
    nextLabel N (gradIndex N j) = gradIndex N (j + 1) := APG.nextLabel_labelOf j

/-- Each positive path edge lies among the selected nearest-neighbour edges. -/
theorem varAlGap_path_edge_mem {N : ℕ+} {ℓ γ δ : ℝ}
    (hK : 1 ≤ (N : ℝ) * ℓ) (hγδ : γ ≤ δ) {j : ℤ}
    (hj : j ∈ gradLabels N ℓ γ) (hj1 : gradInWindow N ℓ γ (j + 1)) :
    gradIndex N j ∈ nearestPairs N (window N ((N : ℝ) * ℓ) δ) := by
  classical
  by_cases hp : GradPartial N ℓ δ
  · have hpγ : GradPartial N ℓ γ :=
      (Real.rpow_le_rpow_of_exponent_le hK hγδ).trans_lt hp
    rw [nearestPairs, mem_filter, varAlGap_window_eq hK, varAlGap_next_index]
    exact ⟨mem_image_of_mem _ (varAl_gradInWindow_mono hK hγδ (fun _ => hj) hp),
      mem_image_of_mem _ (varAl_gradInWindow_mono hK hγδ hj1 hp)⟩
  · rw [window_full hp]
    simp [nearestPairs]

/-- The smaller-window covector vanishes off the convexified edge set. -/
theorem varAlGap_covector_support {N : ℕ+} {ℓ γ δ s : ℝ}
    (hK : 1 ≤ (N : ℝ) * ℓ) (hγδ : γ ≤ δ) (ψ : ℝ → ℝ)
    (X : Fin (N : ℕ) → ℝ) (e : Fin (N : ℕ))
    (he : e ∉ nearestPairs N (window N ((N : ℝ) * ℓ) δ)) :
    gradWgap s ψ N ℓ γ X (e.val : ℤ) = 0 := by
  classical
  have hpδ : GradPartial N ℓ δ := by
    by_contra h
    apply he
    rw [window_full h]
    simp [nearestPairs]
  have hp : GradPartial N ℓ γ :=
    (Real.rpow_le_rpow_of_exponent_le hK hγδ).trans_lt hpδ
  apply gradWgap_eq_zero_of_partial ψ X hp
  intro j hj hj1 hje
  apply he
  have hi : gradIndex N j = e := by
    rw [varAlGap_index_eq]
    apply Fin.ext
    change (j % (N : ℤ)).toNat = e.val
    rw [hje, Int.toNat_natCast]
  rw [← hi]
  exact varAlGap_path_edge_mem hK hγδ
    ((mem_gradLabels_partial hp j).2 ⟨hj, by omega⟩)
    (fun _ => (mem_gradLabels_partial hp (j + 1)).2 ⟨by omega, by omega⟩)

/-- Reindex one cyclic period by the actual particle labels. -/
theorem varAlGap_sum_Ico (N : ℕ+) (f : ℤ → ℝ) :
    ∑ e ∈ Ico (0 : ℤ) N, f e = ∑ e : Fin (N : ℕ), f (e.val : ℤ) := by
  classical
  symm
  apply Finset.sum_bij (fun e _ => (e.val : ℤ))
  · intro e _
    exact mem_Ico.2 ⟨by positivity, by exact_mod_cast e.isLt⟩
  · intro a _ b _ hab
    exact Fin.ext (by exact_mod_cast hab)
  · intro e he
    have hh := mem_Ico.1 he
    exact ⟨⟨e.toNat, by omega⟩, mem_univ _, by exact Int.toNat_of_nonneg hh.1⟩
  · intro e _
    rfl

/-- On anchored vectors the cyclic differences are the edge forms. -/
theorem varAlGap_edgeForm (n : ℕ) (U : Fin n → ℝ) (e : Fin (n.succPNat : ℕ)) :
    gradEdgeDiff n.succPNat (anchorVector U) (e.val : ℤ) = edgeForm n e U := by
  have hi : gradIndex n.succPNat (e.val : ℤ) = e := labelOf_natCast _ e
  have hi1 : gradIndex n.succPNat ((e.val : ℤ) + 1) = nextLabel n.succPNat e := by
    rw [← varAlGap_next_index, hi]
  simp only [gradEdgeDiff, hi, hi1]
  exact (edgeForm_apply n e U).symm

/-- The anchored cutoff gap field has coefficients `-η Wgap`, with
support in the convexified larger window. -/
theorem varAlGap_covector_identity {n : ℕ} {ℓ γ δ s : ℝ} {ψ : ℝ → ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hp : Function.Periodic ψ ℓ⁻¹)
    (hK : 1 ≤ (n.succPNat : ℝ) * ℓ) (hγδ : γ ≤ δ)
    {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n) (η : ℝ) (U : Fin n → ℝ) :
    dotProd (fun i => η * gradWfield s ψ n.succPNat ℓ γ (anchorVector y) i.succ) U =
      ∑ e ∈ nearestPairs n.succPNat (window n.succPNat ((n.succPNat : ℝ) * ℓ) δ),
        (-η * gradWgap s ψ n.succPNat ℓ γ (anchorVector y) (e.val : ℤ)) *
          (((n : ℝ) + 1) * edgeForm n e U) := by
  classical
  have h := gradient_splitting_gap_identity (γ := γ) hs0 hs1 hp
    (varAl_anchorVector_mem hy) (anchorVector U)
  change (∑ k : Fin (n + 1), _) = _ at h
  rw [Fin.sum_univ_succ] at h
  have hz : anchorVector U (0 : Fin (n + 1)) = 0 := anchorVector_zero U
  simp only [hz, mul_zero, anchorVector_succ, zero_add] at h
  rw [varAlGap_sum_Ico] at h
  simp only [varAlGap_edgeForm] at h
  unfold dotProd
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, h, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [← Finset.sum_subset (subset_univ (nearestPairs n.succPNat
    (window n.succPNat ((n.succPNat : ℝ) * ℓ) δ)))]
  · apply Finset.sum_congr rfl
    intro e _
    simp only [Nat.succPNat_coe, Nat.cast_succ]
    ring
  · intro e _ he
    rw [varAlGap_covector_support hK hγδ ψ (anchorVector y) e he]
    ring

/-- Continuity of the existing finite path sum on the physical domain. -/
theorem varAlGap_continuousOn_covector {s ℓ γ : ℝ} {N : ℕ+} {ψ : ℝ → ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hℓ : 0 < ℓ) (hψ : ContDiff ℝ ∞ ψ) (e : ℤ) :
    ContinuousOn (fun X => gradWgap s ψ N ℓ γ X e) (orderedDomain N) := by
  classical
  unfold gradWgap
  apply continuousOn_const.mul
  apply continuousOn_finsetSum
  intro l hl
  apply continuousOn_finsetSum
  intro m hm
  split_ifs with hc
  · have hmI := Finset.mem_of_mem_erase hm
    have hlm : l ≠ m := fun h => (Finset.mem_erase.mp hm).1 h.symm
    intro X hX
    have hnon := nonInt_of_mem_orderedDomain (ℓ := ℓ) (γ := γ) hℓ.le hX
    have hpair : Continuous (fun Y : Fin (N : ℕ) → ℝ =>
        (gradLift N Y l, gradLift N Y l + gradSep N ℓ γ Y l m)) :=
      (contDiff_gradLift N l).continuous.prodMk
        ((contDiff_gradLift N l).continuous.add (continuous_gradSep N ℓ γ l m))
    exact ((((continuous_gradZ_pair hψ ℓ).comp hpair).continuousAt).mul
      ((ContinuousAt.comp (g := deriv (gradKernelH s)) (f := fun Y => gradSep N ℓ γ Y l m)
        (continuousAt_deriv_gradKernelH hs0 hs1 (gradSep_ne_coe_zero hnon hl hmI hlm))
        (continuous_gradSep N ℓ γ l m).continuousAt).sub continuousAt_const)).continuousWithinAt
  · exact continuousOn_const

/-- For short increments from a chosen representative, membership of
the endpoint is equivalent to membership of its residue in the window. -/
theorem varAlGap_endpoint_mem {N : ℕ+} {ℓ γ : ℝ} (hK : 1 ≤ (N : ℝ) * ℓ)
    {i k : ℤ} (hi : i ∈ gradLabels N ℓ γ)
    (hk : -((N : ℤ) / 2) ≤ k ∧ k ≤ (N : ℤ) / 2) :
    gradInWindow N ℓ γ (i + k) ↔
      gradIndex N (i + k) ∈ window N ((N : ℝ) * ℓ) γ := by
  classical
  by_cases hp : GradPartial N ℓ γ
  · have hM : 8 * ⌊gradM N ℓ γ⌋ < (N : ℤ) := by
      have hfloor := Int.floor_le (gradM N ℓ γ)
      have hh : (8 : ℝ) * (⌊gradM N ℓ γ⌋ : ℝ) < (N : ℝ) := by
        change gradM N ℓ γ < (N : ℝ) / 8 at hp
        linarith
      exact_mod_cast hh
    rw [varAlGap_window_eq hK, mem_image]
    constructor
    · intro hj
      exact ⟨i + k, hj hp, rfl⟩
    · rintro ⟨j, hj, hji⟩ _
      have hI := (mem_gradLabels_partial hp i).1 hi
      have hJ := (mem_gradLabels_partial hp j).1 hj
      have hmod : j % (N : ℤ) = (i + k) % (N : ℤ) := by
        have := congrArg (fun e : Fin (N : ℕ) => (e.val : ℤ)) hji
        simpa only [varAlGap_index_eq, labelOf_val_int] using this
      have hN : (0 : ℤ) < N := by exact_mod_cast N.pos
      have hij : j = i + k := eq_of_emod_eq_of_abs_lt hN hmod (by
        rw [abs_lt]
        constructor <;> omega)
      rwa [← hij]
  · rw [window_full hp]
    simp [gradInWindow, hp]

end Riesz1

end
