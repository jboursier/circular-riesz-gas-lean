/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodGradientEuclid
public import Riesz1.Variance.APrioriGoodComparison

/-!
# Selected-edge support of the cutoff differential

In the proof of Lemma 5.2, every edge of a short arc between
window labels belongs to the selected nearest-neighbour edges. Thus the
gap cutoff depends only on those edges, and all its other partial
derivatives vanish, at every gap vector.
-/

@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace Riesz1

variable {N : ℕ+}

/-- Two-particle check: both cyclic directed edges are selected at
every scale at least one and nonnegative window exponent. -/
theorem nearestPairs_window_two (K γ : ℝ) (hK : 1 ≤ K) (hγ : 0 ≤ γ) :
    nearestPairs (2 : ℕ+) (window 2 K γ) = univ := by
  have h : ¬ K ^ γ < (((2 : ℕ+) : ℕ) : ℝ) / 8 := by
    have := Real.one_le_rpow hK hγ
    norm_num
    linarith
  rw [window_full h]
  exact Finset.filter_true_of_mem fun i _ => Finset.mem_univ (nextLabel 2 i)

/-- Every edge in a cutoff pair's short arc is a selected edge. This
includes both orientations and the wrap around label zero. -/
theorem cutoff_arc_mem_nearestPairs {K γ : ℝ} (hK : 1 ≤ K) (hγ : 0 ≤ γ)
    {p : Fin (N : ℕ) × ℤ} (hp : p ∈ cutoffPairs N (window N K γ)) {r : ℤ}
    (hr : r ∈ Ico ((p.1 : ℕ) : ℤ) (((p.1 : ℕ) : ℤ) + p.2) ∪
      Ico (((p.1 : ℕ) : ℤ) + p.2) ((p.1 : ℕ) : ℤ)) :
    labelOf N r ∈ nearestPairs N (window N K γ) := by
  have hK0 : 0 ≤ K ^ γ := (Real.one_le_rpow hK hγ).trans' zero_le_one
  by_cases hpart : K ^ γ < ((N : ℕ) : ℝ) / 8
  · have hw := window_partial hK0 hpart
    have h8 : 8 * ⌊K ^ γ⌋₊ < (N : ℕ) := by
      have hfl := Nat.floor_le hK0
      have : (8 : ℝ) * ⌊K ^ γ⌋₊ < ((N : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    have hmem := Finset.mem_filter.1 hp
    have hk : -(↑((N : ℕ) / 2) : ℤ) ≤ p.2 ∧ p.2 ≤ ↑((N : ℕ) / 2) :=
      Finset.mem_Icc.1 (Finset.mem_erase.1 (Finset.mem_product.1 hmem.1).2).2
    have hpi := hmem.2.1
    have hpk := hmem.2.2
    rw [hw] at hpi hpk
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.1 hpi
    obtain ⟨b, hb, hbe⟩ := Finset.mem_image.1 hpk
    rw [Finset.mem_Icc] at ha hb
    have hA : ((N : ℕ) : ℤ) ∣ ((p.1 : ℕ) : ℤ) - a :=
      dvd_of_labelOf_eq N (hae.trans (labelOf_natCast N p.1).symm)
    have hB : ((N : ℕ) : ℤ) ∣ (((p.1 : ℕ) : ℤ) + p.2) - b :=
      dvd_of_labelOf_eq N hbe
    have hd : ((N : ℕ) : ℤ) ∣ p.2 - (b - a) := by
      convert dvd_sub hB hA using 1; ring
    have hlen : p.2 = b - a := by
      have hlt : |p.2 - (b - a)| < ((N : ℕ) : ℤ) := by
        rw [abs_lt]
        constructor <;> omega
      have := Int.eq_zero_of_abs_lt_dvd hd hlt
      omega
    let t := r - (((p.1 : ℕ) : ℤ) - a)
    have ht : -(⌊K ^ γ⌋₊ : ℤ) ≤ t ∧ t + 1 ≤ (⌊K ^ γ⌋₊ : ℤ) := by
      rcases Finset.mem_union.1 hr with hr | hr
      · have := Finset.mem_Ico.1 hr
        dsimp [t]
        constructor <;> omega
      · have := Finset.mem_Ico.1 hr
        dsimp [t]
        constructor <;> omega
    have hl : labelOf N t = labelOf N r :=
      labelOf_eq_of_dvd N (by convert hA using 1; dsimp [t]; ring)
    have hl1 : labelOf N (t + 1) = labelOf N (r + 1) :=
      labelOf_eq_of_dvd N (by convert hA using 1; dsimp [t]; ring)
    rw [nearestPairs, Finset.mem_filter, APG.nextLabel_labelOf, ← hl, ← hl1, hw]
    constructor
    · exact Finset.mem_image_of_mem _ (Finset.mem_Icc.2 ⟨ht.1, by omega⟩)
    · exact Finset.mem_image_of_mem _ (Finset.mem_Icc.2 ⟨by omega, ht.2⟩)
  · rw [window_full hpart]
    simp [nearestPairs]

/-- The gap cutoff depends only on the selected nearest-neighbour edges,
with no enlargement of that set. -/
theorem gapCutoff_congr_of_agree_nearestPairs (s K γ ε : ℝ) (hK : 1 ≤ K) (hγ : 0 ≤ γ)
    (z z' : Fin (N : ℕ) → ℝ)
    (h : ∀ j ∈ nearestPairs N (window N K γ), z j = z' j) :
    gapCutoff N s K γ ε z = gapCutoff N s K γ ε z' := by
  have harc : ∀ p ∈ cutoffPairs N (window N K γ), gapPairDev N z p = gapPairDev N z' p := by
    intro p hp
    have h1 : ∑ r ∈ Ico (((p.1 : ℕ) : ℤ)) (((p.1 : ℕ) : ℤ) + p.2), z (labelOf N r) =
        ∑ r ∈ Ico (((p.1 : ℕ) : ℤ)) (((p.1 : ℕ) : ℤ) + p.2), z' (labelOf N r) :=
      Finset.sum_congr rfl fun r hr => h _ (cutoff_arc_mem_nearestPairs hK hγ hp
        (Finset.mem_union_left _ hr))
    have h2 : ∑ r ∈ Ico (((p.1 : ℕ) : ℤ) + p.2) (((p.1 : ℕ) : ℤ)), z (labelOf N r) =
        ∑ r ∈ Ico (((p.1 : ℕ) : ℤ) + p.2) (((p.1 : ℕ) : ℤ)), z' (labelOf N r) :=
      Finset.sum_congr rfl fun r hr => h _ (cutoff_arc_mem_nearestPairs hK hγ hp
        (Finset.mem_union_right _ hr))
    unfold gapPairDev gapOrientedSum
    rw [h1, h2]
  unfold gapCutoff
  congr 1
  · exact Finset.prod_congr rfl fun p hp => by rw [harc p hp]
  · exact Finset.prod_congr rfl fun i hi => by rw [h i hi]

/-- The cutoff differential has no component outside the selected edges,
including at points where the totalized derivative is zero. -/
theorem fderiv_gapCutoff_single_eq_zero_of_not_mem_nearestPairs (s K γ ε : ℝ)
    (hK : 1 ≤ K) (hγ : 0 ≤ γ) (z : Fin (N : ℕ) → ℝ) {j : Fin (N : ℕ)}
    (hj : j ∉ nearestPairs N (window N K γ)) :
    fderiv ℝ (gapCutoff N s K γ ε) z (Pi.single j (1 : ℝ)) = 0 := by
  apply fderiv_apply_eq_zero_of_const_line z j
  intro t
  apply gapCutoff_congr_of_agree_nearestPairs s K γ ε hK hγ
  intro i hi
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  simp [hij]

end Riesz1

end
