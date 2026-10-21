/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodGradientBound

/-!
# Euclidean gradient bound for the gap-coordinate cutoff

Last claim of the good event estimate in Lemma 5.2: `|∇η̃| ≤ C K^A` almost everywhere, for the
Euclidean norm of the gradient of the gap-coordinate cutoff `η̃ = gapCutoff`. The part-1 bound
`Riesz1.gapCutoff_ae_fderiv_bound` controls each coordinate partial derivative by `76 K^{2γ+ε}`.
To pass to the Euclidean norm, the number of coordinates on which the cutoff depends must be
bounded. This file shows that it is at most `72 (K^γ)^2`, uniformly in `N`.

* `gapSupport N K γ`: the labels whose gap enters the cutoff. Each such label is `labelOf N (a + u)`
  for a window label `a` and `|u| ≤ ⌊4 K^γ⌋₊`.
* `card_gapSupport_le`: `#gapSupport ≤ 72 (K^γ)^2`.
* `gapCutoff_congr_of_agree`: the cutoff depends only on the gap coordinates in `gapSupport`.
* `fderiv_gapCutoff_single_eq_zero_of_not_mem`: the partial derivative in a coordinate outside
  `gapSupport` vanishes everywhere.
* `gapCutoff_ae_euclidean_bound`: `√(∑_j (∂_j η̃)^2) ≤ 684 K^{3γ+ε}` almost everywhere.
-/

@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace Riesz1

variable {N : ℕ+}

/-! ### The labels that the cutoff depends on -/

/-- The labels whose gaps enter the gap-coordinate cutoff: the window labels, and the labels of
the arcs of the pairs of `cutoffPairs`. Each such label is `labelOf N (a + u)` for a window label
`a` and an integer `u` with `|u| ≤ ⌊4 K^γ⌋₊`. -/
def gapSupport (N : ℕ+) (K γ : ℝ) : Finset (Fin (N : ℕ)) :=
  (window N K γ ×ˢ Icc (-((⌊4 * K ^ γ⌋₊ : ℕ) : ℤ)) ((⌊4 * K ^ γ⌋₊ : ℕ) : ℤ)).image
    fun q => labelOf N (((q.1 : ℕ) : ℤ) + q.2)

/-- A window label lies in `gapSupport`. -/
theorem mem_gapSupport_of_mem_window {K γ : ℝ} {i : Fin (N : ℕ)} (hi : i ∈ window N K γ) :
    i ∈ gapSupport N K γ := by
  unfold gapSupport
  rw [Finset.mem_image]
  refine ⟨(i, 0), Finset.mem_product.2 ⟨hi, ?_⟩, ?_⟩
  · rw [Finset.mem_Icc]
    constructor <;> omega
  · show labelOf N (((i : ℕ) : ℤ) + 0) = i
    rw [add_zero]
    exact labelOf_natCast N i

/-- The label of every arc of a pair of `cutoffPairs` lies in `gapSupport`. -/
theorem arc_label_mem_gapSupport {K γ : ℝ} (hK : 1 ≤ K) (hγ : 0 ≤ γ) {p : Fin (N : ℕ) × ℤ}
    (hp : p ∈ cutoffPairs N (window N K γ)) {r : ℤ}
    (hr : r ∈ Ico (((p.1 : ℕ) : ℤ)) (((p.1 : ℕ) : ℤ) + p.2) ∪
      Ico (((p.1 : ℕ) : ℤ) + p.2) (((p.1 : ℕ) : ℤ))) :
    labelOf N r ∈ gapSupport N K γ := by
  have hm := gradient_pair_bound hK hγ N p hp
  have hu : -((⌊4 * K ^ γ⌋₊ : ℕ) : ℤ) ≤ r - ((p.1 : ℕ) : ℤ) ∧
      r - ((p.1 : ℕ) : ℤ) ≤ ((⌊4 * K ^ γ⌋₊ : ℕ) : ℤ) := by
    rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico] at hr
    omega
  have hp1 : p.1 ∈ window N K γ := (Finset.mem_filter.1 hp).2.1
  unfold gapSupport
  rw [Finset.mem_image]
  refine ⟨(p.1, r - ((p.1 : ℕ) : ℤ)), Finset.mem_product.2 ⟨hp1, Finset.mem_Icc.2 hu⟩, ?_⟩
  show labelOf N (((p.1 : ℕ) : ℤ) + (r - ((p.1 : ℕ) : ℤ))) = labelOf N r
  rw [show ((p.1 : ℕ) : ℤ) + (r - ((p.1 : ℕ) : ℤ)) = r by ring]

/-- The nearest-neighbour labels of the window lie in `gapSupport`. -/
theorem nearestPairs_mem_gapSupport {K γ : ℝ} {i : Fin (N : ℕ)}
    (hi : i ∈ nearestPairs N (window N K γ)) : i ∈ gapSupport N K γ :=
  mem_gapSupport_of_mem_window (Finset.mem_filter.1 hi).1

/-! ### Counting -/

/-- The window has at most `8 K^γ` labels, for `K ≥ 1` and `γ ≥ 0`. -/
theorem card_window_le_real {K γ : ℝ} (hK : 1 ≤ K) (hγ : 0 ≤ γ) :
    ((window N K γ).card : ℝ) ≤ 8 * K ^ γ := by
  have hKγ : 1 ≤ K ^ γ := Real.one_le_rpow hK hγ
  by_cases h : K ^ γ < ((N : ℕ) : ℝ) / 8
  · have hw : window N K γ = windowLabels N (K ^ γ / ((N : ℕ) : ℝ)) := by
      unfold window
      rw [windowTime_of_lt h]
    have ht : ((N : ℕ) : ℝ) * (K ^ γ / ((N : ℕ) : ℝ)) = K ^ γ := by
      field_simp
    have hcard := card_windowLabels_le N (K ^ γ / ((N : ℕ) : ℝ))
    rw [ht] at hcard
    have hfl : (⌊K ^ γ⌋₊ : ℝ) ≤ K ^ γ := Nat.floor_le (by linarith)
    have h1 : (window N K γ).card ≤ 2 * ⌊K ^ γ⌋₊ + 1 := by
      rw [hw]
      exact hcard
    have h2 : ((window N K γ).card : ℝ) ≤ 2 * (⌊K ^ γ⌋₊ : ℝ) + 1 := by
      exact_mod_cast h1
    linarith
  · have hw : window N K γ = univ := window_full h
    have hfull : (N : ℕ) ≤ 8 * K ^ γ := by
      have h' : ((N : ℕ) : ℝ) / 8 ≤ K ^ γ := not_lt.1 h
      linarith
    have hcard : (window N K γ).card ≤ (N : ℕ) := by
      rw [hw]
      simp
    have hcardR : ((window N K γ).card : ℝ) ≤ ((N : ℕ) : ℝ) := by
      exact_mod_cast hcard
    linarith

/-- The support of the gap-coordinate cutoff has at most `72 (K^γ)^2` labels, for `K ≥ 1` and
`γ ≥ 0`, uniformly in `N`. -/
theorem card_gapSupport_le {K γ : ℝ} (hK : 1 ≤ K) (hγ : 0 ≤ γ) :
    ((gapSupport N K γ).card : ℝ) ≤ 72 * (K ^ γ) ^ 2 := by
  have hKγ : 1 ≤ K ^ γ := Real.one_le_rpow hK hγ
  set m : ℕ := ⌊4 * K ^ γ⌋₊ with hmdef
  have hc1 : (gapSupport N K γ).card ≤ (window N K γ).card * (2 * m + 1) := by
    unfold gapSupport
    refine card_image_le.trans ?_
    rw [card_product, Int.card_Icc]
    have e : ((m : ℤ) + 1 - -(m : ℤ)).toNat = 2 * m + 1 := by omega
    rw [e]
  have hm : (m : ℝ) ≤ 4 * K ^ γ := Nat.floor_le (by linarith)
  have hc2 : ((gapSupport N K γ).card : ℝ) ≤ ((window N K γ).card : ℝ) * (2 * (m : ℝ) + 1) := by
    exact_mod_cast hc1
  have hw := card_window_le_real (N := N) hK hγ
  have hW0 : (0 : ℝ) ≤ ((window N K γ).card : ℝ) := Nat.cast_nonneg _
  calc ((gapSupport N K γ).card : ℝ)
      ≤ ((window N K γ).card : ℝ) * (2 * (m : ℝ) + 1) := hc2
    _ ≤ (8 * K ^ γ) * (9 * K ^ γ) := by
        refine mul_le_mul hw (by linarith) (by positivity) (by positivity)
    _ = 72 * (K ^ γ) ^ 2 := by ring

/-! ### Dependence only on the support -/

/-- The gap-coordinate cutoff depends only on the gap coordinates in `gapSupport`: two gap vectors
that agree on `gapSupport` have the same cutoff. -/
theorem gapCutoff_congr_of_agree (s K γ ε : ℝ) (hK : 1 ≤ K) (hγ : 0 ≤ γ)
    (z z' : Fin (N : ℕ) → ℝ) (h : ∀ j ∈ gapSupport N K γ, z j = z' j) :
    gapCutoff N s K γ ε z = gapCutoff N s K γ ε z' := by
  have harc : ∀ p ∈ cutoffPairs N (window N K γ), gapPairDev N z p = gapPairDev N z' p := by
    intro p hp
    have h1 : ∑ r ∈ Ico (((p.1 : ℕ) : ℤ)) (((p.1 : ℕ) : ℤ) + p.2), z (labelOf N r) =
        ∑ r ∈ Ico (((p.1 : ℕ) : ℤ)) (((p.1 : ℕ) : ℤ) + p.2), z' (labelOf N r) :=
      Finset.sum_congr rfl fun r hr => h _ (arc_label_mem_gapSupport hK hγ hp
        (Finset.mem_union_left _ hr))
    have h2 : ∑ r ∈ Ico (((p.1 : ℕ) : ℤ) + p.2) (((p.1 : ℕ) : ℤ)), z (labelOf N r) =
        ∑ r ∈ Ico (((p.1 : ℕ) : ℤ) + p.2) (((p.1 : ℕ) : ℤ)), z' (labelOf N r) :=
      Finset.sum_congr rfl fun r hr => h _ (arc_label_mem_gapSupport hK hγ hp
        (Finset.mem_union_right _ hr))
    unfold gapPairDev gapOrientedSum
    rw [h1, h2]
  unfold gapCutoff
  congr 1
  · exact Finset.prod_congr rfl fun p hp => by rw [harc p hp]
  · exact Finset.prod_congr rfl fun i hi => by
      rw [h i (nearestPairs_mem_gapSupport hi)]

/-- The derivative of a function along a direction in which it does not change is zero. -/
theorem fderiv_apply_eq_zero_of_const_line {f : (Fin (N : ℕ) → ℝ) → ℝ} (z : Fin (N : ℕ) → ℝ)
    (j : Fin (N : ℕ)) (h : ∀ t : ℝ, f (z + t • (Pi.single j (1 : ℝ) : Fin (N : ℕ) → ℝ)) = f z) :
    fderiv ℝ f z (Pi.single j (1 : ℝ)) = 0 := by
  by_cases hd : DifferentiableAt ℝ f z
  · have hline : HasDerivAt (fun t : ℝ => z + t • (Pi.single j (1 : ℝ) : Fin (N : ℕ) → ℝ))
        (Pi.single j (1 : ℝ)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
        (Pi.single j (1 : ℝ) : Fin (N : ℕ) → ℝ)).const_add z
    have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hd.hasFDerivAt hline (by simp)
    have hconst : (f ∘ fun t : ℝ => z + t • (Pi.single j (1 : ℝ) : Fin (N : ℕ) → ℝ)) =
        fun _ => f z := funext fun t => h t
    rw [hconst] at hcomp
    exact hcomp.unique (hasDerivAt_const (0 : ℝ) (f z))
  · simp [fderiv_zero_of_not_differentiableAt hd]

/-- The partial derivative of the gap-coordinate cutoff in a coordinate outside `gapSupport` is
zero at every gap vector. -/
theorem fderiv_gapCutoff_single_eq_zero_of_not_mem (s K γ ε : ℝ) (hK : 1 ≤ K) (hγ : 0 ≤ γ)
    (z : Fin (N : ℕ) → ℝ) {j : Fin (N : ℕ)} (hj : j ∉ gapSupport N K γ) :
    fderiv ℝ (gapCutoff N s K γ ε) z (Pi.single j (1 : ℝ)) = 0 := by
  apply fderiv_apply_eq_zero_of_const_line z j
  intro t
  apply gapCutoff_congr_of_agree s K γ ε hK hγ
  intro i hi
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  simp [hij]

/-! ### The Euclidean bound -/

/-- A sum of squares of numbers bounded by `M`, supported on a finite set `T`, is at most
`#T M^2`. -/
theorem sum_sq_le_card_mul_of_support {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Finset ι)
    (g : ι → ℝ) (M : ℝ) (hT : ∀ j ∉ T, g j = 0) (hg : ∀ j, |g j| ≤ M) :
    ∑ j, g j ^ 2 ≤ (T.card : ℝ) * M ^ 2 := by
  rw [← Finset.sum_subset (Finset.subset_univ T) (fun j _ hj => by simp [hT j hj])]
  have hM : ∀ j, g j ^ 2 ≤ M ^ 2 := fun j => by
    have h0 : 0 ≤ M := (abs_nonneg _).trans (hg j)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hg j) 2
  calc ∑ j ∈ T, g j ^ 2 ≤ ∑ _j ∈ T, M ^ 2 := Finset.sum_le_sum fun j _ => hM j
    _ = (T.card : ℝ) * M ^ 2 := by simp

/-- **Euclidean gradient bound.** Let `K ≥ 1`, `γ ≥ 0`, `s ≥ 0` and `ε ≥ 0`. For every `N`, the
Euclidean norm of the gradient of the gap-coordinate cutoff is at most `684 K^{3γ+ε}`, for almost
every gap vector. The norm is `√(∑_j (∂_j η̃)^2)` with `∂_j η̃ = fderiv η̃ e_j`. -/
theorem gapCutoff_ae_euclidean_bound (s K γ ε : ℝ) (hK1 : 1 ≤ K) (hγ : 0 ≤ γ) (hs : 0 ≤ s)
    (hε : 0 ≤ ε) :
    ∀ᵐ z ∂(volume : Measure (Fin (N : ℕ) → ℝ)),
      Real.sqrt (∑ j : Fin (N : ℕ),
          (fderiv ℝ (gapCutoff N s K γ ε) z (Pi.single j (1 : ℝ))) ^ 2)
        ≤ 684 * K ^ (3 * γ + ε) := by
  filter_upwards [ae_all_iff.2 fun j => gapCutoff_ae_fderiv_bound s K γ ε hK1 hγ hs hε j]
    with z hz
  have hK0 : 0 < K := by linarith
  have hsum := sum_sq_le_card_mul_of_support (gapSupport N K γ)
    (fun j : Fin (N : ℕ) => fderiv ℝ (gapCutoff N s K γ ε) z (Pi.single j (1 : ℝ)))
    (76 * K ^ (2 * γ + ε))
    (fun j hj => fderiv_gapCutoff_single_eq_zero_of_not_mem s K γ ε hK1 hγ z hj) hz
  have hcard := card_gapSupport_le (N := N) hK1 hγ
  have hQ : K ^ γ * K ^ (2 * γ + ε) = K ^ (3 * γ + ε) := by
    rw [← Real.rpow_add hK0]
    ring_nf
  have hpos : 0 ≤ K ^ (3 * γ + ε) := by positivity
  rw [Real.sqrt_le_left (by positivity)]
  calc ∑ j : Fin (N : ℕ), (fderiv ℝ (gapCutoff N s K γ ε) z (Pi.single j (1 : ℝ))) ^ 2
      ≤ ((gapSupport N K γ).card : ℝ) * (76 * K ^ (2 * γ + ε)) ^ 2 := hsum
    _ ≤ (72 * (K ^ γ) ^ 2) * (76 * K ^ (2 * γ + ε)) ^ 2 :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 415872 * ((K ^ γ) ^ 2 * (K ^ (2 * γ + ε)) ^ 2) := by ring
    _ ≤ 467856 * ((K ^ γ) ^ 2 * (K ^ (2 * γ + ε)) ^ 2) := by
        have : 0 ≤ (K ^ γ) ^ 2 * (K ^ (2 * γ + ε)) ^ 2 := by positivity
        linarith
    _ = (684 * K ^ (3 * γ + ε)) ^ 2 := by
        rw [← hQ]
        ring

end Riesz1

end
end
