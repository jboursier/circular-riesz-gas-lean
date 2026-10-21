/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GeometryRelabelIndex
public import Riesz1.HelfferSjostrand.SettingHamiltonian

/-!
# Relabeled pair potentials and the invariance of the pair Hamiltonian

For a cyclic relabeling `T_k` (see `GeometryRelabelIndex`), this file builds the relabeled pair
potentials. For a pair of labels `a < b`, the relabeled potential is `χ_{σa σb}` when the images
keep their order, and `r ↦ χ_{σa σb}(1 - r)` when the relabeling reverses them. Here `σ = hsCycIdx`.
The main result is the pointwise identity `H'(T_k x) = H(x)` for every `x`, where `H` and `H'`
are the pair Hamiltonians of the old and the relabeled potentials.

This is the relabeling assertion in the proof of Lemma 3.6.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Finset
open scoped Topology ContDiff

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

/-- The ordered-pair term: `χ_ij(x_j - x_i)` for `i < j`, symmetric in the labels, and zero on
the diagonal. Summing it over all ordered pairs gives twice the pair sum. -/
def hsPairTerm (χ : HsPairPotentials N c) (x : HsEuclidean N) (i j : Fin (N : ℕ)) : ℝ :=
  if i < j then χ.potential i j (x j - x i)
  else if j < i then χ.potential j i (x i - x j) else 0

theorem hsPairTerm_comm (χ : HsPairPotentials N c) (x : HsEuclidean N) (i j : Fin (N : ℕ)) :
    hsPairTerm χ x j i = hsPairTerm χ x i j := by
  rcases lt_trichotomy i j with h | h | h
  · simp [hsPairTerm, h, not_lt.mpr h.le]
  · subst h
    rfl
  · simp [hsPairTerm, h, not_lt.mpr h.le]

/-- The pair Hamiltonian is the double sum of the ordered-pair terms. -/
theorem hsPairExpression_eq_sum_pairTerm (χ : HsPairPotentials N c) (x : HsEuclidean N) :
    hsPairExpression χ x = ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), hsPairTerm χ x i j := by
  have hsplit : ∀ i j : Fin (N : ℕ), hsPairTerm χ x i j =
      (if i < j then χ.potential i j (x j - x i) else 0) +
        (if j < i then χ.potential j i (x i - x j) else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [hsPairTerm, h, not_lt.mpr h.le]
    · subst h
      simp [hsPairTerm]
    · simp [hsPairTerm, h, not_lt.mpr h.le]
  have hA : ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
      (if j < i then χ.potential j i (x i - x j) else 0) =
      ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
        (if i < j then χ.potential i j (x j - x i) else 0) := by
    rw [Finset.sum_comm]
  have hfilter : hsPairExpression χ x = 2 * ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
      (if i < j then χ.potential i j (x j - x i) else 0) := by
    unfold hsPairExpression
    simp only [Finset.sum_filter]
  rw [hfilter]
  simp only [hsplit, Finset.sum_add_distrib, hA]
  ring

/-! ### Regularity of a pair potential away from the diagonal -/

theorem smooth_of_ne (χ : HsPairPotentials N c) {a b : Fin (N : ℕ)} (hab : a ≠ b) :
    ContDiffOn ℝ ∞ (χ.potential a b) (Ioo 0 1) := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact χ.smooth a b h
  · rw [χ.symmetric a b]
    exact χ.smooth b a h

theorem curvature_of_ne (χ : HsPairPotentials N c) {a b : Fin (N : ℕ)} (hab : a ≠ b)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    c ≤ deriv (deriv (χ.potential a b)) s := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact χ.curvature a b h s hs
  · rw [χ.symmetric a b]
    exact χ.curvature b a h s hs

theorem left_of_ne (χ : HsPairPotentials N c) {a b : Fin (N : ℕ)} (hab : a ≠ b) :
    Tendsto (χ.potential a b) (𝓝[>] 0) atTop := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact χ.leftBoundary a b h
  · rw [χ.symmetric a b]
    exact χ.leftBoundary b a h

theorem right_of_ne (χ : HsPairPotentials N c) {a b : Fin (N : ℕ)} (hab : a ≠ b) :
    Tendsto (χ.potential a b) (𝓝[<] 1) atTop := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact χ.rightBoundary a b h
  · rw [χ.symmetric a b]
    exact χ.rightBoundary b a h

/-! ### Reflection `r ↦ 1 - r` of a potential -/

theorem tendsto_one_sub_nhdsGT_zero :
    Tendsto (fun r : ℝ => 1 - r) (𝓝[>] 0) (𝓝[<] 1) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Tendsto (fun r : ℝ => 1 - r) (𝓝 0) (𝓝 (1 - 0)) :=
      (continuous_const.sub continuous_id).tendsto (0 : ℝ)
    rw [sub_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) < r := hr
    show 1 - r ∈ Set.Iio (1 : ℝ)
    simp only [Set.mem_Iio]
    linarith

theorem tendsto_one_sub_nhdsLT_one :
    Tendsto (fun r : ℝ => 1 - r) (𝓝[<] 1) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Tendsto (fun r : ℝ => 1 - r) (𝓝 1) (𝓝 (1 - 1)) :=
      (continuous_const.sub continuous_id).tendsto (1 : ℝ)
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : r < (1 : ℝ) := hr
    show 1 - r ∈ Set.Ioi (0 : ℝ)
    simp only [Set.mem_Ioi]
    linarith

/-- Second derivative of a reflected potential: `(f(1 - r))'' = f''(1 - r)`. -/
theorem deriv_deriv_one_sub (f : ℝ → ℝ) (hf : ContDiffOn ℝ ∞ f (Ioo 0 1)) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv (fun r => f (1 - r))) s = deriv (deriv f) (1 - s) := by
  have hfd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt f (deriv f t) t := fun t ht =>
    (((hf.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds ht))).hasDerivAt
  have hdd : ContDiffOn ℝ 1 (deriv f) (Ioo 0 1) :=
    hf.deriv_of_isOpen isOpen_Ioo (by simp)
  have hddd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (deriv f) (deriv (deriv f) t) t := fun t ht =>
    (((hdd.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds ht))).hasDerivAt
  have hg : ∀ r ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun r => f (1 - r)) (-deriv f (1 - r)) r := by
    intro r hr
    have hmem : 1 - r ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have hsub : HasDerivAt (fun r : ℝ => 1 - r) (-1) r := by
      simpa using (hasDerivAt_id' r).const_sub 1
    exact ((hfd (1 - r) hmem).comp r hsub).congr_deriv (by ring)
  have hev : deriv (fun r => f (1 - r)) =ᶠ[𝓝 s] fun r => -deriv f (1 - r) :=
    Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) fun r hr =>
      (hg r hr).deriv
  rw [hev.deriv_eq]
  have hmem : 1 - s ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hsub : HasDerivAt (fun r : ℝ => 1 - r) (-1) s := by
    simpa using (hasDerivAt_id' s).const_sub 1
  have hneg : HasDerivAt (fun r => -deriv f (1 - r)) (deriv (deriv f) (1 - s)) s :=
    (((hddd (1 - s) hmem).comp s hsub).neg).congr_deriv (by ring)
  exact hneg.deriv

/-! ### Relabeled potentials -/

/-- The relabeled potential of the pair `(a, b)` before the symmetric extension: the old pair
`(σa, σb)` with its separation kept when the images keep their order, and reflected otherwise. -/
def hsRelabelG (χ : HsPairPotentials N c) (k : ℕ) (a b : Fin (N : ℕ)) (r : ℝ) : ℝ :=
  if hsCycIdx N k a < hsCycIdx N k b then χ.potential (hsCycIdx N k a) (hsCycIdx N k b) r
  else χ.potential (hsCycIdx N k a) (hsCycIdx N k b) (1 - r)

/-- The relabeled pair potential, extended symmetrically in the labels. -/
def hsRelabelPotential (χ : HsPairPotentials N c) (k : ℕ) (i j : Fin (N : ℕ)) : ℝ → ℝ :=
  if i ≤ j then hsRelabelG χ k i j else hsRelabelG χ k j i

theorem hsRelabelPotential_symm (χ : HsPairPotentials N c) (k : ℕ) (i j : Fin (N : ℕ)) :
    hsRelabelPotential χ k i j = hsRelabelPotential χ k j i := by
  rcases lt_trichotomy i j with h | h | h
  · simp [hsRelabelPotential, h.le, not_le.mpr h]
  · subst h
    rfl
  · simp [hsRelabelPotential, h.le, not_le.mpr h]

/-- Away from the diagonal the relabeled potential is one of the two old potentials. -/
theorem hsRelabelPotential_eq_of_lt (χ : HsPairPotentials N c) (k : ℕ) {i j : Fin (N : ℕ)}
    (hij : i < j) : hsRelabelPotential χ k i j = hsRelabelG χ k i j := by
  simp [hsRelabelPotential, hij.le]

theorem hsCycIdx_ne (N : ℕ+) (k : ℕ) {i j : Fin (N : ℕ)} (hij : i < j) :
    hsCycIdx N k i ≠ hsCycIdx N k j :=
  fun h => hij.ne (hsCycIdx_injective N k h)

theorem hsRelabelG_smooth (χ : HsPairPotentials N c) (k : ℕ) {i j : Fin (N : ℕ)}
    (hij : i < j) : ContDiffOn ℝ ∞ (hsRelabelG χ k i j) (Ioo 0 1) := by
  have hne := hsCycIdx_ne N k hij
  by_cases hlt : hsCycIdx N k i < hsCycIdx N k j
  · have heq : hsRelabelG χ k i j = χ.potential (hsCycIdx N k i) (hsCycIdx N k j) := by
      funext r
      simp [hsRelabelG, hlt]
    rw [heq]
    exact smooth_of_ne χ hne
  · have heq : hsRelabelG χ k i j =
        fun r => χ.potential (hsCycIdx N k i) (hsCycIdx N k j) (1 - r) := by
      funext r
      simp [hsRelabelG, hlt]
    rw [heq]
    refine (smooth_of_ne χ hne).comp ((contDiff_const.sub contDiff_id).contDiffOn) ?_
    exact fun r hr => ⟨by linarith [hr.2], by linarith [hr.1]⟩

theorem hsRelabelG_curvature (χ : HsPairPotentials N c) (k : ℕ) {i j : Fin (N : ℕ)}
    (hij : i < j) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    c ≤ deriv (deriv (hsRelabelG χ k i j)) r := by
  have hne := hsCycIdx_ne N k hij
  by_cases hlt : hsCycIdx N k i < hsCycIdx N k j
  · have heq : hsRelabelG χ k i j = χ.potential (hsCycIdx N k i) (hsCycIdx N k j) := by
      funext s
      simp [hsRelabelG, hlt]
    rw [heq]
    exact curvature_of_ne χ hne hr
  · have heq : hsRelabelG χ k i j =
        fun s => χ.potential (hsCycIdx N k i) (hsCycIdx N k j) (1 - s) := by
      funext s
      simp [hsRelabelG, hlt]
    rw [heq, deriv_deriv_one_sub _ (smooth_of_ne χ hne) hr]
    have hmem : 1 - r ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    exact curvature_of_ne χ hne hmem

theorem hsRelabelG_left (χ : HsPairPotentials N c) (k : ℕ) {i j : Fin (N : ℕ)}
    (hij : i < j) : Tendsto (hsRelabelG χ k i j) (𝓝[>] 0) atTop := by
  have hne := hsCycIdx_ne N k hij
  by_cases hlt : hsCycIdx N k i < hsCycIdx N k j
  · have heq : hsRelabelG χ k i j = χ.potential (hsCycIdx N k i) (hsCycIdx N k j) := by
      funext r
      simp [hsRelabelG, hlt]
    rw [heq]
    exact left_of_ne χ hne
  · have heq : hsRelabelG χ k i j =
        fun r => χ.potential (hsCycIdx N k i) (hsCycIdx N k j) (1 - r) := by
      funext r
      simp [hsRelabelG, hlt]
    rw [heq]
    exact (right_of_ne χ hne).comp tendsto_one_sub_nhdsGT_zero

theorem hsRelabelG_right (χ : HsPairPotentials N c) (k : ℕ) {i j : Fin (N : ℕ)}
    (hij : i < j) : Tendsto (hsRelabelG χ k i j) (𝓝[<] 1) atTop := by
  have hne := hsCycIdx_ne N k hij
  by_cases hlt : hsCycIdx N k i < hsCycIdx N k j
  · have heq : hsRelabelG χ k i j = χ.potential (hsCycIdx N k i) (hsCycIdx N k j) := by
      funext r
      simp [hsRelabelG, hlt]
    rw [heq]
    exact right_of_ne χ hne
  · have heq : hsRelabelG χ k i j =
        fun r => χ.potential (hsCycIdx N k i) (hsCycIdx N k j) (1 - r) := by
      funext r
      simp [hsRelabelG, hlt]
    rw [heq]
    exact (left_of_ne χ hne).comp tendsto_one_sub_nhdsLT_one

/-- The relabeled pair potentials, as an element of the setting's `HsPairPotentials`. -/
def hsRelabelPairs (χ : HsPairPotentials N c) (k : ℕ) : HsPairPotentials N c where
  potential := hsRelabelPotential χ k
  symmetric := hsRelabelPotential_symm χ k
  smooth := fun i j hij => by
    rw [hsRelabelPotential_eq_of_lt χ k hij]
    exact hsRelabelG_smooth χ k hij
  curvature := fun i j hij r hr => by
    rw [hsRelabelPotential_eq_of_lt χ k hij]
    exact hsRelabelG_curvature χ k hij hr
  leftBoundary := fun i j hij => by
    rw [hsRelabelPotential_eq_of_lt χ k hij]
    exact hsRelabelG_left χ k hij
  rightBoundary := fun i j hij => by
    rw [hsRelabelPotential_eq_of_lt χ k hij]
    exact hsRelabelG_right χ k hij

/-! ### The pair identity -/

/-- For `i < j`, the relabeled ordered-pair term is the old term of the images `(σi, σj)`. -/
theorem hsPairTerm_relabel_lt (χ : HsPairPotentials N c) (k : ℕ) (x : HsEuclidean N)
    {i j : Fin (N : ℕ)} (hij : i < j) :
    hsPairTerm (hsRelabelPairs χ k) (hsRelabel N k x) i j =
      hsPairTerm χ x (hsCycIdx N k i) (hsCycIdx N k j) := by
  unfold hsPairTerm
  simp only [hij, ↓reduceIte]
  show hsRelabelPotential χ k i j (hsRelabel N k x j - hsRelabel N k x i) = _
  rw [hsRelabelPotential_eq_of_lt χ k hij]
  rcases hsCycShift_sub_cases N k hij with ⟨hs, hord⟩ | ⟨hs, hord⟩
  · have hsep : hsRelabel N k x j - hsRelabel N k x i =
        x (hsCycIdx N k j) - x (hsCycIdx N k i) := by
      rw [hsRelabel_apply, hsRelabel_apply, hs]
      ring
    rw [hsep]
    simp only [hsRelabelG, hord, ↓reduceIte]
  · have hsep : hsRelabel N k x j - hsRelabel N k x i =
        x (hsCycIdx N k j) - x (hsCycIdx N k i) + 1 := by
      rw [hsRelabel_apply, hsRelabel_apply, hs]
      push_cast
      ring
    have hnlt : ¬ hsCycIdx N k i < hsCycIdx N k j := not_lt.mpr hord.le
    rw [hsep]
    simp only [hsRelabelG, hnlt, hord, ↓reduceIte]
    rw [χ.symmetric (hsCycIdx N k i) (hsCycIdx N k j)]
    congr 1
    ring

/-- The pointwise identity for every ordered pair of labels. -/
theorem hsPairTerm_relabel (χ : HsPairPotentials N c) (k : ℕ) (x : HsEuclidean N)
    (i j : Fin (N : ℕ)) :
    hsPairTerm (hsRelabelPairs χ k) (hsRelabel N k x) i j =
      hsPairTerm χ x (hsCycIdx N k i) (hsCycIdx N k j) := by
  rcases lt_trichotomy i j with h | h | h
  · exact hsPairTerm_relabel_lt χ k x h
  · subst h
    simp [hsPairTerm]
  · rw [hsPairTerm_comm (hsRelabelPairs χ k) (hsRelabel N k x) j i,
      hsPairTerm_relabel_lt χ k x h, hsPairTerm_comm χ x (hsCycIdx N k i) (hsCycIdx N k j)]

/-- The relabeled pair Hamiltonian is the old one, pointwise on the whole lift space:
`H'(T_k x) = H(x)`. -/
theorem hsPairExpression_relabel (χ : HsPairPotentials N c) (k : ℕ) (x : HsEuclidean N) :
    hsPairExpression (hsRelabelPairs χ k) (hsRelabel N k x) = hsPairExpression χ x := by
  have hσ := hsCycIdx_bijective N k
  rw [hsPairExpression_eq_sum_pairTerm, hsPairExpression_eq_sum_pairTerm]
  simp only [hsPairTerm_relabel]
  have inner : ∀ i : Fin (N : ℕ),
      ∑ j : Fin (N : ℕ), hsPairTerm χ x (hsCycIdx N k i) (hsCycIdx N k j) =
        ∑ j : Fin (N : ℕ), hsPairTerm χ x (hsCycIdx N k i) j := fun i =>
    hσ.sum_comp (fun b => hsPairTerm χ x (hsCycIdx N k i) b)
  simp only [inner]
  exact hσ.sum_comp (fun a => ∑ b : Fin (N : ℕ), hsPairTerm χ x a b)

end Riesz1

end
