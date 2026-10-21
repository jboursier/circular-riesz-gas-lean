/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.MonotonicityForm

/-!
# Symmetry, positivity and sub-additivity of the anchored inverse energy

This concerns the anchored law `μ*` and the inverse `T*`. The
pairing `⟪v, T* w⟫` is symmetric because the anchored form is symmetric and both sides equal a
form value. The energy `J_{μ*}(v) = ⟪v, T* v⟫` is nonnegative, and the polarization identity
`J(v + w) + J(v - w) = 2 J(v) + 2 J(w)` gives the two-field sub-additivity. The three-field bound
follows by applying the two-field bound twice.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- For the anchored law `μ*` and the inverse `T*`, the
operator `T*` is linear, the pairing `∫ v · T* w dμ*` is symmetric in `v` and `w`, the energy
`J_{μ*}` is nonnegative, and it satisfies the two-field and three-field sub-additivity bounds.
No compatibility condition is needed. -/
theorem anchoredInverse_symmetry_positivity_subadditivity (χ : HsPairPotentials n.succPNat c)
    (hc : 0 < c) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    (∀ (a b : ℝ) (v w : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ)),
      anchoredInverse χ hc (a • v + b • w) =
        a • anchoredInverse χ hc v + b • anchoredInverse χ hc w) ∧
    (∀ v w : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ),
      ∫ y, inner ℝ (v y) (anchoredVectorValues (anchoredMeasureE χ) χ
          (anchoredInverse χ hc w) y) ∂(anchoredMeasureE χ) =
        ∫ y, inner ℝ (w y) (anchoredVectorValues (anchoredMeasureE χ) χ
          (anchoredInverse χ hc v) y) ∂(anchoredMeasureE χ)) ∧
    (∀ v : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ), 0 ≤ anchoredInverseEnergy χ hc v) ∧
    (∀ v w : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ),
      anchoredInverseEnergy χ hc (v + w) ≤
        2 * anchoredInverseEnergy χ hc v + 2 * anchoredInverseEnergy χ hc w) ∧
    (∀ a b d : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ),
      anchoredInverseEnergy χ hc (a + b + d) ≤
        4 * anchoredInverseEnergy χ hc a + 4 * anchoredInverseEnergy χ hc b +
          2 * anchoredInverseEnergy χ hc d) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  -- The energy is the `L²` pairing of a field with its inverse.
  have hJ : ∀ x : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ),
      anchoredInverseEnergy χ hc x =
        inner ℝ x (anchoredVectorValues (anchoredMeasureE χ) χ (anchoredInverse χ hc x)) :=
    fun x => rfl
  have hnonneg : ∀ x : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ),
      0 ≤ anchoredInverseEnergy χ hc x :=
    fun x => anchoredVectorInverseEnergy_nonneg (anchoredMeasureE χ) χ hc
      (ae_mem_anchoredSimplex χ) x
  -- Symmetry: both pairings equal the anchored form of the two inverses, which is symmetric.
  have hsym : ∀ v w : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ),
      inner ℝ v (anchoredVectorValues (anchoredMeasureE χ) χ (anchoredInverse χ hc w)) =
        inner ℝ w (anchoredVectorValues (anchoredMeasureE χ) χ (anchoredInverse χ hc v)) := by
    intro v w
    rw [← anchoredInverse_solves χ hc v (anchoredInverse χ hc w),
      ← anchoredInverse_solves χ hc w (anchoredInverse χ hc v)]
    exact anchoredVectorSobolevForm_comm _ _ _
  -- Expansion of the energy of a sum and of a difference.
  have hexpAdd : ∀ v w : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ),
      anchoredInverseEnergy χ hc (v + w) = anchoredInverseEnergy χ hc v +
        2 * inner ℝ v (anchoredVectorValues (anchoredMeasureE χ) χ (anchoredInverse χ hc w)) +
        anchoredInverseEnergy χ hc w := by
    intro v w
    simp only [hJ, map_add, inner_add_left, inner_add_right]
    rw [hsym w v]
    ring
  have hexpSub : ∀ v w : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ),
      anchoredInverseEnergy χ hc (v - w) = anchoredInverseEnergy χ hc v -
        2 * inner ℝ v (anchoredVectorValues (anchoredMeasureE χ) χ (anchoredInverse χ hc w)) +
        anchoredInverseEnergy χ hc w := by
    intro v w
    simp only [hJ, map_sub, inner_sub_left, inner_sub_right]
    rw [hsym w v]
    ring
  -- Two-field sub-additivity: the two expansions sum to `2 J(v) + 2 J(w)`, and `J(v - w) ≥ 0`.
  have hsub2 : ∀ v w : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ),
      anchoredInverseEnergy χ hc (v + w) ≤
        2 * anchoredInverseEnergy χ hc v + 2 * anchoredInverseEnergy χ hc w := by
    intro v w
    have h1 := hexpAdd v w
    have h2 := hexpSub v w
    have h3 := hnonneg (v - w)
    linarith
  -- Three-field sub-additivity: apply the two-field bound to `(a + b) + d`, then to `a + b`.
  have hsub3 : ∀ a b d : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ),
      anchoredInverseEnergy χ hc (a + b + d) ≤
        4 * anchoredInverseEnergy χ hc a + 4 * anchoredInverseEnergy χ hc b +
          2 * anchoredInverseEnergy χ hc d := by
    intro a b d
    have h1 := hsub2 (a + b) d
    have h2 := hsub2 a b
    linarith
  -- Linearity of `T*` is the linearity of the continuous linear map `anchoredInverse`.
  have hlin : ∀ (a b : ℝ) (v w : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ)),
      anchoredInverse χ hc (a • v + b • w) =
        a • anchoredInverse χ hc v + b • anchoredInverse χ hc w := by
    intro a b v w
    simp only [map_add, map_smul]
  -- Symmetry of the integrals, from the `L²` pairings.
  have hsymInt : ∀ v w : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ),
      ∫ y, inner ℝ (v y) (anchoredVectorValues (anchoredMeasureE χ) χ
          (anchoredInverse χ hc w) y) ∂(anchoredMeasureE χ) =
        ∫ y, inner ℝ (w y) (anchoredVectorValues (anchoredMeasureE χ) χ
          (anchoredInverse χ hc v) y) ∂(anchoredMeasureE χ) := by
    intro v w
    exact (L2.inner_def v (anchoredVectorValues (anchoredMeasureE χ) χ
        (anchoredInverse χ hc w))).symm.trans
      ((hsym v w).trans (L2.inner_def w (anchoredVectorValues (anchoredMeasureE χ) χ
        (anchoredInverse χ hc v))))
  exact ⟨hlin, hsymInt, hnonneg, hsub2, hsub3⟩

end Riesz1

end
