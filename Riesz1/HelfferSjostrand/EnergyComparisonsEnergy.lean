/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.MonotonicityAnchored
public import Riesz1.HelfferSjostrand.AnchoredInverseEnergy

/-!
# Monotonicity of the anchored inverse energy

Lemma 3.5, energy assertion, for the anchored law `μ*`. If two
vector fields satisfy `|v_i| ≤ w_i` almost everywhere for every coordinate `i`, then
`J_{μ*}(v) ≤ J_{μ*}(w)`.

The proof writes the difference `J(w) - J(v)` as the pairing `⟪w + v, T* (w - v)⟫`. This
pairing is nonnegative, since `w + v` and `T* (w - v)` have nonnegative coordinates: the first
by the hypothesis, the second by the coordinatewise monotonicity of `T*` (Lemma 3.4).
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- The `i`-th coordinate of a sum in `L²` is the sum of the coordinates, almost everywhere. -/
theorem anchoredLp_coord_add_ae (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ]
    (x y : Lp (AnchoredEuclidean n) 2 μ) (i : Fin n) :
    ∀ᵐ z ∂μ, (x + y) z i = x z i + y z i := by
  filter_upwards [Lp.coeFn_add x y] with z hz
  rw [hz]
  rfl

/-- The `i`-th coordinate of a difference in `L²` is the difference of the coordinates, almost
everywhere. -/
theorem anchoredLp_coord_sub_ae (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ]
    (x y : Lp (AnchoredEuclidean n) 2 μ) (i : Fin n) :
    ∀ᵐ z ∂μ, (x - y) z i = x z i - y z i := by
  filter_upwards [Lp.coeFn_sub x y] with z hz
  rw [hz]
  rfl

/-- Lemma 3.5, energy assertion. Let `v, w ∈ L²(μ*; ℝ^{N-1})`
satisfy `|v_i| ≤ w_i` almost everywhere for every coordinate `i`. Then
`J_{μ*}(v) ≤ J_{μ*}(w)`. The statement needs no admissibility and no bound `N ≥ 2`. -/
theorem anchoredInverseEnergy_mono_of_abs_le (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (v w : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ))
    (hvw : ∀ i : Fin n, ∀ᵐ y ∂(anchoredMeasureE χ), |v y i| ≤ w y i) :
    anchoredInverseEnergy χ hc v ≤ anchoredInverseEnergy χ hc w := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  -- The energy is the `L²` pairing of a field with its inverse.
  have hJ : ∀ x : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ),
      anchoredInverseEnergy χ hc x =
        inner ℝ x (anchoredVectorValues (anchoredMeasureE χ) χ (anchoredInverse χ hc x)) :=
    fun x => rfl
  -- Symmetry of the mixed pairings, from the integral identity.
  have hsym : inner ℝ v (anchoredVectorValues (anchoredMeasureE χ) χ (anchoredInverse χ hc w)) =
      inner ℝ w (anchoredVectorValues (anchoredMeasureE χ) χ (anchoredInverse χ hc v)) := by
    rw [L2.inner_def, L2.inner_def]
    exact (anchoredInverse_symmetry_positivity_subadditivity χ hc).2.1 v w
  -- The difference `w - v` has nonnegative coordinates.
  have hwv : ∀ i : Fin n, ∀ᵐ y ∂(anchoredMeasureE χ), 0 ≤ (w - v) y i := by
    intro i
    filter_upwards [anchoredLp_coord_sub_ae (anchoredMeasureE χ) w v i, hvw i] with y h1 h2
    rw [h1]
    linarith [le_abs_self (v y i)]
  -- Expansion: `⟪w + v, T* (w - v)⟫ = J(w) - J(v)`, using the symmetry of the mixed pairings.
  have hexp : inner ℝ (w + v)
      (anchoredVectorValues (anchoredMeasureE χ) χ (anchoredInverse χ hc (w - v))) =
        anchoredInverseEnergy χ hc w - anchoredInverseEnergy χ hc v := by
    rw [hJ w, hJ v, map_sub, map_sub]
    simp only [inner_sub_right, inner_add_left]
    rw [hsym]
    ring
  -- Nonnegativity of the pairing, from the coordinates of both factors.
  have hpos : 0 ≤ inner ℝ (w + v)
      (anchoredVectorValues (anchoredMeasureE χ) χ (anchoredInverse χ hc (w - v))) := by
    apply lp_euclidean_inner_nonneg_of_coords
    · intro i
      filter_upwards [anchoredLp_coord_add_ae (anchoredMeasureE χ) w v i, hvw i] with y h1 h2
      rw [h1]
      linarith [neg_abs_le (v y i)]
    · intro i
      have hnn := anchoredInverse_coordinate_nonneg χ hc (w - v) hwv i
      filter_upwards [anchoredVectorValues_coord_ae χ (anchoredMeasureE χ)
        (anchoredInverse χ hc (w - v)) i, hnn] with y h1 h2
      rw [h1]
      exact h2
  linarith [hexp, hpos]

end Riesz1

end
