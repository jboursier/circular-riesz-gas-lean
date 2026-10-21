/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.MonotonicityForm
public import Riesz1.HelfferSjostrand.VectorEnergyTruncation
public import Riesz1.HelfferSjostrand.Coercivity
public import Riesz1.ToMathlib.Hilbert.CoordinateInnerNonneg

/-!
# Monotonicity of the anchored inverse

Lemma 3.4: the anchored inverse `T*` preserves coordinatewise
nonnegativity. The proof tests the weak equation with the negative part `u⁻` of `u = T* v`.
The truncation lemma gives `q_{μ*}(u⁺, u⁻) ≤ 0`, so `q_{μ*}(u⁻, u⁻) ≤ 0`, and coercivity
forces `u⁻ = 0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set InnerProductSpace

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- Lemma 3.4. Let `v ∈ L²(μ*; ℝ^{N-1})` have nonnegative coordinates
almost everywhere, with `N - 1 = n`. Then the solution `u = T* v` of `A_1^{μ*} u = v` has
nonnegative coordinates almost everywhere. -/
theorem anchoredInverse_coordinate_nonneg (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (v : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ))
    (hv : ∀ i : Fin n, ∀ᵐ y ∂(anchoredMeasureE χ), 0 ≤ v y i) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    ∀ i : Fin n, ∀ᵐ y ∂(anchoredMeasureE χ), 0 ≤ vecValue χ i (anchoredInverse χ hc v) y := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  obtain ⟨⟨up, hup⟩, ⟨um, hum⟩, hkey⟩ :=
    anchoredVectorSobolev_truncation χ hc (anchoredInverse χ hc v)
  obtain ⟨hsub, -, hform⟩ := hkey up um hup hum
  obtain ⟨hvalNeg, -⟩ := hum
  -- The coordinates of the negative part are nonnegative, so the pairing with `v` is nonnegative.
  have hum_nonneg : ∀ i : Fin n,
      ∀ᵐ y ∂(anchoredMeasureE χ), 0 ≤ anchoredVectorValues (anchoredMeasureE χ) χ um y i := by
    intro i
    filter_upwards [anchoredVectorValues_coord_ae χ (anchoredMeasureE χ) um i,
      hvalNeg i] with y h1 h2
    rw [h1]
    have h3 : 0 ≤ vecValue χ i um y := by
      rw [h2]
      exact le_max_right _ _
    exact h3
  have hpos : 0 ≤ inner ℝ v (anchoredVectorValues (anchoredMeasureE χ) χ um) :=
    lp_euclidean_inner_nonneg_of_coords v _ hv hum_nonneg
  -- Splitting the form on the difference `u = u⁺ - u⁻`.
  have hsplit : anchoredVectorSobolevForm (anchoredMeasureE χ) (anchoredInverse χ hc v).val um.val =
      anchoredVectorSobolevForm (anchoredMeasureE χ) up.val um.val -
        anchoredVectorSobolevForm (anchoredMeasureE χ) um.val um.val := by
    have hu : (anchoredInverse χ hc v).val = up.val - um.val := by
      rw [← Submodule.coe_sub, hsub]
    rw [hu, anchoredVectorSobolevForm_sub_left]
  -- The weak equation tested with `u⁻`, together with `q(u⁺, u⁻) ≤ 0`, gives `q(u⁻, u⁻) ≤ 0`.
  have hweak := anchoredInverse_solves χ hc v um
  have hq : anchoredVectorSobolevForm (anchoredMeasureE χ) um.val um.val ≤ 0 := by
    linarith
  -- Coercivity turns `q(u⁻, u⁻) ≤ 0` into vanishing values of `u⁻`.
  have hcoer := anchored_vector_coercivity χ hc um
  have hnorm : anchoredInverseValues (anchoredMeasureE χ) um.val = 0 := by
    have hcoef : 0 ≤ (2 * c)⁻¹ := inv_nonneg.mpr (by linarith)
    have hle : (2 * c)⁻¹ * anchoredVectorSobolevForm (anchoredMeasureE χ) um.val um.val ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcoef hq
    have hsq : ‖anchoredInverseValues (anchoredMeasureE χ) um.val‖ ^ 2 = 0 :=
      le_antisymm (le_trans hcoer hle) (sq_nonneg _)
    exact Lp.eq_zero_iff_ae_eq_zero.mpr (by
      filter_upwards [Lp.eq_zero_iff_ae_eq_zero.mp (norm_eq_zero.mp
        ((pow_eq_zero_iff two_ne_zero).mp hsq))] with y hy
      exact hy)
  have hzero : ∀ i : Fin n, ∀ᵐ y ∂(anchoredMeasureE χ),
      anchoredJetValue (anchoredMeasureE χ) i (um : Lp (AnchoredJetPoint n) 2 _) y = 0 := by
    intro i
    filter_upwards [anchoredVectorValues_coord_ae χ (anchoredMeasureE χ) um i,
      Lp.eq_zero_iff_ae_eq_zero.mp hnorm] with y h1 h2
    have hv : anchoredVectorValues (anchoredMeasureE χ) χ um =
        anchoredInverseValues (anchoredMeasureE χ) um.val := rfl
    rw [← h1, hv]
    simpa using congrArg (fun z : AnchoredEuclidean n => z i) h2
  -- The negative part is `max (-u_i, 0)`, so vanishing gives `u_i ≥ 0`.
  intro i
  filter_upwards [hzero i, hvalNeg i] with y h1 h2
  have h4 : max (-(vecValue χ i (anchoredInverse χ hc v) y)) 0 = 0 := by
    rw [← h2]
    exact h1
  linarith [le_max_left (-(vecValue χ i (anchoredInverse χ hc v) y)) 0]

end Riesz1

end
