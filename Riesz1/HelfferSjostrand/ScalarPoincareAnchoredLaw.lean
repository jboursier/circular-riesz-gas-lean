/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.ScalarPoincareAnchored
public import Riesz1.HelfferSjostrand.AnchoredLawSobolev
public import Riesz1.ToMathlib.Poincare.Isometry

/-!
# Scalar Poincaré for the anchored pushforward law

The anchored clause of the scalar Poincaré inequality, on the anchored law and
its Sobolev space.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

theorem scalarPoincareAnchorDomain_eq (n : ℕ) :
    scalarPoincareAnchorDomain n = anchoredSimplex n := by
  ext y
  rw [scalarPoincareAnchorDomain_iff]
  change (StrictMono y ∧ ∀ i, 0 < y i ∧ y i < 1) ↔
    (∀ i, 0 < y i ∧ y i < 1) ∧ StrictMono y
  exact and_comm

theorem scalarPoincareAnchorPotential_eq {n : ℕ} {c : ℝ}
    (χ : HsPairPotentials n.succPNat c) :
    scalarPoincareAnchorPotential χ = hsAnchoredHamiltonianE χ := by
  funext y
  unfold scalarPoincareAnchorPotential hsAnchoredHamiltonianE hsAnchoredHamiltonian
  congr 1

/-- The Euclidean realization of the anchored pushforward is the normalized
exponential density used in the anchored Poincaré theorem. -/
theorem anchoredMeasureE_eq_poincare_tilted {n : ℕ} {c : ℝ}
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    anchoredMeasureE χ = (volume.restrict (scalarPoincareAnchorDomain n)).tilted
      (fun y => -scalarPoincareAnchorPotential χ y) := by
  let e := (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm.toMeasurableEquiv
  let ρ := (volume.restrict (scalarPoincareAnchorDomain n)).withDensity
    (fun y => ENNReal.ofReal (Real.exp (-scalarPoincareAnchorPotential χ y)))
  have hbase : (volume.restrict (anchoredDomain n)).map e =
      volume.restrict (scalarPoincareAnchorDomain n) := by
    rw [scalarPoincareAnchorDomain_eq]
    exact ((PiLp.volume_preserving_toLp (Fin n)).restrict_preimage
      (measurableSet_anchoredSimplex n)).map_eq
  have hW : (hsAnchoredWeight χ).map e = ρ := by
    have hden : hsAnchoredDensity χ = fun y =>
        ENNReal.ofReal (Real.exp (-scalarPoincareAnchorPotential χ (e y))) := by
      funext y
      rw [scalarPoincareAnchorPotential_eq]
      rfl
    unfold hsAnchoredWeight
    rw [hden]
    change ((volume.restrict (anchoredDomain n)).withDensity _).map e = _
    rw [show ρ = ((volume.restrict (anchoredDomain n)).map e).withDensity
      (fun y => ENNReal.ofReal (Real.exp (-scalarPoincareAnchorPotential χ y))) by
        rw [hbase]]
    ext s hs
    rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
      withDensity_apply _ hs, ← lintegral_indicator (e.measurable hs),
      ← lintegral_indicator hs, lintegral_map_equiv]
    exact lintegral_congr fun y => by
      by_cases hy : e y ∈ s <;> simp [hy]
  have hmass : hsAnchoredWeight χ univ = ρ univ := by
    rw [← hW, Measure.map_apply e.measurable MeasurableSet.univ, preimage_univ]
  have hfinite : ρ univ ≠ ⊤ := by
    rw [← hmass, ← hsPartitionFunction_eq_hsAnchoredWeight]
    exact (hsPartitionFunction_lt_top χ hc).ne
  have hpositive : ρ univ ≠ 0 := by
    rw [← hmass, ← hsPartitionFunction_eq_hsAnchoredWeight]
    exact (hsPartitionFunction_pos χ).ne'
  have hρ : ρ univ = ∫⁻ y in scalarPoincareAnchorDomain n,
      ENNReal.ofReal (Real.exp (-scalarPoincareAnchorPotential χ y)) := by
    dsimp only [ρ]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hi : IntegrableOn (fun y => Real.exp (-scalarPoincareAnchorPotential χ y))
      (scalarPoincareAnchorDomain n) :=
    (lintegral_ofReal_ne_top_iff_integrable
      ((Real.continuous_exp.comp_continuousOn
        (contDiffOn_scalarPoincareAnchorPotential χ).continuousOn.neg).aestronglyMeasurable
          (isOpen_scalarPoincareAnchorDomain n).measurableSet)
      (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)).mp (hρ ▸ hfinite)
  have hp : 0 < ∫ y in scalarPoincareAnchorDomain n,
      Real.exp (-scalarPoincareAnchorPotential χ y) := by
    have he := ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)
    rw [← hρ] at he
    exact ENNReal.ofReal_pos.mp (he.symm ▸ bot_lt_iff_ne_bot.mpr hpositive)
  rw [poincare_tilted_eq_normalized _ _ hi hp]
  change ((hsAnchoredWeight χ univ)⁻¹ • hsAnchoredWeight χ).map e = _
  rw [Measure.map_smul _ e.measurable.aemeasurable, hW, hmass, ← hρ]

/-- **Scalar Poincaré, anchored law**. Only pair convexity
is needed, so the boundary-growth condition can be dropped. -/
theorem scalar_poincare_anchoredLaw (hPL : External.PrekopaLeindler)
    {n : ℕ} (hn : 0 < n) {c : ℝ} (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {F : AnchoredEuclidean n → ℝ} {G : AnchoredEuclidean n → AnchoredEuclidean n}
    (hFG : IsAnchoredH1 χ F G) :
    (∫ y, (F y - ∫ z, F z ∂anchoredMeasureE χ) ^ 2 ∂anchoredMeasureE χ) ≤
      (2 * c)⁻¹ * ∫ y, ‖G y‖ ^ 2 ∂anchoredMeasureE χ := by
  have h := scalar_poincare_anchored hPL hn χ hc (F := F) (G := G)
  rw [IsAnchoredH1, ← scalarPoincareAnchorDomain_eq,
    anchoredMeasureE_eq_poincare_tilted χ hc] at hFG
  simpa only [anchoredMeasureE_eq_poincare_tilted χ hc] using h hFG

end Riesz1

end
