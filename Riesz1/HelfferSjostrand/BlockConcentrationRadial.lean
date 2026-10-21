/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BlockConcentrationCurvature
public import Riesz1.HelfferSjostrand.BlockConcentrationHerbst
public import Riesz1.HelfferSjostrand.ConvexityExterior
public import Riesz1.HelfferSjostrand.ScalarPoincareRadial
public import Riesz1.ToMathlib.ConvexHessian

/-!
# Concentration for the radial block law

The potential `H₁ + H̃` of Lemma 3.9, in orthonormal coordinates on the
zero-sum hyperplane, has a convex residual after subtracting `c₁ m ‖z‖² / 2`.
The internal radial concentration theorem applies to every weighted `H¹` observable of this
law. It does not assert the missing Sobolev descent from a circular marginal.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

variable {N M : ℕ+} {c c₁ : ℝ} {n : ℕ}

/-- The retained marginal potential in orthonormal coordinates on the zero-sum hyperplane. -/
def blockRadialPotential (χ : HsPairPotentials N c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (basis : OrthonormalBasis (Fin (Module.finrank ℝ (hsOrthSubspace M))) ℝ (hsOrthSubspace M))
    (q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace M)))) : ℝ :=
  blockRetainedEnergy χ e (scalarPoincareRadialEmbedding basis q) +
    blockTilde χ e (scalarPoincareRadialEmbedding basis q)

/-- The convexity statement needed for Gaussian conditioning in Lemma 3.9. The pair
curvature hypothesis is made only on actual full configurations. -/
theorem convexOn_blockRadialResidual (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩)
    (basis : OrthonormalBasis (Fin (Module.finrank ℝ (hsOrthSubspace M))) ℝ (hsOrthSubspace M))
    (hcurv : ∀ x ∈ hsChamber N, ∀ i j : Fin (M : ℕ), i < j → c₁ / 2 ≤
      deriv (deriv (χ.potential (e (Sum.inl i)) (e (Sum.inl j)))) (x (e (Sum.inl j)) - x (e (Sum.inl i)))) :
    ConvexOn ℝ (scalarPoincareRadialDomain basis)
      (fun q => blockRadialPotential χ e basis q - (c₁ * M) / 2 * ‖q‖ ^ 2) := by
  let ψ := blockPairPotentials χ e hmono
  have hH : ∀ q ∈ scalarPoincareRadialDomain basis, ∀ a,
      (c₁ * M) * ‖a‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ (scalarPoincareRadialPotential basis ψ)) q a a := by
    intro q hq a
    rw [hessian_scalarPoincareRadialPotential basis ψ hq]
    have hz : scalarPoincareRadialEmbedding basis q ∈ retainedChamber (M : ℕ) := by
      rwa [retainedChamber_eq_hsChamber]
    have ha : ∑ i, scalarPoincareRadialEmbedding basis a i = 0 :=
      scalarPoincare_radial_sum_zero (scalarPoincareRadialChart basis a)
    have h := hessian_blockRetainedEnergy_zero_sum χ e hmono hz
      (block_curvature_of_full_chamber χ e hmono he0 hcurv hz)
      (scalarPoincareRadialEmbedding basis a) ha
    rw [blockRetainedEnergy_eq_pairExpression χ e hmono] at h
    simpa only [LinearIsometry.norm_map] using h
  have h1 := convexOn_sub_norm_sq_of_hessian_lower (convex_scalarPoincareRadialDomain basis)
    (isOpen_scalarPoincareRadialDomain basis)
    ((contDiffOn_scalarPoincareRadialPotential basis ψ).of_le (by norm_num)) hH
  have ht := convexOn_blockTilde hPL χ hc e hmono M.pos he0
  have h2 : ConvexOn ℝ (scalarPoincareRadialDomain basis)
      (fun q => blockTilde χ e (scalarPoincareRadialEmbedding basis q)) := by
    refine ⟨convex_scalarPoincareRadialDomain basis, fun x hx y hy a b ha hb hab => ?_⟩
    have hx' : scalarPoincareRadialEmbedding basis x ∈ retainedChamber (M : ℕ) := by
      rwa [retainedChamber_eq_hsChamber]
    have hy' : scalarPoincareRadialEmbedding basis y ∈ retainedChamber (M : ℕ) := by
      rwa [retainedChamber_eq_hsChamber]
    simpa only [map_add, map_smul] using ht.2 hx' hy' ha hb hab
  have h := h1.add h2
  convert h using 1
  funext q
  dsimp [blockRadialPotential, scalarPoincareRadialPotential, ψ]
  rw [blockRetainedEnergy_eq_pairExpression χ e hmono]
  ring

namespace Internal

/-- The radial analytic conclusion of Lemma 3.9. The input is an actual weighted
`H¹` function on the radial law. Passing from the circular marginal to this input remains a
separate Sobolev descent problem. This internal theorem does not replace that step by an
additional hypothesis of the circular theorem. -/
theorem block_radial_concentration (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c) (hc₁ : 0 < c₁)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩)
    (basis : OrthonormalBasis (Fin (Module.finrank ℝ (hsOrthSubspace M))) ℝ (hsOrthSubspace M))
    (hcurv : ∀ x ∈ hsChamber N, ∀ i j : Fin (M : ℕ), i < j → c₁ / 2 ≤
      deriv (deriv (χ.potential (e (Sum.inl i)) (e (Sum.inl j)))) (x (e (Sum.inl j)) - x (e (Sum.inl i))))
    {F : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace M))) → ℝ}
    {G : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace M))) →
      EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace M)))}
    (hFG : WeightedSobolev.IsWeightedH1
      ((volume.restrict (scalarPoincareRadialDomain basis)).tilted
        (fun q => -blockRadialPotential χ e basis q)) (scalarPoincareRadialDomain basis) F G)
    {L : ℝ} (hL : ∀ᵐ q ∂((volume.restrict (scalarPoincareRadialDomain basis)).tilted
      (fun q => -blockRadialPotential χ e basis q)), ‖G q‖ ≤ L) (t : ℝ) :
    IsProbabilityMeasure ((volume.restrict (scalarPoincareRadialDomain basis)).tilted
      (fun q => -blockRadialPotential χ e basis q)) ∧
      Integrable F ((volume.restrict (scalarPoincareRadialDomain basis)).tilted
        (fun q => -blockRadialPotential χ e basis q)) ∧
      Integrable (fun q => Real.exp (t * F q))
        ((volume.restrict (scalarPoincareRadialDomain basis)).tilted
          (fun q => -blockRadialPotential χ e basis q)) ∧
      Real.log (∫ q, Real.exp (t * F q)
        ∂((volume.restrict (scalarPoincareRadialDomain basis)).tilted
          (fun q => -blockRadialPotential χ e basis q))) ≤
        t * ∫ q, F q ∂((volume.restrict (scalarPoincareRadialDomain basis)).tilted
          (fun q => -blockRadialPotential χ e basis q)) + t ^ 2 * L ^ 2 / (2 * c₁ * M) := by
  have h := block_herbst_of_convex_residual hBE
    (isOpen_scalarPoincareRadialDomain basis) (convex_scalarPoincareRadialDomain basis)
    (bounded_scalarPoincareRadialDomain basis) (nonempty_scalarPoincareRadialDomain basis)
    (mul_pos hc₁ (Nat.cast_pos.mpr M.pos))
    (convexOn_blockRadialResidual hPL χ hc e hmono he0 basis hcurv) hFG hL t
  simpa only [mul_assoc] using h

end Internal

end Riesz1

end
