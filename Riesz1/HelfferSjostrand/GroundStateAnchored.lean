/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BoundaryCoreAnchoredGeometry
public import Riesz1.HelfferSjostrand.BoundaryCoreBarrier

/-!
# The anchored ground-state barrier

Smoothness and real/complex distributional uniqueness for the anchored
potential in the proof of the scalar boundary core. This module does not
identify the domain or closure of the anchored operator on test functions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ContDiff Laplacian

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- The ground-state potential of the anchored Hamiltonian is smooth
throughout the anchored simplex. -/
theorem contDiffOn_hsAnchoredGroundStatePotential (χ : HsPairPotentials n.succPNat c) :
    ContDiffOn ℝ ∞ (hsAnchoredGroundStatePotential χ) (anchoredSimplex n) := by
  have hH := contDiffOn_hsAnchoredHamiltonianE χ
  have hd := hH.fderiv_of_isOpen (isOpen_anchoredSimplex n) (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  have hdd := hd.fderiv_of_isOpen (isOpen_anchoredSimplex n) (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  have hg : ContDiffOn ℝ ∞ (fun y => gradient (hsAnchoredHamiltonianE χ) y) (anchoredSimplex n) :=
    (InnerProductSpace.toDual ℝ (AnchoredEuclidean n)).symm.contDiff.comp_contDiffOn hd
  have he : Δ (hsAnchoredHamiltonianE χ) = fun y => ∑ i,
      fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) y
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
    simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
      (EuclideanSpace.basisFun (Fin n) ℝ), iteratedFDeriv_two_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, EuclideanSpace.basisFun_apply]
  have hl : ContDiffOn ℝ ∞ (Δ (hsAnchoredHamiltonianE χ)) (anchoredSimplex n) := by
    rw [he]
    exact ContDiffOn.sum fun i _ => (hdd.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  exact ((hg.norm_sq ℝ).div_const 4).sub (hl.div_const 2)

namespace Internal

private theorem anchoredSimplex_compl_nonempty (hn : 0 < n) : (anchoredSimplex n)ᶜ.Nonempty := by
  refine ⟨0, fun h => ?_⟩
  exact (lt_irrefl (0 : ℝ)) ((h.1 ⟨0, hn⟩).1)

/-- Admissibility gives uniqueness of real anchored L² distributional
solutions for every shift strictly above the barrier constant. -/
theorem anchored_schrodinger_eq_zero {C_N lam : ℝ} (χ : HsPairPotentials n.succPNat c)
    (hc : 0 < c) (hadm : HsAdmissible χ C_N) (hlam : C_N < lam)
    {u : AnchoredEuclidean n → ℝ} (huL : MemLp u 2 (volume.restrict (anchoredSimplex n)))
    (hu : IsDistributionalSchrodingerSolution (anchoredSimplex n)
      (hsAnchoredGroundStatePotential χ) lam u) :
    u =ᵐ[volume.restrict (anchoredSimplex n)] 0 := by
  have hn : 0 < n := by have hN := hadm.choose; change 2 ≤ n + 1 at hN; omega
  exact schrodinger_eq_zero_of_boundary_barrier (isOpen_anchoredSimplex n)
    (isBounded_anchoredSimplex n) (anchoredSimplex_compl_nonempty hn)
    (contDiffOn_hsAnchoredGroundStatePotential χ) hlam
    (fun _ hy => hsAnchoredGroundStatePotential_boundary_lower χ hc hadm hy) huL hu

/-- The same uniqueness assertion for complex anchored L² solutions. -/
theorem anchored_schrodinger_complex_eq_zero {C_N lam : ℝ} (χ : HsPairPotentials n.succPNat c)
    (hc : 0 < c) (hadm : HsAdmissible χ C_N) (hlam : C_N < lam)
    {u : AnchoredEuclidean n → ℂ} (huL : MemLp u 2 (volume.restrict (anchoredSimplex n)))
    (hu : IsDistributionalSchrodingerSolution (anchoredSimplex n)
      (hsAnchoredGroundStatePotential χ) lam u) :
    u =ᵐ[volume.restrict (anchoredSimplex n)] 0 := by
  have hn : 0 < n := by have hN := hadm.choose; change 2 ≤ n + 1 at hN; omega
  exact schrodinger_complex_eq_zero_of_boundary_barrier (isOpen_anchoredSimplex n)
    (isBounded_anchoredSimplex n) (anchoredSimplex_compl_nonempty hn)
    (contDiffOn_hsAnchoredGroundStatePotential χ) hlam
    (fun _ hy => hsAnchoredGroundStatePotential_boundary_lower χ hc hadm hy) huL hu

end Internal

end Riesz1
