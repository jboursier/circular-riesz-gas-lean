/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsPair

/-!
# Parametric Fubini exchange for the arc pairing

The arc pairing `loopArcPairing N X G` of `LoopArcsPair` integrates a kernel `G` against
`ν ⊗ ν`, where `ν = ∑ᵢ δ_{z_i} - dz` on `[0, N]`. The representation of `L(b)` and of the arc
function `Λ` integrates a family of kernels against a parameter measure
`π`. This file proves that the pairing commutes with such a parameter integral, for an arbitrary
σ-finite parameter measure `π`:

`loopArcPairing N X (fun z u => ∫ p, φ p z u ∂π) = ∫ p, loopArcPairing N X (φ p) ∂π`,

under the integrability of the four blocks (the empirical pairs, the two particle-background
blocks and the background-background block). The proof is that of
`loopArcPairing_integral_comm`, with the parameter `t` replaced by `p` and its measure `π`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- **Parametric Fubini exchange for the arc pairing.** The pairing of a parameter integral equals
the parameter integral of the pairings, under the integrability of the four blocks. The
background measure is `volume.restrict (Ioc 0 N)`, as in `loopArcPairing`. -/
theorem loopArcPairing_integral_param {α : Type*} [MeasurableSpace α] (π : Measure α)
    [SFinite π] (N : ℕ+) (X : Configuration N) (φ : α → ℝ → ℝ → ℝ)
    (h1 : ∀ i j : Fin (N : ℕ), Integrable (fun p => φ p (loopArcPos N X i) (loopArcPos N X j)) π)
    (h2 : ∀ i : Fin (N : ℕ), Integrable (fun q : α × ℝ => φ q.1 (loopArcPos N X i) q.2)
      (π.prod (volume.restrict (Ioc (0 : ℝ) N))))
    (h3 : ∀ j : Fin (N : ℕ), Integrable (fun q : α × ℝ => φ q.1 q.2 (loopArcPos N X j))
      (π.prod (volume.restrict (Ioc (0 : ℝ) N))))
    (h4 : Integrable (fun q : α × (ℝ × ℝ) => φ q.1 q.2.1 q.2.2)
      (π.prod ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))))) :
    loopArcPairing N X (fun z u => ∫ p, φ p z u ∂π) = ∫ p, loopArcPairing N X (φ p) ∂π := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  simp only [loopArcPairing, intervalIntegral.integral_of_le hN0]
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) N) with hν
  -- Empirical block: the parameter integral passes through the finite sums.
  have hB1 : ∫ p, ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), φ p (loopArcPos N X i) (loopArcPos N X j) ∂π
      = ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), ∫ p, φ p (loopArcPos N X i) (loopArcPos N X j) ∂π := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum]
      exact fun j _ => h1 i j
    · exact fun i _ => integrable_finsetSum _ fun j _ => h1 i j
  -- Particle-background block with the background variable `u`: Fubini in `(u, p)`.
  have hB2 : ∀ i : Fin (N : ℕ),
      ∫ u, ∫ p, φ p (loopArcPos N X i) u ∂π ∂ν = ∫ p, ∫ u, φ p (loopArcPos N X i) u ∂ν ∂π :=
    fun i => integral_integral_swap (f := fun u p => φ p (loopArcPos N X i) u) (h2 i).swap
  have hB2' : ∫ p, ∑ i : Fin (N : ℕ), ∫ u, φ p (loopArcPos N X i) u ∂ν ∂π
      = ∑ i : Fin (N : ℕ), ∫ u, ∫ p, φ p (loopArcPos N X i) u ∂π ∂ν := by
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => (hB2 i).symm
    · exact fun i _ => (h2 i).integral_prod_left
  -- Background-particle block with the background variable `z`: Fubini in `(z, p)`.
  have hB3 : ∀ j : Fin (N : ℕ),
      ∫ z, ∫ p, φ p z (loopArcPos N X j) ∂π ∂ν = ∫ p, ∫ z, φ p z (loopArcPos N X j) ∂ν ∂π :=
    fun j => integral_integral_swap (f := fun z p => φ p z (loopArcPos N X j)) (h3 j).swap
  have hB3' : ∫ p, ∑ j : Fin (N : ℕ), ∫ z, φ p z (loopArcPos N X j) ∂ν ∂π
      = ∑ j : Fin (N : ℕ), ∫ z, ∫ p, φ p z (loopArcPos N X j) ∂π ∂ν := by
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun j _ => (hB3 j).symm
    · exact fun j _ => (h3 j).integral_prod_left
  -- Background-background block: Fubini in `((z, u), p)`.
  have hψ : Integrable (fun zu : ℝ × ℝ => ∫ p, φ p zu.1 zu.2 ∂π) (ν.prod ν) :=
    h4.integral_prod_right
  have hA : ∫ z, ∫ u, ∫ p, φ p z u ∂π ∂ν ∂ν
      = ∫ zu : ℝ × ℝ, ∫ p, φ p zu.1 zu.2 ∂π ∂(ν.prod ν) :=
    (integral_prod _ hψ).symm
  have hC : ∫ zu : ℝ × ℝ, ∫ p, φ p zu.1 zu.2 ∂π ∂(ν.prod ν)
      = ∫ p, ∫ zu : ℝ × ℝ, φ p zu.1 zu.2 ∂(ν.prod ν) ∂π :=
    integral_integral_swap (f := fun (zu : ℝ × ℝ) p => φ p zu.1 zu.2) h4.swap
  have hD : ∫ p, ∫ zu : ℝ × ℝ, φ p zu.1 zu.2 ∂(ν.prod ν) ∂π
      = ∫ p, ∫ z, ∫ u, φ p z u ∂ν ∂ν ∂π := by
    refine integral_congr_ae ?_
    filter_upwards [h4.prod_right_ae] with p hp
    exact integral_prod _ hp
  -- Integrability in the parameter of the four blocks.
  have iA : Integrable (fun p => ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
      φ p (loopArcPos N X i) (loopArcPos N X j)) π :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => h1 i j
  have iB : Integrable (fun p => ∑ i : Fin (N : ℕ), ∫ u, φ p (loopArcPos N X i) u ∂ν) π :=
    integrable_finsetSum _ fun i _ => (h2 i).integral_prod_left
  have iC : Integrable (fun p => ∑ j : Fin (N : ℕ), ∫ z, φ p z (loopArcPos N X j) ∂ν) π :=
    integrable_finsetSum _ fun j _ => (h3 j).integral_prod_left
  have iD : Integrable (fun p => ∫ z, ∫ u, φ p z u ∂ν ∂ν) π := by
    refine (h4.integral_prod_left).congr ?_
    filter_upwards [h4.prod_right_ae] with p hp
    exact integral_prod _ hp
  -- Assemble: rewrite each block as an integral in `p`, then split the integral.
  rw [← hB1, ← hB2', ← hB3', hA, hC, hD]
  have iAB : Integrable (fun p => (∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
      φ p (loopArcPos N X i) (loopArcPos N X j))
      - ∑ i : Fin (N : ℕ), ∫ u, φ p (loopArcPos N X i) u ∂ν) π := iA.sub iB
  have iABC : Integrable (fun p => (∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
      φ p (loopArcPos N X i) (loopArcPos N X j))
      - (∑ i : Fin (N : ℕ), ∫ u, φ p (loopArcPos N X i) u ∂ν)
      - ∑ j : Fin (N : ℕ), ∫ z, φ p z (loopArcPos N X j) ∂ν) π := iAB.sub iC
  rw [integral_add iABC iD, integral_sub iAB iC, integral_sub iA iB]

end Riesz1

end
end
