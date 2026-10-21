/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsPhi

/-!
# The pairing against `ν ⊗ ν` and the Fubini exchange

For a pair kernel `G : ℝ → ℝ → ℝ`, `loopArcPairing N X G` is the double integral of `G` against
`ν ⊗ ν`, where `ν = ∑ᵢ δ_{z_i} - dz` on `[0, N)` and `z_i = loopArcPos N X i`. It is the
empirical-empirical sum, the two particle-background integrals and the background-background
integral. Unlike `loopArcL`, it keeps the diagonal of the empirical sum. The two agree for the
kernel `loopArcKernel`, which vanishes on the diagonal.

The main lemma `loopArcPairing_integral_comm` exchanges the pairing with an integral in the arc
variable `t`, under integrability hypotheses stated explicitly for each of the four blocks.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The pairing of a pair kernel `G` against `ν ⊗ ν`, `ν = ∑ᵢ δ_{z_i} - dz` on `[0, N)`, with
`z_i = loopArcPos N X i`: the empirical pairs, the two particle-background integrals with the
background measure, and the background-background integral. -/
noncomputable def loopArcPairing (N : ℕ+) (X : Configuration N) (G : ℝ → ℝ → ℝ) : ℝ :=
  (∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), G (loopArcPos N X i) (loopArcPos N X j))
    - (∑ i : Fin (N : ℕ), ∫ u in (0 : ℝ)..(N : ℝ), G (loopArcPos N X i) u)
    - (∑ j : Fin (N : ℕ), ∫ z in (0 : ℝ)..(N : ℝ), G z (loopArcPos N X j))
    + ∫ z in (0 : ℝ)..(N : ℝ), ∫ u in (0 : ℝ)..(N : ℝ), G z u

/-- The kernel `(b(z) - b(u)) g_N'(z - u)` vanishes on the diagonal. -/
theorem loopArcKernel_self (s : ℝ) (N : ℕ+) (b : ℝ → ℝ) (z : ℝ) :
    loopArcKernel s N b z z = 0 := by
  simp [loopArcKernel]

/-- The loop functional is the pairing of its kernel, since the kernel vanishes on the
diagonal. -/
theorem loopArcL_eq_pairing (s : ℝ) (N : ℕ+) (b : ℝ → ℝ) (X : Configuration N) :
    loopArcL s N b X = loopArcPairing N X (loopArcKernel s N b) := by
  have hsum : (∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
      (if j = i then (0 : ℝ) else loopArcKernel s N b (loopArcPos N X i) (loopArcPos N X j)))
      = ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
        loopArcKernel s N b (loopArcPos N X i) (loopArcPos N X j) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j = i
    · subst h
      simp [loopArcKernel_self]
    · simp [h]
  unfold loopArcL loopArcPairing
  rw [hsum]

/-- The arc variable `t` and the pairing commute. This is the Fubini exchange behind the
representation `L(b) = ∫ b'(t) ...`. The four hypotheses are the integrability of the four
blocks of the pairing: the empirical pairs, the particle-background blocks and the
background-background block, each in the variables that the block integrates. -/
theorem loopArcPairing_integral_comm (N : ℕ+) (X : Configuration N) (φ : ℝ → ℝ → ℝ → ℝ)
    (h1 : ∀ i j : Fin (N : ℕ), Integrable (fun t => φ t (loopArcPos N X i) (loopArcPos N X j))
      (volume.restrict (Ioc (0 : ℝ) N)))
    (h2 : ∀ i : Fin (N : ℕ), Integrable
      (fun p : ℝ × ℝ => φ p.1 (loopArcPos N X i) p.2)
      ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))))
    (h3 : ∀ j : Fin (N : ℕ), Integrable (fun p : ℝ × ℝ => φ p.1 p.2 (loopArcPos N X j))
      ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))))
    (h4 : Integrable (fun p : (ℝ × ℝ) × ℝ => φ p.2 p.1.1 p.1.2)
      (((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))).prod
        (volume.restrict (Ioc (0 : ℝ) N)))) :
    loopArcPairing N X (fun z u => ∫ t in (0 : ℝ)..(N : ℝ), φ t z u)
      = ∫ t in (0 : ℝ)..(N : ℝ), loopArcPairing N X (φ t) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  simp only [loopArcPairing, intervalIntegral.integral_of_le hN0]
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) N) with hμ
  -- Empirical block: the integral in `t` passes through the finite sums.
  have hB1 : ∫ t, ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), φ t (loopArcPos N X i) (loopArcPos N X j) ∂μ
      = ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), ∫ t, φ t (loopArcPos N X i) (loopArcPos N X j) ∂μ := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum]
      exact fun j _ => h1 i j
    · exact fun i _ => integrable_finsetSum _ fun j _ => h1 i j
  -- Particle-background block with the background variable `u`: Fubini in `(u, t)`.
  have hB2 : ∀ i : Fin (N : ℕ),
      ∫ u, ∫ t, φ t (loopArcPos N X i) u ∂μ ∂μ = ∫ t, ∫ u, φ t (loopArcPos N X i) u ∂μ ∂μ :=
    fun i => integral_integral_swap (f := fun u t => φ t (loopArcPos N X i) u) (h2 i).swap
  have hB2' : ∫ t, ∑ i : Fin (N : ℕ), ∫ u, φ t (loopArcPos N X i) u ∂μ ∂μ
      = ∑ i : Fin (N : ℕ), ∫ u, ∫ t, φ t (loopArcPos N X i) u ∂μ ∂μ := by
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => (hB2 i).symm
    · exact fun i _ => (h2 i).integral_prod_left
  -- Background-particle block with the background variable `z`: Fubini in `(z, t)`.
  have hB3 : ∀ j : Fin (N : ℕ),
      ∫ z', ∫ t, φ t z' (loopArcPos N X j) ∂μ ∂μ = ∫ t, ∫ z', φ t z' (loopArcPos N X j) ∂μ ∂μ :=
    fun j => integral_integral_swap (f := fun z' t => φ t z' (loopArcPos N X j)) (h3 j).swap
  have hB3' : ∫ t, ∑ j : Fin (N : ℕ), ∫ z', φ t z' (loopArcPos N X j) ∂μ ∂μ
      = ∑ j : Fin (N : ℕ), ∫ z', ∫ t, φ t z' (loopArcPos N X j) ∂μ ∂μ := by
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun j _ => (hB3 j).symm
    · exact fun j _ => (h3 j).integral_prod_left
  -- Background-background block: Fubini in `((z, u), t)`.
  have hψ : Integrable (fun zu : ℝ × ℝ => ∫ t, φ t zu.1 zu.2 ∂μ) (μ.prod μ) :=
    h4.integral_prod_left
  have hA : ∫ z', ∫ u, ∫ t, φ t z' u ∂μ ∂μ ∂μ
      = ∫ zu : ℝ × ℝ, ∫ t, φ t zu.1 zu.2 ∂μ ∂(μ.prod μ) :=
    (integral_prod _ hψ).symm
  have hC : ∫ zu : ℝ × ℝ, ∫ t, φ t zu.1 zu.2 ∂μ ∂(μ.prod μ)
      = ∫ t, ∫ zu : ℝ × ℝ, φ t zu.1 zu.2 ∂(μ.prod μ) ∂μ :=
    integral_integral_swap (f := fun (zu : ℝ × ℝ) t => φ t zu.1 zu.2) h4
  have hD : ∫ t, ∫ zu : ℝ × ℝ, φ t zu.1 zu.2 ∂(μ.prod μ) ∂μ
      = ∫ t, ∫ z', ∫ u, φ t z' u ∂μ ∂μ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [h4.prod_left_ae] with t ht
    exact integral_prod _ ht
  -- Integrability in `t` of the four blocks.
  have iA : Integrable (fun t => ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
      φ t (loopArcPos N X i) (loopArcPos N X j)) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => h1 i j
  have iB : Integrable (fun t => ∑ i : Fin (N : ℕ), ∫ u, φ t (loopArcPos N X i) u ∂μ) μ :=
    integrable_finsetSum _ fun i _ => (h2 i).integral_prod_left
  have iC : Integrable (fun t => ∑ j : Fin (N : ℕ), ∫ z', φ t z' (loopArcPos N X j) ∂μ) μ :=
    integrable_finsetSum _ fun j _ => (h3 j).integral_prod_left
  have iD : Integrable (fun t => ∫ z', ∫ u, φ t z' u ∂μ ∂μ) μ := by
    refine (h4.integral_prod_right).congr ?_
    filter_upwards [h4.prod_left_ae] with t ht
    exact integral_prod _ ht
  -- Assemble: rewrite each block as an integral in `t`, then split the integral.
  rw [← hB1, ← hB2', ← hB3', hA, hC, hD]
  have iAB : Integrable (fun t => (∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
      φ t (loopArcPos N X i) (loopArcPos N X j))
      - ∑ i : Fin (N : ℕ), ∫ u, φ t (loopArcPos N X i) u ∂μ) μ := iA.sub iB
  have iABC : Integrable (fun t => (∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
      φ t (loopArcPos N X i) (loopArcPos N X j))
      - (∑ i : Fin (N : ℕ), ∫ u, φ t (loopArcPos N X i) u ∂μ)
      - ∑ j : Fin (N : ℕ), ∫ z', φ t z' (loopArcPos N X j) ∂μ) μ := iAB.sub iC
  rw [integral_add iABC iD, integral_sub iAB iC, integral_sub iA iB]

end Riesz1

end
end
