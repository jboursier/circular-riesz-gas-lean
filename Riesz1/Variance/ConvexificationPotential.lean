/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.ConvexificationHessianForm
public import Riesz1.Variance.NearestForcing
public import Riesz1.Rigidity.GapLawReversal
public import Riesz1.Rigidity.GapLaw

/-!
# The anchored potential is the Gibbs energy plus the forcing

The anchored potential `β (H_N^* + F^*)` is the anchored version of the Gibbs
potential `β H_N + β F_{ε,γ}`. This file identifies the two sides on configurations:

`β · energy s X + β · nearestForcing θ N K γ ε X = anchoredPotential β hβ s θ n K γ ε (anchorCoords X)`

for `N = n + 1` and every configuration `X`, where `anchorCoords X` is the anchored coordinate vector of
`X`. Hence the Hessian bound `anchoredPotential_hessian_lower` is a statement about the potential of the
Gibbs law and of the convexified law, in their anchored coordinates.

The identity `β · energy = β · H_N` is the symmetry of the pair energy, `rieszRepresentative_neg`. The
double sum over ordered pairs is split into the pairs `i < j` and `j < i`, which are exchanged by the
symmetry.
-/

@[expose] public section

open Finset

namespace Riesz1

/-- For a symmetric array `f`, the sum over ordered pairs `i ≠ j` is twice the sum over `i < j`. -/
lemma sum_erase_eq_two_mul_sum_lt (m : ℕ) (f : Fin m → Fin m → ℝ)
    (hf : ∀ i j, f j i = f i j) :
    ∑ i : Fin m, ∑ j ∈ univ.erase i, f i j =
      2 * ∑ i : Fin m, ∑ j ∈ univ.filter (i < ·), f i j := by
  set F : Fin m → Fin m → ℝ := fun i j => if i < j then f i j else 0 with hFdef
  set G : Fin m → Fin m → ℝ := fun i j => if j < i then f i j else 0 with hGdef
  have hsplit : ∀ i, ∑ j ∈ univ.erase i, f i j = ∑ j, (F i j + G i j) := by
    intro i
    have h0 : F i i + G i i = 0 := by
      simp [hFdef, hGdef]
    rw [← Finset.sum_erase (f := fun j => F i j + G i j) univ h0]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    rcases lt_or_gt_of_ne hji with h | h
    · simp [hFdef, hGdef, not_lt.mpr h.le, h]
    · simp [hFdef, hGdef, h, not_lt.mpr h.le]
  have hG : ∀ i j, G i j = F j i := by
    intro i j
    simp only [hFdef, hGdef, hf]
  calc ∑ i : Fin m, ∑ j ∈ univ.erase i, f i j
      = ∑ i : Fin m, ∑ j : Fin m, (F i j + G i j) :=
        Finset.sum_congr rfl fun i _ => hsplit i
    _ = ∑ i : Fin m, ∑ j : Fin m, F i j + ∑ i : Fin m, ∑ j : Fin m, G i j := by
        simp only [Finset.sum_add_distrib]
    _ = 2 * ∑ i : Fin m, ∑ j : Fin m, F i j := by
        have hGF : ∑ i : Fin m, ∑ j : Fin m, G i j = ∑ i : Fin m, ∑ j : Fin m, F i j := by
          simp only [hG]
          exact Finset.sum_comm
        rw [hGF]
        ring
    _ = 2 * ∑ i : Fin m, ∑ j ∈ univ.filter (i < ·), f i j := by
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_filter]

/-- The Riesz energy, times `β`, is the Riesz pair expression on the lift of the configuration. -/
theorem beta_energy_eq_pairExpression (β : ℝ) (hβ : 0 < β) (s : RieszExponent) (n : ℕ)
    (X : Configuration n.succPNat) :
    β * energy s X = hsPairExpression (hsRieszPairPotentials n.succPNat β hβ s)
      (WithLp.toLp 2 X.val) := by
  rw [hsPairExpression_hsRieszPairPotentials]
  unfold energy
  set f : Fin (n.succPNat : ℕ) → Fin (n.succPNat : ℕ) → ℝ := fun i j =>
    rieszRepresentative s ((X.val i - X.val j : ℝ) : UnitAddCircle) with hfdef
  have hf : ∀ i j, f j i = f i j := by
    intro i j
    simp only [hfdef]
    have h := rieszRepresentative_neg s (((X.val i - X.val j : ℝ)) : UnitAddCircle)
    rw [← h]
    congr 1
    rw [← AddCircle.coe_neg]
    congr 1
    ring
  have hsum := sum_erase_eq_two_mul_sum_lt (n.succPNat : ℕ) f hf
  simp only [hfdef] at hsum
  rw [hsum]
  have hpos : (0 : ℝ) ≤ ((n.succPNat : ℕ) : ℝ) ^ (-s.val) := Real.rpow_nonneg (by positivity) _
  have hkey : ∑ i : Fin (n.succPNat : ℕ), ∑ j ∈ univ.filter (i < ·), f i j =
      ∑ i : Fin (n.succPNat : ℕ), ∑ j ∈ univ.filter (i < ·),
        rieszRepresentative s (((WithLp.toLp 2 X.val) j - (WithLp.toLp 2 X.val) i : ℝ) :
          UnitAddCircle) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hf i j]
  rw [hkey]
  ring

/-- **The anchored potential is the Gibbs potential.** For `N = n + 1` particles and every configuration
`X`, the anchored potential `β (H_N^* + F^*)` at the anchored coordinates of `X` equals
`β H_N(X) + β F_{ε,γ}(X)`, the potential of the Gibbs law and of the forcing. -/
theorem anchoredPotential_eq_gibbs (β : ℝ) (hβ : 0 < β) (s : RieszExponent) (θ : ℝ → ℝ)
    (n : ℕ) (K γ ε : ℝ) (X : Configuration n.succPNat) :
    anchoredPotential β hβ s θ n K γ ε (anchorCoords n X.val).2 =
      β * energy s X + β * nearestForcing θ n.succPNat K γ ε X := by
  have h1 : hsAnchoredHamiltonian (hsRieszPairPotentials n.succPNat β hβ s)
      (anchorCoords n X.val).2 = β * energy s X := by
    rw [beta_energy_eq_pairExpression β hβ s n X, ← hsFundamentalHamiltonian_eq_anchored]
    rfl
  have h2 : anchoredForcing θ n K γ ε (anchorCoords n X.val).2 =
      nearestForcing θ n.succPNat K γ ε X := by
    unfold anchoredForcing nearestForcing
    simp only [gap_eq_anchoredGapAt]
  unfold anchoredPotential
  rw [h1, h2]

end Riesz1

end
