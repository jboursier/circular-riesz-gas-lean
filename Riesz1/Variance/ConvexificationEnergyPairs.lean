/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.ConvexificationPotential
public import Riesz1.Rigidity.CurvatureLaw

/-!
# Pair potentials for the actual nearest-neighbour tilt

The pair representation of the nearest-neighbour tilt. Each selected directed
cyclic edge contributes half its penalty to its unordered pair. In
particular both directed edges contribute when there are two particles.
-/

@[expose] public section

noncomputable section

open Set Finset MeasureTheory
open scoped ContDiff

namespace Riesz1

/-- The unordered pair underlying a cyclic edge, in increasing order. -/
def nearestEdgePair (N : ℕ+) (e : Fin (N : ℕ)) : Fin (N : ℕ) × Fin (N : ℕ) :=
  (min e (nextLabel N e), max e (nextLabel N e))

theorem nextLabel_ne_self {N : ℕ+} (hN : 2 ≤ (N : ℕ)) (e : Fin (N : ℕ)) :
    nextLabel N e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  simp only [nextLabel] at hv
  by_cases he : e.val + 1 < (N : ℕ)
  · rw [Nat.mod_eq_of_lt he] at hv
    omega
  · have he' : e.val + 1 = (N : ℕ) := by have := e.isLt; omega
    rw [he', Nat.mod_self] at hv
    omega

theorem nearestEdgePair_mem {n : ℕ} (hn : 1 ≤ n) (e : Fin (n.succPNat : ℕ)) :
    nearestEdgePair n.succPNat e ∈ pairSet n := by
  apply mem_filter.mpr
  exact ⟨mem_univ _, min_lt_max.mpr (nextLabel_ne_self (by simpa using hn) e).symm⟩

/-- The separation of a directed edge from the separation of its unordered pair. -/
def nearestEdgeSeparation (N : ℕ+) (e : Fin (N : ℕ)) (r : ℝ) : ℝ :=
  if e < nextLabel N e then r else 1 - r

theorem nearestEdgeSeparation_pos (N : ℕ+) (e : Fin (N : ℕ)) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) : 0 < nearestEdgeSeparation N e r := by
  unfold nearestEdgeSeparation
  split_ifs <;> linarith [hr.1, hr.2]

/-- A selected edge contributes to its unordered pair. Contributions add even
when two different edges have the same unordered pair. -/
def nearestPairPenalty (β : ℝ) (θ : ℝ → ℝ) (N : ℕ+) (E : Finset (Fin (N : ℕ)))
    (R : ℝ) (i j : Fin (N : ℕ)) (r : ℝ) : ℝ :=
  ∑ e ∈ E, if nearestEdgePair N e = (i, j) then
    β / 2 * θ ((N : ℝ) / R * nearestEdgeSeparation N e r) else 0

/-- The two-particle boundary case: both directed cyclic edges contribute
to the single unordered pair. -/
theorem nearestPairPenalty_two (β : ℝ) (θ : ℝ → ℝ) (R r : ℝ) :
    nearestPairPenalty β θ 2 univ R 0 1 r =
      β / 2 * θ (2 / R * r) + β / 2 * θ (2 / R * (1 - r)) := by
  unfold nearestPairPenalty
  change (∑ e : Fin 2, _) = _
  rw [Fin.sum_univ_two]
  have hp0 : nearestEdgePair 2 (0 : Fin 2) = (0, 1) := rfl
  have hp1 : nearestEdgePair 2 (1 : Fin 2) = (0, 1) := rfl
  have h01 : (0 : Fin 2) < 1 := by norm_num
  have hs0 : nearestEdgeSeparation 2 (0 : Fin 2) r = r := by
    change (if (0 : Fin 2) < 1 then r else 1 - r) = r
    exact ite_eq_left h01
  have hs1 : nearestEdgeSeparation 2 (1 : Fin 2) r = 1 - r := by
    change (if (1 : Fin 2) < 0 then r else 1 - r) = 1 - r
    exact ite_eq_right (not_lt.mpr h01.le)
  rw [hp0, hp1]
  simp only [ite_true]
  rw [hs0, hs1]
  norm_num


theorem nearestPairPenalty_smooth (β : ℝ) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ)
    (N : ℕ+) (E : Finset (Fin (N : ℕ))) (R : ℝ) (i j : Fin (N : ℕ)) :
    ContDiff ℝ ∞ (nearestPairPenalty β θ N E R i j) := by
  unfold nearestPairPenalty
  apply ContDiff.sum
  intro e _
  split_ifs
  · unfold nearestEdgeSeparation
    split_ifs
    · exact contDiff_const.mul (hθ.1.comp (contDiff_const.mul contDiff_id))
    · exact contDiff_const.mul
        (hθ.1.comp (contDiff_const.mul (contDiff_const.sub contDiff_id)))
  · exact contDiff_const

/-- Convexity of the forcing cutoff on `[0, ∞)`. -/
theorem forcingCutoff_convexOn_nonneg {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) :
    ConvexOn ℝ (Ici (0 : ℝ)) θ := by
  apply convexOn_of_deriv2_nonneg' (convex_Ici _)
    (hθ.1.differentiable (by simp)).differentiableOn
    ((hθ.1.of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)).differentiable_deriv_two).differentiableOn
  intro r hr
  exact (hθ.2.2.2.1 r hr).1

theorem nearestPairPenalty_convex {β : ℝ} (hβ : 0 ≤ β) {θ : ℝ → ℝ}
    (hθ : IsForcingCutoff θ) (N : ℕ+) (E : Finset (Fin (N : ℕ))) {R : ℝ}
    (hR : 0 < R) (i j : Fin (N : ℕ)) :
    ConvexOn ℝ (Ioo (0 : ℝ) 1) (nearestPairPenalty β θ N E R i j) := by
  unfold nearestPairPenalty
  have hterm (e : Fin (N : ℕ)) : ConvexOn ℝ (Ioo (0 : ℝ) 1)
      (fun r => if nearestEdgePair N e = (i, j) then
        β / 2 * θ ((N : ℝ) / R * nearestEdgeSeparation N e r) else 0) := by
    split_ifs
    · apply ConvexOn.smul (div_nonneg hβ (by norm_num))
      let L : ℝ →ᵃ[ℝ] ℝ :=
        if e < nextLabel N e then
          ((N : ℝ) / R) • AffineMap.id ℝ ℝ
        else ((N : ℝ) / R) • (AffineMap.const ℝ ℝ 1 - AffineMap.id ℝ ℝ)
      have hL (r : ℝ) : L r = (N : ℝ) / R * nearestEdgeSeparation N e r := by
        dsimp [L, nearestEdgeSeparation]
        split_ifs <;> rfl
      have hc := (forcingCutoff_convexOn_nonneg hθ).comp_affineMap L
      have hc' := hc.subset (fun r hr => show L r ∈ Ici (0 : ℝ) from by
        rw [hL]
        exact mul_nonneg (div_nonneg (by positivity) hR.le)
          (nearestEdgeSeparation_pos N e hr).le) (convex_Ioo 0 1)
      simpa only [Function.comp_def, hL, smul_eq_mul] using hc'
    · exact convexOn_const _ (convex_Ioo _ _)
  induction E using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using convexOn_const (0 : ℝ) (convex_Ioo 0 1)
  | @insert e E he ih =>
      simp only [Finset.sum_insert he]
      exact (hterm e).add ih

/-- Riesz pairs with exactly the selected cyclic nearest-neighbour penalties. -/
def nearestTiltedPairs (P : Parameters) (N : ℕ+) {θ : ℝ → ℝ}
    (hθ : IsForcingCutoff θ) (K γ ε : ℝ) (hK : 0 < K) :
    HsPairPotentials N
      (P.val.1 * (N : ℝ) ^ (-(parametersExponent P).val) *
        ((parametersExponent P).val * ((parametersExponent P).val + 1))) :=
  (hsRieszPairPotentials N P.val.1 P.2.1 (parametersExponent P)).addConvex
    (nearestPairPenalty P.val.1 θ N (nearestPairs N (window N K γ)) (K ^ ε))
    (fun i j _ => (nearestPairPenalty_smooth P.val.1 hθ N _ _ i j).contDiffOn)
    (fun i j _ => nearestPairPenalty_convex P.2.1.le hθ N _
      (Real.rpow_pos_of_pos hK _) i j)

/-- Orientation and the period offset recover the actual cyclic gap. -/
theorem nearestEdgeSeparation_pairForm {n : ℕ} (hn : 1 ≤ n)
    (e : Fin (n.succPNat : ℕ)) (y : Fin n → ℝ) :
    nearestEdgeSeparation n.succPNat e (pairForm n (nearestEdgePair n.succPNat e) y) =
      edgeForm n e y + wrapOffset n e := by
  by_cases he : e.val = n
  · have hnext : nextLabel n.succPNat e = 0 := by
      apply Fin.ext
      simp [nextLabel, he]
    have h0 : (0 : Fin (n.succPNat : ℕ)) < e := by
      change 0 < e.val
      omega
    unfold nearestEdgeSeparation nearestEdgePair
    rw [hnext, ite_eq_right (not_lt.mpr h0.le), min_eq_right h0.le, max_eq_left h0.le,
      pairForm_apply, edgeForm_apply, hnext]
    simp only [wrapOffset, he, ite_true]
    ring
  · have hlt : e.val + 1 < (n.succPNat : ℕ) := by
      have := e.isLt
      simp only [Nat.succPNat_coe] at this ⊢
      omega
    have he' : e < nextLabel n.succPNat e := by
      change e.val < (e.val + 1) % (n.succPNat : ℕ)
      rw [Nat.mod_eq_of_lt hlt]
      omega
    unfold nearestEdgeSeparation nearestEdgePair
    rw [ite_eq_left he', min_eq_left he'.le, max_eq_right he'.le, pairForm_apply, edgeForm_apply]
    simp only [wrapOffset, he, ite_false, add_zero]

/-- Summing pair penalties counts each selected edge exactly once. -/
theorem nearestPairPenalty_sum {n : ℕ} (hn : 1 ≤ n) (β : ℝ) (θ : ℝ → ℝ)
    (E : Finset (Fin (n.succPNat : ℕ))) (R : ℝ) (y : Fin n → ℝ) :
    2 * (∑ p ∈ pairSet n, nearestPairPenalty β θ n.succPNat E R p.1 p.2 (pairForm n p y)) =
      β * ∑ e ∈ E, θ (((n : ℝ) + 1) * (edgeForm n e y + wrapOffset n e) / R) := by
  unfold nearestPairPenalty
  rw [Finset.sum_comm]
  have he (e : Fin (n.succPNat : ℕ)) :
      (∑ p ∈ pairSet n, if nearestEdgePair n.succPNat e = (p.1, p.2) then
        β / 2 * θ ((n.succPNat : ℝ) / R * nearestEdgeSeparation n.succPNat e (pairForm n p y))
        else 0) =
      β / 2 * θ (((n : ℝ) + 1) * (edgeForm n e y + wrapOffset n e) / R) := by
    rw [Finset.sum_eq_single (nearestEdgePair n.succPNat e)]
    · simp only [Prod.mk.eta, ite_true, nearestEdgeSeparation_pairForm hn]
      congr 2
      change ((n + 1 : ℕ) : ℝ) / R * _ = _
      rw [Nat.cast_add, Nat.cast_one]
      ring
    · intro p _ hp
      simp only [Prod.mk.eta, Ne.symm hp, ite_false]
    · intro hp
      exact (hp (nearestEdgePair_mem hn e)).elim
  simp_rw [he, ← Finset.mul_sum]
  ring

/-- The pair datum has the exact anchored potential. -/
theorem nearestTiltedPairs_anchoredPotential (P : Parameters) {n : ℕ} (hn : 1 ≤ n)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (K γ ε : ℝ) (hK : 0 < K) (y : Fin n → ℝ) :
    hsAnchoredHamiltonian (nearestTiltedPairs P n.succPNat hθ K γ ε hK) y =
      anchoredPotential P.val.1 P.2.1 (parametersExponent P) θ n K γ ε y := by
  unfold hsAnchoredHamiltonian nearestTiltedPairs
  rw [hsPairExpression_addConvex, sum_filter_lt_eq]
  change hsAnchoredHamiltonian _ y +
    2 * (∑ p ∈ pairSet n,
      nearestPairPenalty P.val.1 θ n.succPNat _ _ p.1 p.2
        (anchorVector y p.2 - anchorVector y p.1)) = _
  simp_rw [← pairForm_apply]
  rw [nearestPairPenalty_sum hn]
  unfold anchoredPotential anchoredForcing
  simp_rw [anchoredGapAt_label]

/-- The fundamental Hamiltonian is the actual Gibbs energy plus nearest forcing. -/
theorem nearestTiltedPairs_hamiltonian (P : Parameters) {n : ℕ} (hn : 1 ≤ n)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (K γ ε : ℝ) (hK : 0 < K)
    (X : Configuration n.succPNat) :
    hsFundamentalHamiltonian (nearestTiltedPairs P n.succPNat hθ K γ ε hK) X =
      P.val.1 * energy (parametersExponent P) X +
        P.val.1 * nearestForcing θ n.succPNat K γ ε X := by
  rw [hsFundamentalHamiltonian_eq_anchored,
    nearestTiltedPairs_anchoredPotential P hn hθ K γ ε hK, anchoredPotential_eq_gibbs]

end Riesz1

end
