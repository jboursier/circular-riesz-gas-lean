/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.NoExplosionEndpoints

/-!
# Convexity after removing the first singular interaction

The joint-energy step of Lemma 4.5.
Exactly the two ordered terms of the first pair are modified.
-/

public section

noncomputable section

open Set

namespace Riesz1

/-- The anchored joint energy remains convex after removing the singular part
of the first pair. -/
theorem convexOn_anchoredEnergy_sub_first_singularity (s : RieszExponent) (n : ℕ) :
    ConvexOn ℝ (anchoredDomain (n + 1)) (fun y =>
      anchoredEnergy s (n + 1) y - 2 * (n + 2 : ℝ) ^ (-s.val) * (y 0) ^ (-s.val)) := by
  let m := n + 2
  let g : Fin m → Fin m → (Fin (n + 1) → ℝ) → ℝ := fun i j y =>
    hurwitzKernel s.val (anchorVector y i - anchorVector y j)
  let f : Fin m → Fin m → (Fin (n + 1) → ℝ) → ℝ := fun i j y =>
    g i j y - (if i = 0 ∧ j = 1 then (y 0) ^ (-s.val) else 0) -
      (if i = 1 ∧ j = 0 then (y 0) ^ (-s.val) else 0)
  have hone : (0 : Fin m) ≠ 1 := (Fin.ne_of_val_ne (by simp [m]) : (1 : Fin m) ≠ 0).symm
  have h01 (y : Fin (n + 1) → ℝ) : g 0 1 y = hurwitzKernel s.val (y 0) := by
    simpa [g, m, anchorVector, hurwitzKernel] using
      congrArg (fun t : ℝ => 2 * t) (hurwitzZetaEven_re_even (s : ℂ) (y 0))
  have h10 (y : Fin (n + 1) → ℝ) : g 1 0 y = hurwitzKernel s.val (y 0) := by
    simp [g, m, anchorVector]
  have hc : ConvexOn ℝ (anchoredDomain (n + 1))
      (fun y => hurwitzKernel s.val (y 0) - (y 0) ^ (-s.val)) := by
    refine ⟨convex_anchoredDomain _, ?_⟩
    intro y hy z hz a b ha hb hab
    exact (convexOn_hurwitzKernel_sub_rpow s.val s.2.1 s.2.2).2
      (hy.1 0) (hz.1 0) ha hb hab
  have hfc (i j : Fin m) (hij : i ≠ j) : ConvexOn ℝ (anchoredDomain (n + 1)) (f i j) := by
    by_cases h : i = 0 ∧ j = 1
    · obtain ⟨rfl, rfl⟩ := h
      simpa only [f, h01, eq_self, true_and, and_self, ite_true,
        hone, false_and, ite_false, sub_zero] using hc
    · by_cases h' : i = 1 ∧ j = 0
      · obtain ⟨rfl, rfl⟩ := h'
        simpa only [f, h10, eq_self, true_and, and_self, ite_true,
          hone.symm, false_and, ite_false, sub_zero] using hc
      · have hreg := convexOn_anchored_pair s (n + 1) i j hij
        change ConvexOn ℝ (anchoredDomain (n + 1)) (fun y => g i j y) at hreg
        simpa only [f, h, h', ite_false, sub_zero] using hreg
  have hsum : ConvexOn ℝ (anchoredDomain (n + 1))
      (fun y => ∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, f i j y) := by
    refine ⟨convex_anchoredDomain _, ?_⟩
    intro y hy z hz a b ha hb hab
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ =>
      Finset.sum_le_sum (s := Finset.univ.erase i) (fun j hj =>
        (hfc i j (Finset.ne_of_mem_erase hj).symm).2 hy hz ha hb hab))
    simpa only [Finset.sum_add_distrib, ← Finset.smul_sum] using h
  have hid (y : Fin (n + 1) → ℝ) :
      (∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, f i j y) =
        (∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, g i j y) - 2 * (y 0) ^ (-s.val) := by
    simp only [f, Finset.sum_sub_distrib]
    have hleft : (∑ i : Fin m, ∑ j ∈ Finset.univ.erase i,
        if i = 0 ∧ j = 1 then (y 0) ^ (-s.val) else 0) = (y 0) ^ (-s.val) := by
      simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
      simp [hone.symm]
    have hright : (∑ i : Fin m, ∑ j ∈ Finset.univ.erase i,
        if i = 1 ∧ j = 0 then (y 0) ^ (-s.val) else 0) = (y 0) ^ (-s.val) := by
      simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
      simp [hone]
    rw [hleft, hright]
    ring
  have hscaled := hsum.smul (Real.rpow_nonneg (show (0 : ℝ) ≤ m by positivity) (-s.val))
  apply hscaled.congr
  intro y _
  dsimp only
  rw [hid]
  simp only [smul_eq_mul]
  unfold anchoredEnergy
  have hcoe : (((n + 1).succPNat : ℕ) : ℝ) = (n + 2 : ℝ) := by simp; ring
  rw [hcoe]
  have hm : (m : ℝ) = (n + 2 : ℝ) := by simp [m]
  rw [hm]
  change (n + 2 : ℝ) ^ (-s.val) *
    ((∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, g i j y) - 2 * (y 0) ^ (-s.val)) =
      (n + 2 : ℝ) ^ (-s.val) * (∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, g i j y) -
        2 * (n + 2 : ℝ) ^ (-s.val) * (y 0) ^ (-s.val)
  ring

end Riesz1

end
