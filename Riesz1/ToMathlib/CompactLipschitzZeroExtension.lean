/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Zero extension of compactly supported Lipschitz functions

A real Lipschitz function on an open metric subspace with compact support
has a globally Lipschitz zero extension with support still inside that subspace.
-/

@[expose] public section

noncomputable section

open Set Function Metric
open scoped NNReal

namespace Riesz1

/-- The canonical zero extension from an open metric subspace is Lipschitz
when the original support is compact. The extension and its support are
specified, so this introduces no choice of mathematical object. -/
theorem exists_lipschitz_zeroExtension {X : Type*} [MetricSpace X]
    {U : Set X} (hU : IsOpen U) {f : U → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hfc : HasCompactSupport f) :
    ∃ (F : X → ℝ) (D : ℝ≥0), LipschitzWith D F ∧
      (∀ x : U, F x.val = f x) ∧ (∀ x ∉ U, F x = 0) ∧
      HasCompactSupport F ∧ tsupport F ⊆ U := by
  classical
  let F : X → ℝ := fun x => if hx : x ∈ U then f ⟨x, hx⟩ else 0
  let K : Set X := Subtype.val '' tsupport f
  have hK : IsCompact K := hfc.image continuous_subtype_val
  have hKU : K ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.property
  have hFx (x : U) : F x.val = f x := by simp only [F, dite_eq_left x.property]
  have hFz (x : X) (hx : x ∉ U) : F x = 0 := by
    simp only [F, dite_eq_right hx]
  have hFs : tsupport F ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_cases hxU : x ∈ U
    · refine ⟨⟨x, hxU⟩, subset_tsupport f ?_, rfl⟩
      simpa only [Function.mem_support, ← hFx ⟨x, hxU⟩] using hx
    · exact False.elim (hx (hFz x hxU))
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨M, hM⟩ := hfc.exists_bound_of_continuous hf.continuous
  let m : ℝ≥0 := ⟨|M|, abs_nonneg M⟩
  let d : ℝ≥0 := ⟨|M| / δ, div_nonneg (abs_nonneg M) hδ.le⟩
  let D := C + d
  have hcross (x : U) (y : X) (hy : y ∉ U) :
      dist (f x) 0 ≤ (D : ℝ) * dist x.val y := by
    by_cases hx : f x = 0
    · simp only [hx, dist_self]
      positivity
    · have hxK : x.val ∈ K := ⟨x, subset_tsupport f hx, rfl⟩
      have hd : δ ≤ dist x.val y := by
        by_contra h
        have hh := mem_cthickening_of_dist_le y x.val δ K hxK
          (by rw [dist_comm]; exact (lt_of_not_ge h).le)
        exact hy (hδU hh)
      have hm : ‖f x‖ ≤ (m : ℝ) := (hM x).trans (le_abs_self M)
      have hCD : (m : ℝ) / δ ≤ (D : ℝ) := by
        change |M| / δ ≤ (C : ℝ) + |M| / δ
        exact le_add_of_nonneg_left C.2
      rw [dist_zero_right]
      calc
        ‖f x‖ ≤ (m : ℝ) := hm
        _ = ((m : ℝ) / δ) * δ := by field_simp
        _ ≤ ((m : ℝ) / δ) * dist x.val y :=
          mul_le_mul_of_nonneg_left hd (div_nonneg m.2 hδ.le)
        _ ≤ (D : ℝ) * dist x.val y := mul_le_mul_of_nonneg_right hCD dist_nonneg
  refine ⟨F, D, LipschitzWith.of_dist_le_mul (fun x y => ?_), hFx, hFz,
    hK.of_isClosed_subset (isClosed_tsupport _) hFs, hFs.trans hKU⟩
  by_cases hx : x ∈ U <;> by_cases hy : y ∈ U
  · rw [hFx ⟨x, hx⟩, hFx ⟨y, hy⟩]
    exact (hf.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩).trans
      (mul_le_mul_of_nonneg_right (show (C : ℝ) ≤ (D : ℝ) from by
        change (C : ℝ) ≤ (C : ℝ) + (d : ℝ)
        exact le_add_of_nonneg_right d.2) dist_nonneg)
  · rw [hFx ⟨x, hx⟩, hFz y hy]
    exact hcross ⟨x, hx⟩ y hy
  · rw [hFz x hx, hFx ⟨y, hy⟩, dist_comm, dist_comm x y]
    exact hcross ⟨y, hy⟩ x hx
  · rw [hFz x hx, hFz y hy, dist_self]
    positivity

end Riesz1
