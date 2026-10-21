/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

/-!
# Distance to a finite intersection of open half spaces

For unit outward normals, the distance from an interior point to the
complement is the smallest signed margin. Redundant faces are allowed.
-/

@[expose] public section

noncomputable section

open Set Metric

namespace Riesz1

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [Nonempty ι]

/-- An intersection of finitely many strict affine half spaces. -/
def finiteOpenChamber (v : ι → E) (b : ι → ℝ) : Set E :=
  {x | ∀ i, inner ℝ (v i) x < b i}

/-- Minimum of the signed margins, including for points outside the chamber. -/
def finiteChamberMargin (v : ι → E) (b : ι → ℝ) (x : E) : ℝ :=
  (Finset.univ.image (fun i => b i - inner ℝ (v i) x)).min'
    (Finset.univ_nonempty.image _)

theorem finiteChamberMargin_le (v : ι → E) (b : ι → ℝ) (x : E) (i : ι) :
    finiteChamberMargin v b x ≤ b i - inner ℝ (v i) x :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

theorem finiteChamberMargin_exists_eq (v : ι → E) (b : ι → ℝ) (x : E) :
    ∃ i, finiteChamberMargin v b x = b i - inner ℝ (v i) x := by
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp
    (Finset.min'_mem (Finset.univ.image (fun i => b i - inner ℝ (v i) x))
      (Finset.univ_nonempty.image _))
  exact ⟨i, hi.symm⟩

/-- The elementary distance formula, proved by projection to a nearest face. -/
theorem infDist_compl_finiteOpenChamber (v : ι → E) (b : ι → ℝ)
    (hv : ∀ i, ‖v i‖ = 1) {x : E} (hx : x ∈ finiteOpenChamber v b) :
    infDist x (finiteOpenChamber v b)ᶜ = finiteChamberMargin v b x := by
  obtain ⟨i, hi⟩ := finiteChamberMargin_exists_eq v b x
  let m := finiteChamberMargin v b x
  have hm : 0 < m := by rw [show m = b i - inner ℝ (v i) x from hi]; exact sub_pos.mpr (hx i)
  let y := x + m • v i
  have hin : inner ℝ (v i) (v i) = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hyi : inner ℝ (v i) y = b i := by
    dsimp [y]
    rw [inner_add_right, inner_smul_right, hin, mul_one]
    linarith [hi]
  have hy : y ∈ (finiteOpenChamber v b)ᶜ := by
    intro hy
    have := hy i
    rw [hyi] at this
    exact lt_irrefl _ this
  apply le_antisymm
  · calc infDist x (finiteOpenChamber v b)ᶜ ≤ dist x y := infDist_le_dist_of_mem hy
      _ = m := by
        rw [dist_eq_norm]
        dsimp [y]
        rw [sub_add_cancel_left, norm_neg, norm_smul, hv, mul_one,
          Real.norm_eq_abs, abs_of_pos hm]
  · apply (le_infDist ⟨y, hy⟩).mpr
    intro z hz
    have hz' : ¬ ∀ j, inner ℝ (v j) z < b j := hz
    obtain ⟨j, hj⟩ := not_forall.mp hz'
    have hj' : b j ≤ inner ℝ (v j) z := le_of_not_gt hj
    calc m ≤ b j - inner ℝ (v j) x := finiteChamberMargin_le v b x j
      _ ≤ inner ℝ (v j) (z - x) := by rw [inner_sub_right]; linarith
      _ ≤ ‖v j‖ * ‖z - x‖ := real_inner_le_norm _ _
      _ = dist x z := by rw [hv, one_mul, ← dist_eq_norm, dist_comm]

end Riesz1

end
