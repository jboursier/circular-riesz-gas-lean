/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SettingBoundary
public import Riesz1.HelfferSjostrand.GeometryHessian

/-!
# Geometry for Riesz boundary growth

The smallest cyclic gap is a pair separation or its complement, and
it bounds both quantities for every pair. The equispaced comparison
configuration has bounded displacement. These are the geometric steps
of the boundary growth estimate.
-/

@[expose] public section

noncomputable section

open Set Finset
open scoped Topology

namespace Riesz1

namespace Internal

theorem hs_boundary_mul_sqrt_le_gap (n : ℕ) {x : HsEuclidean (n + 1).succPNat}
    (hx : x ∈ hsChamber (n + 1).succPNat) (f : HsCollisionFace n) :
    hsBoundaryDistance (n + 1).succPNat (by change 2 ≤ n + 1 + 1; omega) x *
        Real.sqrt 2 ≤ hsCollisionGap n x f := by
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mp
  rw [hsBoundaryDistance_eq_min_gap n hx]
  exact min'_le _ _ (mem_image.mpr ⟨f, mem_univ _, rfl⟩)

end Internal

/-- Every pair separation and its complement contain at least one cyclic gap. -/
theorem hsBoundaryDistance_pair_lower (n : ℕ) {x : HsEuclidean (n + 1).succPNat}
    (hx : x ∈ hsChamber (n + 1).succPNat) {i j : Fin (n + 2)} (hij : i < j) :
    let δ := hsBoundaryDistance (n + 1).succPNat
      (by change 2 ≤ n + 1 + 1; omega) x * Real.sqrt 2
    δ ≤ x j - x i ∧ δ ≤ 1 - (x j - x i) := by
  dsimp only
  have hi : i.val < n + 1 := by have := j.isLt; have := hij; omega
  let k : Fin (n + 1) := ⟨i.val, hi⟩
  have hk : k.castSucc = i := Fin.ext rfl
  have hkj : k.succ ≤ j := by apply Fin.le_iff_val_le_val.mpr; exact hij
  have h₁ := Internal.hs_boundary_mul_sqrt_le_gap n hx (some k)
  have h₂ := Internal.hs_boundary_mul_sqrt_le_gap n hx none
  change _ ≤ x k.succ - x k.castSucc at h₁
  rw [hk] at h₁
  change _ ≤ 1 + x 0 - x (Fin.last (n + 1)) at h₂
  constructor
  · linarith [hx.1.monotone hkj]
  · have hzero : (0 : Fin (n + 2)) ≤ i := Fin.zero_le _
    have hlo : x 0 ≤ x i := hx.1.monotone hzero
    have hhi : x j ≤ x (Fin.last (n + 1)) := hx.1.monotone (Fin.le_last j)
    linarith

/-- One pair realizes a nearest collision face, at either endpoint of `(0,1)`. -/
theorem hsBoundaryDistance_pair_attains (n : ℕ) {x : HsEuclidean (n + 1).succPNat}
    (hx : x ∈ hsChamber (n + 1).succPNat) :
    ∃ i j : Fin (n + 2), i < j ∧
      (x j - x i = hsBoundaryDistance (n + 1).succPNat
          (by change 2 ≤ n + 1 + 1; omega) x * Real.sqrt 2 ∨
        1 - (x j - x i) = hsBoundaryDistance (n + 1).succPNat
          (by change 2 ≤ n + 1 + 1; omega) x * Real.sqrt 2) := by
  have hmem := min'_mem
    (univ.image (fun f : HsCollisionFace n => hsCollisionGap n x f / Real.sqrt 2))
    (univ_nonempty.image _)
  rw [← hsBoundaryDistance_eq_min_gap n hx] at hmem
  obtain ⟨f, _, hf⟩ := mem_image.mp hmem
  have hf' : hsCollisionGap n x f = hsBoundaryDistance (n + 1).succPNat
      (by change 2 ≤ n + 1 + 1; omega) x * Real.sqrt 2 :=
    (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))).mp hf
  cases f with
  | none =>
    refine ⟨0, Fin.last (n + 1), ?_, Or.inr ?_⟩
    · change 0 < n + 1
      omega
    · change 1 - (x (Fin.last (n + 1)) - x 0) = _
      change 1 + x 0 - x (Fin.last (n + 1)) = _ at hf'
      linarith
  | some k => exact ⟨k.castSucc, k.succ, Fin.castSucc_lt_succ, Or.inl hf'⟩

/-- The equispaced comparison lift with the same first coordinate. -/
def hsEquispacedComparison {N : ℕ+} (x : HsEuclidean N) : HsEuclidean N :=
  WithLp.toLp 2 (fun i => x ⟨0, N.pos⟩ + (i.val : ℝ) / (N : ℝ))

theorem hsEquispacedComparison_separation {N : ℕ+} (x : HsEuclidean N)
    (i j : Fin (N : ℕ)) :
    hsEquispacedComparison x j - hsEquispacedComparison x i =
      ((j.val : ℝ) - i.val) / (N : ℝ) := by
  change (x ⟨0, N.pos⟩ + (j.val : ℝ) / (N : ℝ)) -
    (x ⟨0, N.pos⟩ + (i.val : ℝ) / (N : ℝ)) = _
  ring

theorem hsEquispacedComparison_separation_bounds {N : ℕ+} (x : HsEuclidean N)
    {i j : Fin (N : ℕ)} (hij : i < j) :
    (N : ℝ)⁻¹ ≤ hsEquispacedComparison x j - hsEquispacedComparison x i ∧
      hsEquispacedComparison x j - hsEquispacedComparison x i ≤ 1 - (N : ℝ)⁻¹ := by
  rw [hsEquispacedComparison_separation]
  have hN : 0 < (N : ℝ) := by exact_mod_cast N.pos
  have hdiff : (1 : ℝ) ≤ (j.val : ℝ) - i.val := by
    have h : i.val + 1 ≤ j.val := hij
    have h' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast h
    linarith
  have htop : (j.val : ℝ) - i.val ≤ (N : ℝ) - 1 := by
    have hj : j.val + 1 ≤ (N : ℕ) := j.isLt
    have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    have hj' : (j.val : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hj
    linarith
  constructor
  · rw [← one_div]
    exact div_le_div_of_nonneg_right hdiff hN.le
  · apply (div_le_iff₀ hN).mpr
    rw [sub_mul, one_mul, inv_mul_cancel₀ hN.ne']
    exact htop

/-- A coarse bound, sufficient since no uniformity in the particle number is needed. -/
theorem norm_sub_hsEquispacedComparison_le {N : ℕ+} {x : HsEuclidean N}
    (hx : x ∈ hsChamber N) : ‖x - hsEquispacedComparison x‖ ≤ (N : ℝ) := by
  have hN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast N.pos
  have hc (i : Fin (N : ℕ)) : |(x - hsEquispacedComparison x) i| ≤ 1 := by
    have hi : (i.val : ℝ) / (N : ℝ) ∈ Ico (0 : ℝ) 1 := by
      refine ⟨by positivity, (div_lt_one (by positivity : 0 < (N : ℝ))).mpr ?_⟩
      exact_mod_cast i.isLt
    have hmono : x ⟨0, N.pos⟩ ≤ x i :=
      hx.1.monotone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
    have htop := hx.2 i
    change |x i - (x ⟨0, N.pos⟩ + (i.val : ℝ) / (N : ℝ))| ≤ 1
    rw [abs_le]
    constructor <;> linarith [hi.1, hi.2]
  have hsq : ‖x - hsEquispacedComparison x‖ ^ 2 ≤ (N : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc (∑ i, ((x - hsEquispacedComparison x) i) ^ 2) ≤
        ∑ _i : Fin (N : ℕ), (1 : ℝ) := by
          apply sum_le_sum
          intro i _
          nlinarith [abs_le.mp (hc i), sq_abs ((x - hsEquispacedComparison x) i)]
      _ = (N : ℝ) := by simp
  nlinarith [norm_nonneg (x - hsEquispacedComparison x)]

end Riesz1

end
