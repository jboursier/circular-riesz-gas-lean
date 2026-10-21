/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SettingGeometry
public import Riesz1.ToMathlib.Chamber.Halfspaces

/-!
# The explicit collision-boundary distance

The distance is the smallest cyclic gap divided by
`√2`. Indexing by `n` below means `N = n + 2`, so both the adjacent and
the wrap-around faces have distinct coordinate normals.
-/

@[expose] public section

noncomputable section

open Set Metric

namespace Riesz1

/-- Collision faces: `some i` closes gap `i`, and `none` closes the wrap-around gap. -/
abbrev HsCollisionFace (n : ℕ) := Option (Fin (n + 1))

/-- Coordinate unit vectors, with their Euclidean carrier fixed explicitly. -/
def hsBasisVector (N : ℕ+) (i : Fin (N : ℕ)) : HsEuclidean N := PiLp.single 2 i 1

/-- The cyclic gaps before multiplication by the particle number. -/
def hsCollisionGap (n : ℕ) (x : HsEuclidean (n + 1).succPNat) : HsCollisionFace n → ℝ
  | none => 1 + x 0 - x (Fin.last (n + 1))
  | some i => x i.succ - x i.castSucc

/-- Unit outward normals to the collision faces. -/
def hsCollisionNormal (n : ℕ) : HsCollisionFace n → HsEuclidean (n + 1).succPNat
  | none => (Real.sqrt 2)⁻¹ •
      (hsBasisVector (n + 1).succPNat (Fin.last (n + 1)) - hsBasisVector (n + 1).succPNat 0)
  | some i => (Real.sqrt 2)⁻¹ •
      (hsBasisVector (n + 1).succPNat i.castSucc - hsBasisVector (n + 1).succPNat i.succ)

/-- Offsets for the unit normals. -/
def hsCollisionOffset (n : ℕ) : HsCollisionFace n → ℝ
  | none => (Real.sqrt 2)⁻¹
  | some _ => 0

theorem hsCollisionNormal_norm (n : ℕ) (i : HsCollisionFace n) :
    ‖hsCollisionNormal n i‖ = 1 := by
  have hn {j k : Fin ((n + 1).succPNat : ℕ)} (hjk : j ≠ k) :
      ‖(hsBasisVector _ j - hsBasisVector _ k : HsEuclidean (n + 1).succPNat)‖ =
        Real.sqrt 2 := by
    have hh : ‖(hsBasisVector _ j - hsBasisVector _ k : HsEuclidean (n + 1).succPNat)‖ ^ 2 =
        (2 : ℝ) := by
      rw [norm_sub_sq_real]
      norm_num [hsBasisVector, PiLp.norm_single, EuclideanSpace.inner_single_left, hjk]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ),
      norm_nonneg (hsBasisVector _ j - hsBasisVector _ k : HsEuclidean (n + 1).succPNat)]
  have hpos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  cases i with
  | none =>
    erw [hsCollisionNormal, norm_smul, hn (by
      intro h
      have hh := congrArg Fin.val h
      change n + 1 = 0 at hh
      omega), Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
  | some i =>
    erw [hsCollisionNormal, norm_smul, hn (ne_of_lt Fin.castSucc_lt_succ),
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']

theorem hsCollision_margin (n : ℕ) (x : HsEuclidean (n + 1).succPNat)
    (i : HsCollisionFace n) :
    hsCollisionOffset n i - inner ℝ (hsCollisionNormal n i) x =
      hsCollisionGap n x i / Real.sqrt 2 := by
  cases i <;>
    erw [hsCollisionOffset, hsCollisionNormal, inner_smul_left, inner_sub_left,
      show inner ℝ (hsBasisVector _ _) x = _ from EuclideanSpace.inner_single_left _ 1 x,
      show inner ℝ (hsBasisVector _ _) x = _ from EuclideanSpace.inner_single_left _ 1 x] <;>
    simp only [hsCollisionGap, starRingEnd_apply, star_trivial, one_mul, div_eq_mul_inv] <;> ring

theorem hsChamber_iff_collisionGaps_pos (n : ℕ) (x : HsEuclidean (n + 1).succPNat) :
    x ∈ hsChamber (n + 1).succPNat ↔ ∀ i, 0 < hsCollisionGap n x i := by
  constructor
  · rintro ⟨hm, hb⟩ i
    cases i with
    | none =>
      have := hb (Fin.last (n + 1))
      change x (Fin.last (n + 1)) < x 0 + 1 at this
      change 0 < 1 + x 0 - x (Fin.last (n + 1))
      linarith
    | some i => exact sub_pos.mpr (hm Fin.castSucc_lt_succ)
  · intro h
    have hm : StrictMono x := Fin.strictMono_iff_lt_succ.mpr (fun i => sub_pos.mp (h (some i)))
    refine ⟨hm, fun i => ?_⟩
    have hb := h none
    change 0 < 1 + x 0 - x (Fin.last (n + 1)) at hb
    change x i < x 0 + 1
    have := hm.monotone (Fin.le_last i)
    linarith

theorem hsChamber_eq_finiteOpenChamber (n : ℕ) :
    hsChamber (n + 1).succPNat = finiteOpenChamber (hsCollisionNormal n) (hsCollisionOffset n) := by
  ext x
  rw [hsChamber_iff_collisionGaps_pos]
  change (∀ i, 0 < hsCollisionGap n x i) ↔ ∀ i,
    inner ℝ (hsCollisionNormal n i) x < hsCollisionOffset n i
  have hpos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  constructor
  · intro h i
    apply sub_pos.mp
    rw [hsCollision_margin]
    exact div_pos (h i) hpos
  · intro h i
    have hi := sub_pos.mpr (h i)
    rw [hsCollision_margin] at hi
    exact (div_pos_iff_of_pos_right hpos).mp hi

/-- The explicit distance formula, with the finite minimum written using its face indices. -/
theorem hsBoundaryDistance_eq_min_gap (n : ℕ) {x : HsEuclidean (n + 1).succPNat}
    (hx : x ∈ hsChamber (n + 1).succPNat) :
    hsBoundaryDistance (n + 1).succPNat (by change 2 ≤ n + 1 + 1; omega) x =
      (Finset.univ.image (fun i : HsCollisionFace n => hsCollisionGap n x i / Real.sqrt 2)).min'
        (Finset.univ_nonempty.image _) := by
  change infDist x (hsChamber (n + 1).succPNat)ᶜ = _
  rw [hsChamber_eq_finiteOpenChamber] at hx ⊢
  rw [infDist_compl_finiteOpenChamber _ _ (hsCollisionNormal_norm n) hx]
  unfold finiteChamberMargin
  simp_rw [hsCollision_margin]

end Riesz1

end
