/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GeometryLawProduct

/-!
# Bijection and local isometry of the Gibbs coordinates

The map `x ↦ (z, ω)` is a bijection onto `B_N × (ℝ/√N ℤ)` and a local
isometry. The bijection is stated on `Configuration N`, the carrier of the Gibbs probability. The
local isometry is stated on the lift, with the `L²` product distance `√(d₁² + d₂²)` on
`e^⊥ × AddCircle (√N)`. It holds at every lift point with radius `√N / 4`: the orthogonal part
is a Euclidean isometry, and the circle distance equals the Euclidean distance of the
`t`-coordinates on windows shorter than `√N / 2`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Submodule

namespace Riesz1

variable {N : ℕ+}

/-- The `L²` product distance `√(d₁² + d₂²)` on `e^⊥ × AddCircle (√N)`. -/
def hsProductDist (p q : hsOrthSubspace N × AddCircle (Real.sqrt (N : ℕ))) : ℝ :=
  Real.sqrt (dist p.1 q.1 ^ 2 + dist p.2 q.2 ^ 2)

theorem hsOrthComp_coe (N : ℕ+) (x : HsEuclidean N) :
    (hsOrthComp N x : HsEuclidean N) = x - inner ℝ x (hsUnitVector N) • hsUnitVector N :=
  rfl

theorem inner_add_smul_hsUnitVector {z : HsEuclidean N} (hz : z ∈ hsOrthSubspace N) (t : ℝ) :
    inner ℝ (z + t • hsUnitVector N) (hsUnitVector N) = t := by
  rw [mem_orthogonal_singleton_iff_inner_left] at hz
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hsUnitVector_norm, hz]
  ring

theorem hsOrthComp_add_smul_of_mem {z : HsEuclidean N} (hz : z ∈ hsOrthSubspace N) (t : ℝ) :
    hsOrthComp N (z + t • hsUnitVector N) = ⟨z, hz⟩ := by
  apply Subtype.ext
  change (z + t • hsUnitVector N) - inner ℝ (z + t • hsUnitVector N) (hsUnitVector N) •
    hsUnitVector N = z
  rw [inner_add_smul_hsUnitVector hz]
  abel

theorem hsOrthComp_sub (N : ℕ+) (y y' : HsEuclidean N) :
    (hsOrthComp N y : HsEuclidean N) - (hsOrthComp N y' : HsEuclidean N) =
      (hsOrthComp N (y - y') : HsEuclidean N) := by
  rw [hsOrthComp_coe, hsOrthComp_coe, hsOrthComp_coe, inner_sub_left, sub_smul]
  abel

/-- Pythagoras on `e^⊥ ⊕ ℝ e`: the squared norm splits into the orthogonal part and the square of
the coordinate along `e`. -/
theorem norm_sq_hsOrthComp (N : ℕ+) (w : HsEuclidean N) :
    ‖w‖ ^ 2 = ‖(hsOrthComp N w : HsEuclidean N)‖ ^ 2 + inner ℝ w (hsUnitVector N) ^ 2 := by
  have hw := hsOrthComp_add_smul N w
  have hperp : inner ℝ (hsOrthComp N w : HsEuclidean N)
      (inner ℝ w (hsUnitVector N) • hsUnitVector N) = 0 := by
    have h := (mem_orthogonal_singleton_iff_inner_left.mp (hsOrthComp N w).2)
    rw [real_inner_smul_right, h, mul_zero]
  conv_lhs => rw [← hw]
  rw [norm_add_sq_real, hperp, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hsUnitVector_norm,
    one_pow, mul_one]
  ring

theorem sqrt_N_pos (N : ℕ+) : 0 < Real.sqrt (N : ℕ) :=
  Real.sqrt_pos.mpr (Nat.cast_pos.mpr N.pos)

/-- The circle distance of two angles is the Euclidean distance of the `t`-coordinates when
`‖y - y'‖ < √N / 2`. -/
theorem dist_hsAngle_eq (N : ℕ+) {y y' : HsEuclidean N}
    (hyy : ‖y - y'‖ < Real.sqrt (N : ℕ) / 2) :
    dist (hsAngle N y) (hsAngle N y') = |inner ℝ (y - y') (hsUnitVector N)| := by
  have hT : Real.sqrt (N : ℕ) ≠ 0 := (sqrt_N_pos N).ne'
  have hb : |inner ℝ (y - y') (hsUnitVector N)| ≤ |Real.sqrt (N : ℕ)| / 2 := by
    have h := abs_real_inner_le_norm (y - y') (hsUnitVector N)
    rw [hsUnitVector_norm, mul_one] at h
    rw [abs_of_pos (sqrt_N_pos N)]
    linarith
  rw [hsAngle, hsAngle, dist_eq_norm, ← QuotientAddGroup.mk_sub, ← inner_sub_left]
  exact (AddCircle.norm_coe_eq_abs_iff _ hT).mpr hb

/-- Two lift points with the same orthogonal part and the same circle coordinate, and with first
coordinates in `[0, 1)`, coincide. This is the injectivity of the coordinates on the fundamental
region. -/
theorem eq_of_hsCoord_eq {x y : HsEuclidean N} (hz : hsOrthComp N x = hsOrthComp N y)
    (hw : hsAngle N x = hsAngle N y) (hx0 : 0 ≤ x ⟨0, N.pos⟩) (hx1 : x ⟨0, N.pos⟩ < 1)
    (hy0 : 0 ≤ y ⟨0, N.pos⟩) (hy1 : y ⟨0, N.pos⟩ < 1) : x = y := by
  have hT : Real.sqrt (N : ℕ) ≠ 0 := (sqrt_N_pos N).ne'
  have hzy : (hsOrthComp N x : HsEuclidean N) = (hsOrthComp N y : HsEuclidean N) :=
    congrArg Subtype.val hz
  have hx := (hsOrthComp_add_smul N x).symm
  have hy := (hsOrthComp_add_smul N y).symm
  rw [← hzy] at hy
  -- the circle equality gives an integer multiple of the period
  have h0 : ((inner ℝ x (hsUnitVector N) - inner ℝ y (hsUnitVector N) : ℝ) :
      AddCircle (Real.sqrt (N : ℕ))) = 0 := by
    rw [QuotientAddGroup.mk_sub, sub_eq_zero]
    exact hw
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).mp h0
  have hk' : (k : ℝ) * Real.sqrt (N : ℕ) = inner ℝ x (hsUnitVector N) - inner ℝ y (hsUnitVector N) := by
    rw [← zsmul_eq_mul]
    exact hk
  -- the first coordinates differ by the integer `k`
  have hx0' := add_smul_hsUnitVector_apply_zero N (hsOrthComp N x : HsEuclidean N)
    (inner ℝ x (hsUnitVector N))
  rw [← hx] at hx0'
  have hy0' := add_smul_hsUnitVector_apply_zero N (hsOrthComp N x : HsEuclidean N)
    (inner ℝ y (hsUnitVector N))
  rw [← hy] at hy0'
  have hdiff : x ⟨0, N.pos⟩ - y ⟨0, N.pos⟩ = (k : ℝ) := by
    have hm : x ⟨0, N.pos⟩ - y ⟨0, N.pos⟩ =
        (inner ℝ x (hsUnitVector N) - inner ℝ y (hsUnitVector N)) * (Real.sqrt (N : ℕ))⁻¹ := by
      rw [hx0', hy0']
      ring
    rw [hm, ← hk', mul_inv_cancel_right₀ hT]
  have hk1 : k < 1 := by
    have : (k : ℝ) < 1 := by linarith
    exact_mod_cast this
  have hk2 : -1 < k := by
    have : (-1 : ℝ) < k := by linarith
    exact_mod_cast this
  have hk0 : k = 0 := by omega
  rw [hk0, Int.cast_zero, zero_mul] at hk'
  have hts : inner ℝ x (hsUnitVector N) = inner ℝ y (hsUnitVector N) := by
    linarith
  calc x = (hsOrthComp N x : HsEuclidean N) + inner ℝ x (hsUnitVector N) • hsUnitVector N := hx
    _ = (hsOrthComp N x : HsEuclidean N) + inner ℝ y (hsUnitVector N) • hsUnitVector N := by
      rw [hts]
    _ = y := hy.symm

/-- The `L²` product distance of two coordinate images is the distance of the lift points, for
lift points at distance less than `√N / 2`. -/
theorem hsProductDist_hsCoord {y y' : HsEuclidean N} (hyy : ‖y - y'‖ < Real.sqrt (N : ℕ) / 2) :
    hsProductDist (hsCoord N y) (hsCoord N y') = dist y y' := by
  have h1 : dist (hsOrthComp N y) (hsOrthComp N y') =
      ‖(hsOrthComp N (y - y') : HsEuclidean N)‖ := by
    rw [Subtype.dist_eq, dist_eq_norm, hsOrthComp_sub]
  have h2 : dist (hsAngle N y) (hsAngle N y') = |inner ℝ (y - y') (hsUnitVector N)| :=
    dist_hsAngle_eq N hyy
  change Real.sqrt (dist (hsOrthComp N y) (hsOrthComp N y') ^ 2 +
    dist (hsAngle N y) (hsAngle N y') ^ 2) = dist y y'
  rw [h1, h2, sq_abs, dist_eq_norm, ← norm_sq_hsOrthComp N (y - y'), Real.sqrt_sq (norm_nonneg _)]

/-- Local isometry of the coordinates `(z, ω)`: every lift point has a ball of radius `√N / 4`
on which the coordinate map preserves distances to the `L²` product of `e^⊥` and the circle. -/
theorem hsCoord_isLocalIsometry (N : ℕ+) (x : HsEuclidean N) :
    ∃ ε > 0, ∀ y ∈ ball x ε, ∀ y' ∈ ball x ε,
      hsProductDist (hsCoord N y) (hsCoord N y') = dist y y' := by
  refine ⟨Real.sqrt (N : ℕ) / 4, by linarith [sqrt_N_pos N], fun y hy y' hy' => ?_⟩
  apply hsProductDist_hsCoord
  rw [← dist_eq_norm]
  have hy1 : dist y x < Real.sqrt (N : ℕ) / 4 := hy
  have hy2 : dist y' x < Real.sqrt (N : ℕ) / 4 := hy'
  linarith [dist_triangle y x y', dist_comm y' x]

/-- The coordinate map is a bijection of the fundamental region onto the radial domain times the
circle, with the inverse given by the affine splitting `(z, ω) ↦ z + t e` with `t ≡ ω`. -/
theorem hsConfigCoord_bijOn (N : ℕ+) :
    BijOn (hsConfigCoord N) univ (hsRadialDomain N ×ˢ univ) := by
  refine ⟨fun X _ => ⟨hsConfigCoord_fst_mem N X, mem_univ _⟩, ?_, ?_⟩
  · intro X _ Y _ hXY
    have hz : hsOrthComp N (WithLp.toLp 2 X.val) = hsOrthComp N (WithLp.toLp 2 Y.val) :=
      congrArg Prod.fst hXY
    have hw : hsAngle N (WithLp.toLp 2 X.val) = hsAngle N (WithLp.toLp 2 Y.val) :=
      congrArg Prod.snd hXY
    have hxy := eq_of_hsCoord_eq hz hw (X.property.2.1) (X.property.2.2.1)
      (Y.property.2.1) (Y.property.2.2.1)
    apply Subtype.ext
    simpa using congrArg WithLp.ofLp hxy
  · rintro ⟨z, w⟩ ⟨hz, -⟩
    obtain ⟨t₀, rfl⟩ := QuotientAddGroup.mk_surjective w
    have hT : 0 < Real.sqrt (N : ℕ) := sqrt_N_pos N
    -- the representative of `t₀` in the window `[a, a + √N)`
    have hk := self_sub_toIcoDiv_zsmul (p := Real.sqrt (N : ℕ)) hT
      (-(Real.sqrt (N : ℕ) * (z : HsEuclidean N) ⟨0, N.pos⟩)) t₀
    have ht := toIcoMod_mem_Ico (p := Real.sqrt (N : ℕ)) hT
      (-(Real.sqrt (N : ℕ) * (z : HsEuclidean N) ⟨0, N.pos⟩)) t₀
    set t := toIcoMod hT (-(Real.sqrt (N : ℕ) * (z : HsEuclidean N) ⟨0, N.pos⟩)) t₀ with htdef
    have hcong : ((t : ℝ) : AddCircle (Real.sqrt (N : ℕ))) = ((t₀ : ℝ) : AddCircle _) := by
      refine QuotientAddGroup.eq.mpr (AddSubgroup.mem_zmultiples_iff.mpr
        ⟨toIcoDiv hT (-(Real.sqrt (N : ℕ) * (z : HsEuclidean N) ⟨0, N.pos⟩)) t₀, ?_⟩)
      rw [← hk]
      abel
    have hfund : (z : HsEuclidean N) + t • hsUnitVector N ∈ hsFundamentalRegion N :=
      (add_smul_mem_hsFundamentalRegion_iff N z t).mpr ⟨hz, ht⟩
    have hmem : WithLp.ofLp ((z : HsEuclidean N) + t • hsUnitVector N) ∈ orderedDomain N := by
      have h := hfund
      rw [hsFundamentalRegion_eq_preimage N] at h
      exact h
    refine ⟨⟨WithLp.ofLp ((z : HsEuclidean N) + t • hsUnitVector N), hmem⟩, mem_univ _, ?_⟩
    refine Prod.ext ?_ ?_
    · change hsOrthComp N (WithLp.toLp 2 (WithLp.ofLp ((z : HsEuclidean N) + t • hsUnitVector N))) =
        z
      rw [WithLp.toLp_ofLp, hsOrthComp_add_smul_of_mem z.2 t]
    · change hsAngle N (WithLp.toLp 2 (WithLp.ofLp ((z : HsEuclidean N) + t • hsUnitVector N))) =
        ((t₀ : ℝ) : AddCircle (Real.sqrt (N : ℕ)))
      rw [WithLp.toLp_ofLp, hsAngle, inner_add_smul_hsUnitVector z.2 t, hcong]

end Riesz1

end
