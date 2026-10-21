/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BoundarySelectionGeometry
public import Riesz1.Rigidity.NoExplosionIntegration

/-!
# Rotation windows for a boundary-selected label

An exact deterministic description of the event that a boundary selects
a specified cyclic label, using the fractional part of its displacement.
This is used in the proof of the boundary selection bound in Theorem 1.
-/

public section

open Set

namespace Riesz1

/-- Arbitrary winding shifts of cyclic lifts. -/
theorem boundary_cyclicLift_add_mul {N : ℕ+} (X : Configuration N) (j q : ℤ) :
    cyclicLift X (j + ((N : ℕ) : ℤ) * q) = cyclicLift X j + q := by
  obtain ⟨i, hi, k, rfl⟩ := exists_nat_add_mul (N := N) j
  rw [show (i : ℤ) + (N : ℕ) * k + (N : ℕ) * q =
    i + (N : ℕ) * (k + q) by ring, cyclicLift_add_mul X hi, cyclicLift_add_mul X hi]
  push_cast
  ring

/-- A specified cyclic label is selected exactly on its fractional rotation window.
The weak inequality at a coincident left endpoint is retained. -/
theorem precedingLabel_cyclic_iff_fract {N : ℕ+} (hN : 2 ≤ (N : ℕ))
    (a : UnitAddCircle) (ℓ : ℝ) (X : Configuration N) (j : ℤ) :
    (∃ q : ℤ, precedingLabel a ℓ X = j + ((N : ℕ) : ℤ) * q) ↔
      Int.fract (leftLift a ℓ - cyclicLift X j) < gap X j / (N : ℝ) := by
  have hNr : (0 : ℝ) < (N : ℕ) := by exact_mod_cast N.pos
  have hg : gap X j / (N : ℝ) = cyclicLift X (j + 1) - cyclicLift X j := by
    unfold gap
    field_simp
  have hlt := gap_lt_particle_number hN X j
  have hlen : cyclicLift X (j + 1) - cyclicLift X j < 1 := by
    have hh := (div_lt_one hNr).mpr hlt
    rwa [hg] at hh
  have hb := leftLift_mem a ℓ
  rw [hg]
  constructor
  · rintro ⟨q, hq⟩
    have hspec := preceding_spec X hb.1 hb.2
    change cyclicLift X (precedingLabel a ℓ X) ≤ leftLift a ℓ ∧
      leftLift a ℓ < cyclicLift X (precedingLabel a ℓ X + 1) at hspec
    rw [hq, boundary_cyclicLift_add_mul,
      show j + (N : ℕ) * q + 1 = (j + 1) + (N : ℕ) * q by ring,
      boundary_cyclicLift_add_mul] at hspec
    have hfloor : ⌊leftLift a ℓ - cyclicLift X j⌋ = q := Int.floor_eq_iff.mpr
      ⟨by linarith [hspec.1], by linarith [hspec.2]⟩
    rw [Int.fract, hfloor]
    linarith [hspec.2]
  · intro h
    refine ⟨⌊leftLift a ℓ - cyclicLift X j⌋, ?_⟩
    apply (preceding_eq_iff X hb.1 hb.2 _).mpr
    rw [boundary_cyclicLift_add_mul,
      show j + (N : ℕ) * ⌊leftLift a ℓ - cyclicLift X j⌋ + 1 =
        (j + 1) + (N : ℕ) * ⌊leftLift a ℓ - cyclicLift X j⌋ by ring,
      boundary_cyclicLift_add_mul]
    dsimp only [Int.fract] at h
    exact ⟨by linarith [Int.floor_le (leftLift a ℓ - cyclicLift X j)], by linarith⟩

end Riesz1
