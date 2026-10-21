/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.CurvatureGaps
public import Riesz1.HelfferSjostrand.BlockConcentrationProduct

/-!
# The linear chart between internal gaps and the radial block chamber

The inverse of the gap map is the cumulative section
followed by orthogonal projection. This chart removes exactly the free
rotation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Riesz1

/-- The existing radial coordinate is the bundled orthogonal projection. -/
theorem hsOrthComp_eq_projection (M : ℕ+) (x : HsEuclidean M) :
    hsOrthComp M x = (hsOrthSubspace M).orthogonalProjectionOnto x := by
  apply Subtype.ext
  exact orthComponent_eq_starProjection (hsUnitVector_norm M) x

/-- Common translation leaves every internal gap unchanged. -/
theorem internalBlockGaps_translate (N : ℕ+) (L : ℕ) (t : ℝ)
    (z : HsEuclidean L.succPNat) :
    internalBlockGaps N L (hsTranslate t z) = internalBlockGaps N L z := by
  ext i
  change (N : ℝ) * ((z i.succ + t) - (z i.castSucc + t)) = _
  change _ = (N : ℝ) * (z i.succ - z i.castSucc)
  ring

namespace Internal

theorem curvature_translate_unit (M : ℕ+) (t : ℝ) (z : HsEuclidean M) :
    hsTranslate t z = z + (t * Real.sqrt (M : ℕ)) • hsUnitVector M := by
  have hs : Real.sqrt (M : ℕ) ≠ 0 := (sqrt_N_pos M).ne'
  ext i
  simp only [hsTranslate_apply, hsUnitVector, hsRotationVector, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  field_simp

end Internal

/-- The cumulative gap section, followed by removing the mean, is a linear isomorphism. -/
def internalGapRadialEquiv (N : ℕ+) (L : ℕ) :
    EuclideanSpace ℝ (Fin L) ≃ₗ[ℝ] hsOrthSubspace L.succPNat where
  toFun := fun v => (hsOrthSubspace L.succPNat).orthogonalProjectionOnto (internalGapSection N L v)
  invFun := fun z => internalBlockGaps N L z.val
  map_add' := by intro v w; rw [map_add, map_add]
  map_smul' := by intro a v; rw [map_smul, map_smul]; rfl
  left_inv := by
    intro v
    change internalBlockGaps N L
      ((hsOrthSubspace L.succPNat).orthogonalProjectionOnto (internalGapSection N L v)) = v
    rw [← hsOrthComp_eq_projection]
    change internalBlockGaps N L (hsOrthProj L.succPNat (internalGapSection N L v)) = v
    rw [hsOrthProj_eq_translate, internalBlockGaps_translate, internalBlockGaps_section]
  right_inv := by
    intro z
    change (hsOrthSubspace L.succPNat).orthogonalProjectionOnto
      (internalGapSection N L (internalBlockGaps N L z.val)) = z
    rw [← hsOrthComp_eq_projection]
    have he : internalGapSection N L (internalBlockGaps N L z.val) =
        hsTranslate (-z.val 0) z.val := by
      ext r
      rw [internalGapSection_reconstruct]
      simp only [hsTranslate_apply, sub_eq_add_neg]
    rw [he, Internal.curvature_translate_unit]
    exact hsOrthComp_add_smul_of_mem z.property _

/-- The inverse chart is literally the internal gap map. -/
theorem internalGapRadialEquiv_symm (N : ℕ+) (L : ℕ) (z : hsOrthSubspace L.succPNat) :
    (internalGapRadialEquiv N L).symm z = internalBlockGaps N L z.val := rfl

/-- The chart uses the specified section modulo a common real translation. -/
theorem internalGapRadialEquiv_apply (N : ℕ+) (L : ℕ) (v : EuclideanSpace ℝ (Fin L)) :
    internalGapRadialEquiv N L v = hsOrthComp L.succPNat (internalGapSection N L v) := by
  exact (hsOrthComp_eq_projection _ _).symm

/-- The gap domain is exactly the inverse image of the radial chamber. -/
theorem internalGapRadialEquiv_mem (N : ℕ+) (L : ℕ) (v : EuclideanSpace ℝ (Fin L)) :
    internalGapRadialEquiv N L v ∈ hsRadialDomain L.succPNat ↔ v ∈ internalGapDomain N L := by
  rw [internalGapRadialEquiv_apply]
  change hsOrthProj L.succPNat (internalGapSection N L v) ∈ hsChamber L.succPNat ↔ _
  rw [hsOrthProj_eq_translate, hsTranslate_mem_chamber_iff]
  rfl

end Riesz1

end
