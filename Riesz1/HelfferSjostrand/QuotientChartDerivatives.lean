/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.InteriorRegularityQuotient
public import Riesz1.ToMathlib.EllipticRegularity.Translations

/-!
# Coherent weak derivatives on the cyclic quotient

The first and second derivatives of a local H² periodic lift have
pointwise periodic representatives. They agree on every translated chart,
and evaluation at the existing fundamental representative descends them
to actual functions on the configuration quotient.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- The chosen representative of a projected chamber point is its
integer translation into the existing half-open fundamental region. -/
theorem hsLiftPoint_chamberProjection {N : ℕ+} (x : hsChamber N) :
    hsLiftPoint N (hsChamberProjection x) =
      hsTranslate (-((⌊x.val ⟨0, N.pos⟩⌋ : ℤ) : ℝ)) x.val := by
  rw [← hsChamberProjection_representative x]
  change WithLp.toLp 2
    ((hsConfigurationEquiv N).symm ((hsConfigurationEquiv N) (hsRepresentative x))).val = _
  rw [Equiv.symm_apply_apply]
  ext i
  simp only [hsRepresentative_apply, hsTranslate_apply, sub_eq_add_neg]

/-- A pointwise periodic representative descends through the actual
quotient representative map, with equality at every chamber point. -/
theorem periodic_eq_comp_hsLiftPoint {N : ℕ+} {F : Type*} {g : HsEuclidean N → F}
    (hg : ∀ (k : ℤ) x, g (hsTranslate (k : ℝ) x) = g x) (x : hsChamber N) :
    g (hsLiftPoint N (hsChamberProjection x)) = g x.val := by
  rw [hsLiftPoint_chamberProjection]
  simpa only [Int.cast_neg] using hg (-⌊x.val ⟨0, N.pos⟩⌋) x.val

namespace Internal

/-- Quotient local H² admits coherent periodic first and second weak
derivatives. The last two identities give their literal descent to the
quotient, including charts crossing the rotation seam.
This supplies derivative representatives for interior regularity on the quotient. -/
theorem isLocalH2_quotient_periodic_derivatives {N : ℕ+} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {u : HsCylinder N → F}
    (hu : IsLocalH2 (hsChamber N) (fun x => u (QuotientAddGroup.mk x))) :
    ∃ (g : Fin (Module.finrank ℝ (HsEuclidean N)) → HsEuclidean N → F)
      (h : Fin (Module.finrank ℝ (HsEuclidean N)) →
        Fin (Module.finrank ℝ (HsEuclidean N)) → HsEuclidean N → F),
      (∀ i (k : ℤ) x, g i (hsTranslate (k : ℝ) x) = g i x) ∧
      (∀ i j (k : ℤ) x, h i j (hsTranslate (k : ℝ) x) = h i j x) ∧
      (∀ i, LocallySquareIntegrableOn (hsChamber N) (g i) ∧
        HasWeakDirectionalDerivativeOn (hsChamber N)
          (fun x => u (QuotientAddGroup.mk x)) (g i)
          (stdOrthonormalBasis ℝ (HsEuclidean N) i) ∧
        ∀ j, LocallySquareIntegrableOn (hsChamber N) (h i j) ∧
          HasWeakDirectionalDerivativeOn (hsChamber N) (g i) (h i j)
            (stdOrthonormalBasis ℝ (HsEuclidean N) j)) ∧
      (∀ i (x : hsChamber N),
        g i (hsLiftPoint N (hsChamberProjection x)) = g i x.val) ∧
      (∀ i j (x : hsChamber N),
        h i j (hsLiftPoint N (hsChamberProjection x)) = h i j x.val) := by
  let ℓ := EuclideanSpace.proj (𝕜 := ℝ) (⟨0, N.pos⟩ : Fin (N : ℕ))
  have hℓ : ℓ (hsRotationVector N) = 1 := by simp [ℓ, hsRotationVector]
  have hp (k : ℤ) (x : HsEuclidean N) :
      u (QuotientAddGroup.mk (x + (k : ℝ) • hsRotationVector N)) =
        u (QuotientAddGroup.mk x) := by
    congr 1
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    apply (hsPeriodLattice_mem_iff _).mpr
    refine ⟨k, fun i => ?_⟩
    change x i + (k : ℝ) * 1 - x i = (k : ℝ)
    ring
  obtain ⟨g, h, hgp, hhp, hd⟩ := hu.periodic_representatives
    (isOpen_hsChamber N) ℓ hℓ
    (fun k x => by rw [← hsTranslate_eq_add_rotation]; exact hsTranslate_mem_chamber_iff _ _) hp
  have hg (i) (k : ℤ) (x : HsEuclidean N) : g i (hsTranslate (k : ℝ) x) = g i x := by
    rw [hsTranslate_eq_add_rotation]
    exact hgp i k x
  have hh (i j) (k : ℤ) (x : HsEuclidean N) :
      h i j (hsTranslate (k : ℝ) x) = h i j x := by
    rw [hsTranslate_eq_add_rotation]
    exact hhp i j k x
  exact ⟨g, h, hg, hh, hd,
    fun i x => periodic_eq_comp_hsLiftPoint (hg i) x,
    fun i j x => periodic_eq_comp_hsLiftPoint (hh i j) x⟩

end Internal

end Riesz1
