/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityMembership
public import Riesz1.ToMathlib.MollifierPointwise.Circle
public import Riesz1.Frozen.UnitLength
public import Riesz1.Frozen.TransportCoeffs
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Length one and the unit circle (Theorem 3)

At scale one the observation circle `Circle (observationLength a)` has length `a⁻¹ = 1`, but its
type is not syntactically `Circle unitLength`. The lemmas here move the objects of the CLT
(periodized profile, transport, mollification, Fourier coefficients) between the two circles.
Each one takes a general `L : Length` with `L.val = 1`. The proof destructs `L` and substitutes,
so the circles become `unitLength` definitionally.

The periodization at length one agrees with the profile `p` on the open central interval
`|x| < 1/2`, which is a set of full measure, so Fourier coefficients agree
(`coeff_periodizedProfile_eq_unit`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1.Internal

/-- At length one the periodization of `p` is `p` on the open central interval. -/
lemma periodizedProfile_eq_of_abs_lt (p : Profile) (L : Length) (hL : L.val = 1) {x : ℝ}
    (hx : |x| < 1 / 2) :
    periodizedProfile p L (x : Circle L) = p.val (x : UnitAddCircle) := by
  have hL1 : 1 ≤ L.val := hL.ge
  rw [admissibility_periodizedProfile_eq_zeroExtension p L hL1]
  have hrep : centralRep L (x : Circle L) = x := by
    have : Fact (0 < L.val) := ⟨L.property⟩
    obtain ⟨h1, h2⟩ := abs_lt.mp hx
    have hmem : x ∈ Ico (-L.val / 2) (-L.val / 2 + L.val) := by
      rw [Set.mem_Ico, hL]
      constructor <;> linarith
    unfold centralRep
    exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hmem)
  rw [hrep]
  unfold zeroExtension
  simp only [hx, ↓reduceIte]

/-- The Fourier coefficients of the periodized profile at length one are those of `p`. -/
lemma coeff_periodizedProfile_eq_unit (p : Profile) (L : Length) (hL : L.val = 1)
    (hf : MemLp (fun x => (periodizedProfile p L x : ℂ)) 2 (arclength L)) (k : ℤ) :
    coeff L ⟨fun x => (periodizedProfile p L x : ℂ), complexL2Integrable L _ hf⟩ k =
      coeff unitLength ⟨fun x => (p.val x : ℂ), complexL2Integrable unitLength _ p.property⟩ k := by
  obtain ⟨v, hv⟩ := L
  change v = 1 at hL
  subst hL
  have : Fact (0 < unitLength.val) := ⟨unitLength.property⟩
  unfold coeff
  rw [fourierCoeff_eq_intervalIntegral _ k (-(1 / 2)),
    fourierCoeff_eq_intervalIntegral _ k (-(1 / 2))]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(ae_iff.2 (by simp) : ∀ᵐ y : ℝ, y ≠ 1 / 2)] with y hy hyI
  rw [Set.uIoc_of_le (by norm_num)] at hyI
  have hyabs : |y| < 1 / 2 := by
    rw [abs_lt]
    have h2 : y ≤ 1 / 2 := by linarith [hyI.2]
    exact ⟨by linarith [hyI.1], lt_of_le_of_ne h2 hy⟩
  rw [periodizedProfile_eq_of_abs_lt p ⟨1, hv⟩ rfl hyabs]
  rfl

/-- Transport coefficients at length one are those of the unit circle. -/
lemma transportCoeffs_periodizedProfile_eq_unit (P : Parameters) (p : Profile) (L : Length)
    (hL : L.val = 1) (hf : MemLp (fun x => (periodizedProfile p L x : ℂ)) 2 (arclength L))
    (k : ℤ) :
    transportCoeffs P L ⟨periodizedProfile p L, hf⟩ k =
      transportCoeffs P unitLength ⟨p.val, p.property⟩ k := by
  obtain ⟨v, hv⟩ := L
  change v = 1 at hL
  subst hL
  unfold transportCoeffs
  by_cases hk : k = 0
  · simp only [hk, ite_true]
  · simp only [hk, ite_false]
    rw [coeff_periodizedProfile_eq_unit p ⟨1, hv⟩ rfl hf k]
    rfl

/-- A subtype function on the unit circle transfers to any circle of length one: the transferred
function has the same lift and the same Fourier coefficients. -/
lemma exists_transfer_of_val_one (L : Length) (hL : L.val = 1)
    (φ : {f : Circle unitLength → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength unitLength)}) :
    ∃ ψ : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
      (∀ x : ℝ, ψ.val (x : Circle L) = φ.val (x : Circle unitLength)) ∧
      (Continuous ψ.val ↔ Continuous φ.val) ∧
      (∀ k : ℤ, coeff L ⟨fun x => (ψ.val x : ℂ), complexL2Integrable L _ ψ.property⟩ k =
        coeff unitLength ⟨fun x => (φ.val x : ℂ), complexL2Integrable unitLength _ φ.property⟩ k) := by
  obtain ⟨v, hv⟩ := L
  change v = 1 at hL
  subst hL
  exact ⟨φ, fun x => rfl, Iff.rfl, fun k => rfl⟩

/-- The mollification at length one is the mollification of the transferred function. -/
lemma circleMollify_eq_of_val_one (ρ : ℝ → ℝ) (L : Length) (hL : L.val = 1) (h : ℝ)
    (ψ : Circle L → ℝ) (φ : Circle unitLength → ℝ)
    (hψφ : ∀ x : ℝ, ψ (x : Circle L) = φ (x : Circle unitLength)) (x : ℝ) :
    circleMollify ρ L.val h (fun t : ℝ => ψ (t : Circle L)) x =
      circleMollify ρ 1 h (fun t : ℝ => φ (t : Circle unitLength)) x := by
  obtain ⟨v, hv⟩ := L
  change v = 1 at hL
  subst hL
  have hfun : (fun t : ℝ => ψ (t : Circle ⟨1, hv⟩)) = fun t : ℝ => φ (t : Circle unitLength) :=
    funext hψφ
  rw [hfun]

/-- The distance of two points of a circle of length one does not depend on the circle type. -/
lemma dist_circle_eq_of_val_one (L : Length) (hL : L.val = 1) (x m : ℝ) :
    dist (x : Circle L) (m : Circle L) = dist (x : Circle unitLength) (m : Circle unitLength) := by
  obtain ⟨v, hv⟩ := L
  change v = 1 at hL
  subst hL
  rfl

end Riesz1.Internal

end
end
