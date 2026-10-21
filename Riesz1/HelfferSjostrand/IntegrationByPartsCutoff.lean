/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SobolevSeam
public import Riesz1.ToMathlib.Chamber.PeriodicCutoff

/-!
# Localizing periodic derivatives on the Euclidean cover

The smooth partition under integer translations turns a periodic
collision-separated coefficient into a compact interior test. Thus the
weighted weak identity applies to derivatives of the test class.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped ContDiff

namespace Riesz1

/-- A cutoff in the rotation coordinate makes chamber-supported functions compact. -/
theorem hasCompactSupport_hsPeriodicCutoff_mul {N : ℕ+} {g : HsEuclidean N → ℝ}
    (hg : tsupport g ⊆ hsChamber N) :
    HasCompactSupport (fun x => periodicCutoff (x ⟨0, N.pos⟩) * g x) := by
  let e := PiLp.homeomorph 2 (fun _ : Fin (N : ℕ) => ℝ)
  let K := e.symm '' Icc (fun _ => (-1 : ℝ)) (fun _ => (2 : ℝ))
  have hK : IsCompact K := isCompact_Icc.image e.symm.continuous
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro x hx
  have hxg : g x ≠ 0 := (mul_ne_zero_iff.mp hx).2
  have hxc := hg (subset_closure hxg)
  have hxt : periodicCutoff (x ⟨0, N.pos⟩) ≠ 0 := (mul_ne_zero_iff.mp hx).1
  have hlo : (-1 : ℝ) ≤ x ⟨0, N.pos⟩ := by
    by_contra hh
    exact hxt (periodicCutoff_eq_zero (Or.inl (le_of_lt (lt_of_not_ge hh))))
  have hhi : x ⟨0, N.pos⟩ ≤ (1 : ℝ) := by
    by_contra hh
    exact hxt (periodicCutoff_eq_zero (Or.inr (le_of_lt (lt_of_not_ge hh))))
  refine ⟨WithLp.ofLp x, ⟨?_, ?_⟩, rfl⟩
  · intro i
    exact hlo.trans (hxc.1.monotone (Fin.zero_le i))
  · intro i
    linarith [hxc.2 i]

/-- The completed weak identity with a derivative of an actual test. -/
theorem hsSobolev_test_directional_integrationByParts {N : ℕ+} {c : ℝ}
    (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : HsTestFunction N)
    (h : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (v : HsEuclidean N) :
    ∫ x, hsSmoothValue (fun y => fderiv ℝ f.toFun y v) x *
        inner ℝ (hsSobolevGradient
          (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) h x) v
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) =
      ∫ x, hsSobolevValue
          (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) h x *
        hsSmoothValue (fun y => fderiv ℝ f.toFun y v * fderiv ℝ (hsPairExpression χ) y v -
          fderiv ℝ (fun z => fderiv ℝ f.toFun z v) y v) x
          ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
  let g := fun y => fderiv ℝ f.toFun y v
  let ℓ := EuclideanSpace.proj (𝕜 := ℝ) (⟨0, N.pos⟩ : Fin (N : ℕ))
  let ψ := fun y => periodicCutoff (ℓ y) * g y
  have hg : ContDiff ℝ ∞ g :=
    (contDiff_infty_iff_fderiv.mp f.smooth).2.clm_apply contDiff_const
  have hgU : tsupport g ⊆ hsChamber N :=
    (tsupport_fderiv_apply_subset ℝ v).trans (f.tsupport_subset_chamber hN)
  have hψc : HasCompactSupport ψ := hasCompactSupport_hsPeriodicCutoff_mul hgU
  have hψ : ContDiff ℝ ∞ ψ := (contDiff_periodicCutoff.comp ℓ.contDiff).mul hg
  have hψU : tsupport ψ ⊆ hsChamber N := tsupport_mul_subset_right.trans hgU
  have hgp (k : ℤ) (x : HsEuclidean N) : g (x + (k : ℝ) • hsRotationVector N) = g x :=
    congrArg (fun A : HsEuclidean N →L[ℝ] ℝ => A v)
      (fderiv_periodic_vector (fun k y => by
        rw [← hsTranslate_eq_add_rotation]; exact f.periodic k y) k x)
  have hP : vectorPeriodize (hsRotationVector N) (hsRotationVector_ne_zero N) ψ hψc = g :=
    vectorPeriodize_periodicCutoff_mul (hsRotationVector_ne_zero N) ℓ
      (by simp [ℓ, hsRotationVector]) hgp hψc
  have hi := hsSobolev_periodized_integrationByParts hN χ hc h hψ hψc hψU v
  dsimp only at hi
  rw [hP] at hi
  exact hi

end Riesz1

end
