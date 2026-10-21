/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.Identity
public import Riesz1.CLT.ErrorOneAnalytic
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Bridges to the mollified profile and transport (Theorem 3)

For the periodized profile `ξ = periodizedProfile p` at scale `ℓ`:

* `cltRegLine_eq_circleMollify`: the line profile `ξ_reg = ξ ⋆ ρ_δ` is the
  mollification `circleMollify` of the periodized profile at radius `δ_N`.
* `loopMasterProfile_eq_circleMollify`: the smooth transport `ψ_reg` of `ξ_reg` is
  the mollification of any transport `ψ0` of `ξ`, because the Fourier coefficients of `ψ_reg`
  are those of `ψ0` times the mollifier multiplier (`errorOne_eq_circleMollify_of_coeff`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

namespace Riesz1.Internal

/-- A function on a circle is continuous when its lift to the line is. -/
lemma continuous_circle_of_lift (L : Length) {ψ : Circle L → ℝ}
    (h : Continuous (fun u : ℝ => ψ (u : Circle L))) : Continuous ψ :=
  (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L.val)).continuous_iff.2 h

/-- The line profile `ξ_reg` is the mollification of the periodized profile at
radius `δ_N`. -/
lemma cltRegLine_eq_circleMollify {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (p : Profile) (x : ℝ) :
    cltRegLine hρ P N ℓ ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩ x =
      circleMollify ρ (observationLength ℓ).val (cltDelta P N ℓ)
        (fun t : ℝ => periodizedProfile p (observationLength ℓ) (t : Circle (observationLength ℓ)))
        x :=
  cltRegCircle_coe hρ (loopMasterLength ℓ) (cltDelta_pos P N ℓ) _ x

/-- The smooth transport `ψ` of `ξ_reg` (given by its Fourier coefficients) is the mollification
of any transport `ψ0` of the periodized profile `ξ`. -/
lemma loopMasterProfile_eq_circleMollify {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (P : Parameters)
    (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) (p : Profile)
    (ψ : Circle (loopMasterLength ℓ) → ℝ)
    (hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle (loopMasterLength ℓ))))
    (htr : ∀ k : ℤ, coeff (loopMasterLength ℓ)
      ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
      transportCoeffs P (loopMasterLength ℓ)
        (loopMasterLengthTest _ (cltReg hρ P N ℓ
          ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩)
          (cltReg_contDiff hρ P N ℓ
            ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩)) k)
    (ψ0 : Circle (loopMasterLength ℓ) → ℝ)
    (hψ0m : MemLp (fun x => (ψ0 x : ℂ)) 2 (arclength (loopMasterLength ℓ)))
    (hψ0 : ∀ k : ℤ, coeff (loopMasterLength ℓ)
      ⟨(fun x => (ψ0 x : ℂ)), complexL2Integrable _ _ hψ0m⟩ k =
      transportCoeffs P (loopMasterLength ℓ)
        ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩ k)
    (x : ℝ) :
    (loopMasterProfile ℓ ψ hψ).val x =
      circleMollify ρ (loopMasterLength ℓ).val (cltDelta P N ℓ)
        (fun t : ℝ => ψ0 (t : Circle (loopMasterLength ℓ))) x := by
  have hψc : Continuous (loopMasterLengthTest _ ψ hψ).val :=
    continuous_circle_of_lift _ hψ.continuous
  have hg : ∀ y : ℝ, (loopMasterLengthTest _ (cltReg hρ P N ℓ
      ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩)
        (cltReg_contDiff hρ P N ℓ
          ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩)).val
        (y : Circle (loopMasterLength ℓ)) =
      circleMollify ρ (loopMasterLength ℓ).val (cltDelta P N ℓ)
        (fun t : ℝ => (⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩ :
          {f : Circle (loopMasterLength ℓ) → ℝ //
            MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength ℓ))}).val
              (t : Circle (loopMasterLength ℓ))) y :=
    fun y => cltRegCircle_coe hρ (loopMasterLength ℓ) (cltDelta_pos P N ℓ) _ y
  have key := errorOne_eq_circleMollify_of_coeff P (loopMasterLength ℓ) hρ
    (cltDelta_pos P N ℓ)
    ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩ ψ0 hψ0m hψ0
    (loopMasterLengthTest _ (cltReg hρ P N ℓ
      ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩)
        (cltReg_contDiff hρ P N ℓ
          ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩))
    hg (loopMasterLengthTest _ ψ hψ) hψc htr x
  exact key

end Riesz1.Internal

end
end
