/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorOneBridge
public import Riesz1.CLT.ErrorOneExponents
public import Riesz1.Variance.RegUniformComplete

/-!
# Pointwise bounds of the regularized profile and transport (first error bound in Theorem 3)

At one scale `ℓ` and one particle number `N`, with smoothing radius `δ = δ_N ∈ (0, 1]`, the
four analytic inputs of the first error bound in the proof of Theorem 3 are

* `‖ξ_reg'‖ ≤ C δ^{-1-α-η}`, `‖ξ_reg''‖ ≤ C δ^{-2-α-η}` (Lemma 5.1).
* `‖ψ_reg‖ ≤ C`.
* `‖ψ_reg'‖ ≤ C δ^{-b-η}` with `b = 1 - s + α`, from the mark sum of the transport bound.

`errorOne_bounds_of_facts` derives them from the same bounds on the mollified families, which the
case lemmas below obtain from Lemma 5.1. The exponent `-1 + s - α'` of the transport
bound equals `-b - η` for `α' = α + η`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

namespace Riesz1.Internal

/-- The four analytic bounds at one scale `ℓ` and particle number `N` (the inputs of the first
error bound in the proof of Theorem 3). The profile bounds hold for the mollification of
the periodized profile and the transport bounds for the mollification of a transport `ψ0` of it,
with `α' = α + η`. The transport `ψ_reg` is the given one. -/
lemma errorOne_bounds_of_facts {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (p : Profile) (α η C₁ C₂ C₃ C₄ : ℝ) (n : ℕ) (marks : Fin n → ℝ)
    (hα0 : P.val.2 - 1 ≤ α) (hη : 0 < η) (_hα'0 : P.val.2 - 1 < α + η)
    (_hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂) (_hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄)
    (hH : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
      |deriv (fun t : ℝ => circleMollify ρ (observationLength ℓ).val h
          (fun s : ℝ => periodizedProfile p (observationLength ℓ) (s : Circle (observationLength ℓ)))
          t) x| ≤ C₁ * h ^ (-1 - α - η) ∧
      |deriv (deriv (fun t : ℝ => circleMollify ρ (observationLength ℓ).val h
          (fun s : ℝ => periodizedProfile p (observationLength ℓ) (s : Circle (observationLength ℓ)))
          t)) x| ≤ C₂ * h ^ (-2 - α - η))
    (ψ0 : Circle (loopMasterLength ℓ) → ℝ)
    (hψ0m : MemLp (fun x => (ψ0 x : ℂ)) 2 (arclength (loopMasterLength ℓ)))
    (hψ0 : ∀ k : ℤ, coeff (loopMasterLength ℓ)
      ⟨(fun x => (ψ0 x : ℂ)), complexL2Integrable _ _ hψ0m⟩ k =
      transportCoeffs P (loopMasterLength ℓ)
        ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩ k)
    (hsup : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
      |circleMollify ρ (loopMasterLength ℓ).val h (fun t : ℝ => ψ0 (t : Circle (loopMasterLength ℓ))) x|
        ≤ C₃)
    (hder : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
      |deriv (fun t : ℝ => circleMollify ρ (loopMasterLength ℓ).val h
          (fun s : ℝ => ψ0 (s : Circle (loopMasterLength ℓ))) t) x| ≤
        C₄ * (1 + ∑ j : Fin n,
          max (dist (x : Circle (loopMasterLength ℓ)) (marks j : Circle (loopMasterLength ℓ))) h ^
            (-1 + P.val.2 - (α + η))))
    (ψ : Circle (loopMasterLength ℓ) → ℝ)
    (hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle (loopMasterLength ℓ))))
    (htr : ∀ k : ℤ, coeff (loopMasterLength ℓ)
      ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
      transportCoeffs P (loopMasterLength ℓ)
        (loopMasterLengthTest _ (cltReg hρ P N ℓ
          ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩)
          (cltReg_contDiff hρ P N ℓ
            ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩)) k)
    (hδ1 : cltDelta P N ℓ ≤ 1) :
    (∀ u : ℝ, |deriv (cltRegLine hρ P N ℓ
          ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩) u| ≤
        C₁ * cltDelta P N ℓ ^ (-1 - α - η)) ∧
    (∀ u : ℝ, |deriv (deriv (cltRegLine hρ P N ℓ
          ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩)) u| ≤
        C₂ * cltDelta P N ℓ ^ (-2 - α - η)) ∧
    (∀ u : ℝ, |(loopMasterProfile ℓ ψ hψ).val u| ≤ C₃) ∧
    (∀ u : ℝ, |deriv (loopMasterProfile ℓ ψ hψ).val u| ≤
        C₄ * (1 + (n : ℝ)) * cltDelta P N ℓ ^ (-(1 - P.val.2 + α) - η)) := by
  have hδ0 : 0 < cltDelta P N ℓ := cltDelta_pos P N ℓ
  set δ := cltDelta P N ℓ with hδdef
  have hR : cltRegLine hρ P N ℓ ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩ =
      fun x => circleMollify ρ (observationLength ℓ).val δ
        (fun t : ℝ => periodizedProfile p (observationLength ℓ) (t : Circle (observationLength ℓ))) x :=
    funext fun x => cltRegLine_eq_circleMollify hρ P N ℓ p x
  have hΨ : (loopMasterProfile ℓ ψ hψ).val =
      fun x => circleMollify ρ (loopMasterLength ℓ).val δ
        (fun t : ℝ => ψ0 (t : Circle (loopMasterLength ℓ))) x :=
    funext fun x => loopMasterProfile_eq_circleMollify hρ P N ℓ p ψ hψ htr ψ0 hψ0m hψ0 x
  have hexp : -1 + P.val.2 - (α + η) = -(1 - P.val.2 + α) - η := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    rw [hR]
    exact (hH δ hδ0 hδ1 u).1
  · intro u
    rw [hR]
    exact (hH δ hδ0 hδ1 u).2
  · intro u
    rw [hΨ]
    exact hsup δ hδ0 hδ1 u
  · intro u
    rw [hΨ]
    have he : -1 + P.val.2 - (α + η) ≤ 0 := by linarith
    have hsum := errorOne_sum_rpow_le n δ (-1 + P.val.2 - (α + η))
      (fun j => dist (u : Circle (loopMasterLength ℓ)) (marks j : Circle (loopMasterLength ℓ)))
      hδ0 hδ1 he
    have h2 := mul_le_mul_of_nonneg_left hsum hC₄
    exact (hder δ hδ0 hδ1 u).trans (h2.trans (le_of_eq (by rw [hexp]; ring)))

end Riesz1.Internal

end
end
