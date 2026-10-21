/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingEstimates
public import Riesz1.Auxiliary.GradientSplittingQuadrature

/-!
# Gradient splitting estimates

The estimates part of Lemma 5.7, unconditionally. The quadrature
conclusion used by `Internal.gradient_splitting_estimates_of_quadrature` is
discharged by `gradient_splitting_quadrature`.
-/

@[expose] public section

open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The quadrature part of Lemma 5.7 gives the internal quadrature
conclusion on the window labels. -/
theorem Internal.gradientSplittingQuadratureConclusion_holds {s α γ : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hα0 : s - 1 ≤ α) (hα1 : α < s / 2)
    (hγ : max 4 (2 / s) ≤ γ) : Internal.GradientSplittingQuadratureConclusion s α γ := by
  obtain ⟨εstar, κ, hεstar, hκ, h⟩ := gradient_splitting_quadrature hs0 hs1 hα0 hα1 hγ
  refine ⟨εstar, hεstar, κ, hκ, fun ε hε hεs => ?_⟩
  obtain ⟨C, hC, hb⟩ := h ε hε hεs
  refine ⟨C, hC, fun N ℓ C₀ ψ hN hℓ hℓ1 hK hC0 hψ hper h1 h2 hsupp X _ hX hanchor i hi => ?_⟩
  have hi' := hb N ℓ C₀ ψ X hN hℓ hℓ1 hK hC0 hψ hper h1 h2 hsupp hX hanchor i
  rwa [gradV2lab_eq hi] at hi'

/-- All assertions of the estimates part of Lemma 5.7. -/
theorem gradient_splitting_estimates {s α γ : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hα0 : s - 1 ≤ α) (hα1 : α < s / 2)
    (hγ : max 4 (2 / s) ≤ γ) :
    ∃ εstar : ℝ, 0 < εstar ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < εstar →
      ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ C₀ : ℝ) (ψ : ℝ → ℝ),
        2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → 0 ≤ C₀ →
        ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
        (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
        (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
        (GradPartial N ℓ γ → ∀ y : ℝ,
          (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) →
        ContDiffOn ℝ ∞ (gradLoop s ψ N ℓ γ) (orderedDomain N) ∧
        (∀ X ∈ orderedDomain N,
          (∀ k : Fin (N : ℕ), fderiv ℝ (gradLoop s ψ N ℓ γ) X (Pi.single k 1) =
            gradVfield s ψ N ℓ γ X k + gradWfield s ψ N ℓ γ X k) ∧
          (∀ k : Fin (N : ℕ), (∀ i ∈ gradLabels N ℓ γ, gradIndex N i ≠ k) →
            gradVfield s ψ N ℓ γ X k = 0 ∧ gradWfield s ψ N ℓ γ X k = 0) ∧
          (∀ e ∈ Finset.Ico (0 : ℤ) N,
            (¬∃ i ∈ gradLabels N ℓ γ, gradInWindow N ℓ γ (i + 1) ∧ i % (N : ℤ) = e) →
            gradWgap s ψ N ℓ γ X e = 0) ∧
          (∀ U : Fin (N : ℕ) → ℝ,
            ∑ k : Fin (N : ℕ), gradWfield s ψ N ℓ γ X k * U k =
              -∑ e ∈ Finset.Ico (0 : ℤ) N,
                gradWgap s ψ N ℓ γ X e * (N : ℝ) * gradEdgeDiff N U e) ∧
          ∑ k : Fin (N : ℕ), gradWfield s ψ N ℓ γ X k = 0) ∧
        (∀ X ∈ orderedDomain N, gradEvent s γ ε N ℓ X →
          |(N : ℝ) * gradLift N X 0| ≤ ((N : ℝ) * ℓ) ^ ε →
          Internal.GradientSplittingEstimatesAt s α γ ε C κ C₀ ℓ N ψ X) ∧
        (∀ X ∈ orderedDomain N, gradEvent s γ ε N ℓ X → ∀ c : ℝ,
          (fun k => X k + c) ∈ orderedDomain N →
          |(N : ℝ) * gradLift N (fun k => X k + c) 0| ≤ ((N : ℝ) * ℓ) ^ ε →
          Internal.GradientSplittingEstimatesAt s α γ ε C κ C₀ ℓ N ψ (fun k => X k + c)) :=
  Internal.gradient_splitting_estimates_of_quadrature hs0 hs1 hα0 hα1 hγ
    (Internal.gradientSplittingQuadratureConclusion_holds hs0 hs1 hα0 hα1 hγ)

end

end Riesz1
