/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingEstimates
public import Riesz1.Auxiliary.GradientSplittingGapIdentity

/-!
# Gradient splitting, every assertion of Lemma 5.7

Lemma 5.7. The statement `Riesz1.Internal.gradient_splitting_of_quadrature` lists every assertion
of the lemma:

* the splitting `∇Loop = V + W` with `V`, `W` (the fields `gradVfield`, `gradWfield`), and the
  vanishing of `V_i`, `W_i` outside `I_γ`.
* the gap covector `W^gap` (`gradWgap`), which vanishes unless `i, i+1 ∈ I_γ`, and the covector
  identity `W·U = -∑_i W^gap_i N (u_{i+1} - u_i)` for every `U` with `u_{N+1} = u_1`.
* the bounds `|V_i|` and `|W^gap|²` on `𝒜_{ε,γ} ∩ {|N x_1| ≤ K^ε}`, with the weights
  `w₁, w₂` of Lemma 5.7 at `K = Nℓ`.

The anchor `x_1 = 0` is the label `0` of `Fin N`.

The one conditional hypothesis is the parameter-wise quadrature conclusion
`GradientSplittingQuadratureConclusion s α γ`, which is the quadrature part of
Lemma 5.7. The parameter `γ₀ = max 4 (2/s)` depends only on `s`. The constants are chosen in
this order: `κ` depends only on `s`, `α` and `γ`. `ε` is small. `C` depends on `ε` and is
chosen before the particle number, the scale, the profile and `C₀`. This `C` is independent of
`C₀`, which is stronger than the statement in the paper (where `C` may depend on `C₀`). The bound
on `|W^gap|²` carries the factor `C₀²` explicitly.
-/

@[expose] public section

open scoped ContDiff

namespace Riesz1.Internal

noncomputable section

/-- **Gradient splitting**, Lemma 5.7, every assertion. -/
theorem gradient_splitting_of_quadrature {s α : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα0 : s - 1 ≤ α) (hα1 : α < s / 2) :
    ∃ γ₀ : ℝ, 1 < γ₀ ∧ ∀ γ : ℝ, γ₀ ≤ γ → GradientSplittingQuadratureConclusion s α γ →
      ∃ εstar : ℝ, 0 < εstar ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < εstar →
        ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ C₀ : ℝ) (ψ : ℝ → ℝ),
          2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → 0 ≤ C₀ →
          ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
          (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
          (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
          (GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) →
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
                -∑ e ∈ Finset.Ico (0 : ℤ) N, gradWgap s ψ N ℓ γ X e * (N : ℝ) * gradEdgeDiff N U e)) ∧
          (∀ X ∈ orderedDomain N, gradEvent s γ ε N ℓ X →
            |(N : ℝ) * gradLift N X 0| ≤ ((N : ℝ) * ℓ) ^ ε →
            (∀ i ∈ gradLabels N ℓ γ, |gradVlab s ψ N ℓ γ X i| ≤
              C * C₀ * ((N : ℝ) * ℓ) ^ (κ * ε) *
                (ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) +
                  (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) /
                    (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2))) ∧
            (∑ e ∈ Finset.Ico (0 : ℤ) N, (gradWgap s ψ N ℓ γ X e) ^ 2 ≤
              C * C₀ ^ 2 * ((N : ℝ) * ℓ) ^ (κ * ε) *
                ((N : ℝ) * ℓ + ((N : ℝ) * ℓ) ^ (2 * (1 - s + α))))) := by
  refine ⟨max 4 (2 / s), lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    fun γ hγ hquad => ?_⟩
  obtain ⟨εstar, hεstar, κ, hκ, hε⟩ :=
    gradient_splitting_estimates_of_quadrature hs0 hs1 hα0 hα1 hγ hquad
  refine ⟨εstar, hεstar, κ, hκ, fun ε hε0 hεs => ?_⟩
  obtain ⟨C, hC, hall⟩ := hε ε hε0 hεs
  refine ⟨C, hC, fun N ℓ C₀ ψ hN hℓ hℓ1 hK hC₀ hψ hper h1 h2 hsupp => ?_⟩
  obtain ⟨-, hfield, hest, -⟩ := hall N ℓ C₀ ψ hN hℓ hℓ1 hK hC₀ hψ hper h1 h2 hsupp
  refine ⟨fun X hX => ?_, fun X hX hev hanc => ?_⟩
  · obtain ⟨h1', h2', h3', h4', -⟩ := hfield X hX
    exact ⟨h1', h2', h3', h4'⟩
  · obtain ⟨hV, hG, -⟩ := hest X hX hev hanc
    exact ⟨hV, hG⟩

end

end Riesz1.Internal
