/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingIdentityCont

/-!
# The gradient splitting identity

The identity part of Lemma 5.7. For the localized
loop `H_γ` on the ordered domain `D_N`:

* `H_γ` is smooth on `D_N`.
* every integral defining the fields `V` and `W` exists, including both principal values at every
  periodic image of every lift `x_i`, and the background integrals of `H_γ` exist.
* the fields `V` and `W` are continuous on `D_N`, hence Borel measurable there.
* the gradient of `H_γ` is `V + W` on `D_N`, in the coordinate directions.
-/

@[expose] public section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The gradient splitting identity for the localized loop `H_γ` on the ordered domain `D_N`, for
the full window and the partial window alike. -/
theorem gradient_splitting_identity {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) :
    ContDiffOn ℝ ∞ (gradLoop s ψ N ℓ γ) (orderedDomain N) ∧
    (∀ X ∈ orderedDomain N, ∀ k : Fin (N : ℕ),
      fderiv ℝ (gradLoop s ψ N ℓ γ) X (Pi.single k 1)
        = gradVfield s ψ N ℓ γ X k + gradWfield s ψ N ℓ γ X k) ∧
    (∀ k : Fin (N : ℕ), ContinuousOn (fun X => gradVfield s ψ N ℓ γ X k) (orderedDomain N)) ∧
    (∀ k : Fin (N : ℕ), ContinuousOn (fun X => gradWfield s ψ N ℓ γ X k) (orderedDomain N)) ∧
    (∀ X ∈ orderedDomain N, ∀ i ∈ gradLabels N ℓ γ, ∃ LA LB : ℝ,
      Tendsto (fun δ : ℝ => ∫ y in gradBLo N ℓ γ (gradLift N X i)..gradBHi N ℓ γ (gradLift N X i),
        Set.indicator {y : ℝ | ∀ m : ℤ, δ ≤ |y - gradLift N X i - m|}
          (fun y => gradZx ψ ℓ (gradLift N X i) y * gradKernelH s (y - gradLift N X i)) y)
        (𝓝[>] 0) (𝓝 LA) ∧
      Tendsto (fun δ : ℝ => ∫ y in gradBLo N ℓ γ (gradLift N X i)..gradBHi N ℓ γ (gradLift N X i),
        Set.indicator {y : ℝ | ∀ m : ℤ, δ ≤ |y - gradLift N X i - m|}
          (fun y => gradZ ψ ℓ (gradLift N X i) y * deriv (gradKernelH s) (y - gradLift N X i)) y)
        (𝓝[>] 0) (𝓝 LB)) ∧
    (∀ X ∈ orderedDomain N, ∀ i ∈ gradLabels N ℓ γ,
      IntervalIntegrable (fun y => gradZ ψ ℓ (gradLift N X i) y * gradKernelH s (y - gradLift N X i))
        volume (gradBLo N ℓ γ (gradLift N X i)) (gradBHi N ℓ γ (gradLift N X i))) := by
  refine ⟨?_, fun X hX k => fderiv_gradLoop_single hψ hℓ0 hp hs0 hs1 hsupp hX k,
    fun k => continuousOn_gradVfield hψ hℓ0 hp hs0 hs1 hsupp k,
    fun k => continuousOn_gradWfield hψ hℓ0 hs0 hs1 k, ?_, ?_⟩
  · exact (contDiffOn_gradLoop_nonInt hψ hℓ0 hp hs0 hs1 hsupp).mono
      (orderedDomain_subset_nonInt hℓ0.le)
  · intro X _ i _
    exact gradPV_exists hψ hℓ0 hp hs0 hs1 hsupp (gradLift N X i)
  · intro X _ i _
    exact intervalIntegrable_gradBackground hψ hℓ0 hp hs0 hs1 N (gradLift N X i)

end

end Riesz1
