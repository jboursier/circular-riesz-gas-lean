/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.RigidityTheorem
public import Riesz1.Auxiliary.BellEnergyBound
public import Riesz1.Auxiliary.BellRandomSum
public import Riesz1.Auxiliary.BellRandomSumMoments
public import Riesz1.Auxiliary.BellRandomSumShort

/-!
# The averaged quadratic energy and random block sums, with the externals as hypotheses

Restatements of the conditional theorems `Riesz1.Internal.*_of_rigidity`
for the Bell kernel. Each statement is that of the conditional theorem with the rigidity
hypothesis removed. The two externals `Riesz1.External.BakryEmery` and
`Riesz1.External.PrekopaLeindler` are explicit arguments instead, and the rigidity conclusion
is supplied by `Riesz1.Internal.rigidityConclusion_of_externals`.

Lemma B.1 (`bell` and `bell_random_sum`).
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- The energy bound behind Lemma B.1, with the externals as hypotheses. -/
theorem bell_energy (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) (ψ : LoopScaleProfile ℓ.val),
      1 ≤ (N : ℝ) * ℓ.val → ContDiff ℝ ∞ ψ.val →
      Integrable (bellQuadraticLoop (parametersExponent
        (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters)) N ℓ ψ)
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ∧
      |(∫ X : Configuration N, bellQuadraticLoop (parametersExponent
          (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters)) N ℓ ψ X
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N)| ≤
          C * (N : ℝ) * ℓ.val * bellEnergy ℓ.val ψ.val := by
  obtain ⟨C, hC, h⟩ := Internal.bell_energy_of_rigidity beta s hbeta hs hs1
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1)
  exact ⟨C, hC, h hPL⟩

/-- Lemma B.1 (averaged quadratic energy), with the externals as hypotheses.
The integrability and the bound `|E B_ℓ[ψ]| ≤ C N ℓ ‖ψ'‖²` hold for every `N ≥ 1`. -/
theorem bell (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) (ψ : ℝ → ℝ),
      1 ≤ (N : ℝ) * ℓ.val → ∀ (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ ℓ.val⁻¹),
      let Ψ : LoopScaleProfile ℓ.val :=
        ⟨ψ, hp, loopMaster_lipschitz (inv_ne_zero ℓ.2.1.ne') hψ hp⟩
      Integrable (bellQuadraticLoop (parametersExponent
        (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters)) N ℓ Ψ)
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ∧
      |(∫ X : Configuration N, bellQuadraticLoop (parametersExponent
          (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters)) N ℓ Ψ X
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N)| ≤
          C * (N : ℝ) * ℓ.val * bellEnergy ℓ.val ψ := by
  obtain ⟨C, hC, h⟩ := Internal.bell_of_rigidity beta s hbeta hs hs1
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1)
  exact ⟨C, hC, h hPL⟩

/-- Lemma B.1 (random block lengths versus a lattice), with the externals as
hypotheses. -/
theorem bell_random_sum (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (ℓ : ℝ) (ψ : ℝ → ℝ),
      0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ k ∈ Finset.Icc 1 ((N : ℕ) - 1),
        Integrable (fun X : Configuration N => bellKernel s N ℓ ψ (blockLength X 0 k))
          (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N)) ∧
      (∑ k ∈ Finset.Icc 1 ((N : ℕ) - 1),
        |(∫ X : Configuration N, bellKernel s N ℓ ψ (blockLength X 0 k)
          ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) -
          bellKernel s N ℓ ψ (k : ℝ)|) ≤ C * bellConstant ℓ ψ := by
  obtain ⟨C, hC, h⟩ := Internal.bell_random_sum_of_rigidity beta s hbeta hs hs1
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1)
  exact ⟨C, hC, h hPL⟩

/-- The second moment of a block in the random-sum argument, with the externals as
hypotheses. -/
theorem bell_block_second_moment (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (i : Fin (N : ℕ)) (k : ℕ),
      1 ≤ k → k ≤ (N : ℕ) / 2 →
      Integrable (fun X : Configuration N => (blockLength X (i : ℕ) k - k) ^ 2)
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ∧
      (∫ X : Configuration N, (blockLength X (i : ℕ) k - k) ^ 2
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
          D * (k : ℝ) ^ (3 * s / 2) := by
  obtain ⟨D, hD, h⟩ := Internal.bell_block_second_moment_of_rigidity beta s hbeta hs hs1
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1)
  exact ⟨D, hD, h hPL⟩

/-- The short-block comparison in the random-sum argument, with the externals as
hypotheses. -/
theorem bell_random_short (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (i : Fin (N : ℕ)) (k : ℕ),
      1 ≤ k → k ≤ (N : ℕ) / 2 →
      ∀ (ℓ : ℝ) (ψ : ℝ → ℝ), 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      |(∫ X : Configuration N, bellKernel s N ℓ ψ (blockLength X (i : ℕ) k)
          ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) -
        bellKernel s N ℓ ψ (k : ℝ)| ≤
          C * bellConstant ℓ ψ * (k : ℝ) ^ (-1 - s / 4) := by
  obtain ⟨C, hC, h⟩ := Internal.bell_random_short_of_rigidity beta s hbeta hs hs1
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1)
  exact ⟨C, hC, h hPL⟩

end Riesz1

end
end
