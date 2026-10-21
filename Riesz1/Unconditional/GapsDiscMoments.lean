/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscMoments
public import Riesz1.CLT.GapsDiscIncrements
public import Riesz1.CLT.GapsDiscScale
public import Riesz1.Rigidity.RigidityTheorem

/-!
# Moments of the centered gaps, with the externals as hypotheses

Restatements of the conditional theorems
`Riesz1.Internal.gapsDisc_secondMoment_of_rigidity`, `gapsDisc_integrable_square_of_rigidity`,
`gapsDisc_selectedBlock_firstMoment_of_rigidity`, `gapsDisc_increment_firstMoment_of_rigidity`
and `gapsDisc_increment_expectation_of_rigidity`. The rigidity hypothesis is replaced by the
externals `Riesz1.External.BakryEmery` and `Riesz1.External.PrekopaLeindler`.

The theorem for Corollary 1 is `gapsDisc_moments_label`.
-/

public section

noncomputable section

open MeasureTheory Filter Finset Set Topology
open scoped ENNReal

namespace Riesz1

/-- The uniform second moment of centered block lengths, with the externals as hypotheses. -/
theorem gapsDisc_secondMoment (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (i : ℤ) (r : ℕ),
      1 ≤ r → r ≤ (N : ℕ) / 2 →
      (∫⁻ X : Configuration N, ENNReal.ofReal ((blockLength X i r - r) ^ 2)
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
          ENNReal.ofReal (K * (r : ℝ) ^ (3 * s / 2)) :=
  Internal.gapsDisc_secondMoment_of_rigidity beta s hbeta hs hs1 hPL
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1)

/-- Integrability of the square of a centered block, with the externals as hypotheses. -/
theorem gapsDisc_integrable_square (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (i : ℤ) (r : ℕ) (hr : 1 ≤ r) (hrN : r ≤ (N : ℕ) / 2) :
    Integrable (fun X : Configuration N => (blockLength X i r - r) ^ 2)
      (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) :=
  Internal.gapsDisc_integrable_square_of_rigidity beta s hbeta hs hs1 hPL
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1) N hN i r hr hrN

/-- The first moment of a selected block, with the externals as hypotheses. -/
theorem gapsDisc_selectedBlock_firstMoment (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s)
    (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (i : ℤ) (r : ℕ),
      1 ≤ r → r ≤ (N : ℕ) / 2 →
      (∫⁻ X : Configuration N,
        ENNReal.ofReal |blockLength X (nearestLabel X + i) r - r|
          ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
            ENNReal.ofReal (C * (r : ℝ) ^ (3 * s / 4)) :=
  Internal.gapsDisc_selectedBlock_firstMoment_of_rigidity beta s hbeta hs hs1 hPL
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1)

/-- The first moment of a selected increment, with the externals as hypotheses. -/
theorem gapsDisc_increment_firstMoment (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s)
    (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (k : ℕ) (r : ℤ),
      r.natAbs ≤ (N : ℕ) / 2 →
      (∫⁻ X : Configuration N, ENNReal.ofReal |selectedIncrement X k r|
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
          ENNReal.ofReal (C * (r.natAbs : ℝ) ^ (3 * s / 4)) :=
  Internal.gapsDisc_increment_firstMoment_of_rigidity beta s hbeta hs hs1 hPL
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1)

/-- The expectation of the absolute value of a selected increment, with the externals as
hypotheses. -/
theorem gapsDisc_increment_expectation (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s)
    (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (k : ℕ) (r : ℤ),
      r.natAbs ≤ (N : ℕ) / 2 →
      Integrable (fun X : Configuration N => selectedIncrement X k r)
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ∧
      (∫ X : Configuration N, |selectedIncrement X k r|
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
          C * (r.natAbs : ℝ) ^ (3 * s / 4) :=
  Internal.gapsDisc_increment_expectation_of_rigidity beta s hbeta hs hs1 hPL
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1)

/-- Corollary 1, with the externals as hypotheses. It states the uniform second moment
`‖S_{i,r} - r‖₂² ≤ C r^{3s/2}`, the
vanishing of the centered block with `r = 0`, the two-sided comparison
`c k^{s/2} ≤ b_{N,k} ≤ C k^{s/2}`, and the limits `b_N → ∞` and `b_N / k_N → 0` along
`k_N → ∞`. -/
theorem gapsDisc_moments_label (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
    (∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (i : ℤ) (r : ℕ),
      1 ≤ r → r ≤ (N : ℕ) / 2 →
      (∫⁻ X : Configuration N, ENNReal.ofReal ((blockLength X i r - r) ^ 2)
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
          ENNReal.ofReal (K * (r : ℝ) ^ (3 * s / 2))) ∧
    (∀ (N : ℕ+) (i : ℤ) (X : Configuration N), blockLength X i 0 - ((0 : ℕ) : ℝ) = 0) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ+) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
      c * (k : ℝ) ^ (s / 2) ≤ gapScale ⟨s, hs, hs1⟩ N k ∧
        gapScale ⟨s, hs, hs1⟩ N k ≤ C * (k : ℝ) ^ (s / 2)) ∧
    (∀ {ι : Type*} {l : Filter ι} (N : ι → ℕ+) (k : ι → ℕ), Tendsto k l atTop →
      (∀ᶠ n in l, 1 ≤ k n ∧ k n ≤ (N n : ℕ) / 2) →
      Tendsto (fun n => gapScale ⟨s, hs, hs1⟩ (N n) (k n)) l atTop ∧
        Tendsto (fun n => gapScale ⟨s, hs, hs1⟩ (N n) (k n) / (k n : ℝ)) l (𝓝 0)) := by
  refine ⟨gapsDisc_secondMoment hBE hPL beta s hbeta hs hs1,
    fun N i X => by simp [blockLength_zero], gapsDisc_gapScale_comparison ⟨s, hs, hs1⟩,
    fun N k hk hvalid => ⟨gapsDisc_gapScale_tendsto_atTop ⟨s, hs, hs1⟩ N k hk hvalid,
      gapsDisc_gapScale_div_tendsto_zero ⟨s, hs, hs1⟩ N k hk hvalid⟩⟩

end Riesz1

end
end
