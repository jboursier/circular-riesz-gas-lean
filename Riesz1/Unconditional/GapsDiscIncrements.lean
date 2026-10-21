/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscIncrementLimits
public import Riesz1.CLT.GapsDiscInversion
public import Riesz1.Rigidity.RigidityTheorem

/-!
# Short increments and the selected count, with the externals as hypotheses

Restatements of the conditional theorems
`Riesz1.Internal.gapsDisc_increment_eventual_expectation_of_rigidity` and
`gapsDisc_increment_probability_of_rigidity`. The rigidity hypothesis is replaced by the
externals `Riesz1.External.BakryEmery` and `Riesz1.External.PrekopaLeindler`.

The theorem for Corollary 1 is `gapsDisc_inversion_label`. It combines these two
restatements with the unconditional event identities `Riesz1.selectedDiscrepancy_inversion`.
-/

public section

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace Riesz1

/-- The eventual `L¹` bound on short increments, with the externals as hypotheses. -/
theorem gapsDisc_increment_eventual_expectation (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s)
    (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} {l : Filter ι} (N : ι → ℕ+) (k : ι → ℕ),
      Tendsto k l atTop → (∀ᶠ n in l, 1 ≤ k n ∧ k n ≤ (N n : ℕ) / 2) →
      ∀ A : ℝ, 0 < A → ∀ᶠ n in l, ∀ r : ℤ,
      (r.natAbs : ℝ) ≤ A * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (k n) →
      Integrable (fun X : Configuration (N n) => selectedIncrement X (k n) r)
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)) ∧
      (∫ X, |selectedIncrement X (k n) r|
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)) ≤
          C * (r.natAbs : ℝ) ^ (3 * s / 4) :=
  Internal.gapsDisc_increment_eventual_expectation_of_rigidity beta s hbeta hs hs1 hPL
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1)

/-- Convergence in probability of the normalized short increments, with the externals as
hypotheses. -/
theorem gapsDisc_increment_probability (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s)
    (hs1 : s < 1) {ι : Type*} {l : Filter ι} (N : ι → ℕ+) (k : ι → ℕ)
    (hk : Tendsto k l atTop)
    (hvalid : ∀ᶠ n in l, 1 ≤ k n ∧ k n ≤ (N n : ℕ) / 2)
    (A : ℝ) (hA : 0 < A) (r : ι → ℤ)
    (hr : ∀ᶠ n in l, ((r n).natAbs : ℝ) ≤ A *
      gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (k n))
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun n => gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)
      {X | η ≤ |selectedIncrement X (k n) (r n) /
        gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (k n)|}) l (𝓝 0) :=
  Internal.gapsDisc_increment_probability_of_rigidity beta s hbeta hs hs1 hPL
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1)
    N k hk hvalid A hA r hr η hη

/-- Corollary 1, with the externals as hypotheses. It states the `L¹` bound
`E|T_r| ≤ C |r|^{3s/4}` for `|r| ≤ A b_N` and
large `N`, the convergence `T_{r_N} / b_N → 0` in probability for integer sequences with
`|r_N| ≤ A b_N`, and both deterministic event identities for integers `r` with
`1 ≤ k + r ≤ N - 1`. -/
theorem gapsDisc_inversion_label (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
    (∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} {l : Filter ι} (N : ι → ℕ+) (k : ι → ℕ),
      Tendsto k l atTop → (∀ᶠ n in l, 1 ≤ k n ∧ k n ≤ (N n : ℕ) / 2) →
      ∀ A : ℝ, 0 < A → ∀ᶠ n in l, ∀ r : ℤ,
      (r.natAbs : ℝ) ≤ A * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (k n) →
      Integrable (fun X : Configuration (N n) => selectedIncrement X (k n) r)
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)) ∧
      (∫ X, |selectedIncrement X (k n) r|
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)) ≤
          C * (r.natAbs : ℝ) ^ (3 * s / 4)) ∧
    (∀ {ι : Type*} {l : Filter ι} (N : ι → ℕ+) (k : ι → ℕ), Tendsto k l atTop →
      (∀ᶠ n in l, 1 ≤ k n ∧ k n ≤ (N n : ℕ) / 2) →
      ∀ A : ℝ, 0 < A → ∀ r : ι → ℤ,
      (∀ᶠ n in l, ((r n).natAbs : ℝ) ≤ A *
        gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (k n)) →
      ∀ η : ℝ, 0 < η →
      Tendsto (fun n => gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)
        {X | η ≤ |selectedIncrement X (k n) (r n) /
          gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (k n)|}) l (𝓝 0)) ∧
    (∀ (N : ℕ+) (k : ℕ) (hk : k < (N : ℕ)) (r : ℤ),
      1 ≤ (k : ℤ) + r → (k : ℤ) + r < (N : ℕ) →
      ({X : Configuration N | r ≤ selectedDiscrepancy X k hk} =
          {X | blockLength X (nearestLabel X) ((k : ℤ) + r).toNat ≤ k} ∧
        {X : Configuration N | r ≤ selectedDiscrepancy X k hk} =
          {X | blockLength X (nearestLabel X) k - k + (r : ℝ) +
            selectedIncrement X k r ≤ 0})) :=
  ⟨gapsDisc_increment_eventual_expectation hBE hPL beta s hbeta hs hs1,
    fun N k hk hvalid A hA r hr η hη =>
      gapsDisc_increment_probability hBE hPL beta s hbeta hs hs1 N k hk hvalid A hA r hr η hη,
    fun _ k hk r hr0 hrN => selectedDiscrepancy_inversion k hk r hr0 hrN⟩

end Riesz1

end
end
