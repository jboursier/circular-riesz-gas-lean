/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscBiasRemoval
public import Riesz1.CLT.GapsDiscScale
public import Riesz1.Rigidity.RigidityTheorem

/-!
# Removal of the nearest-particle bias, with the externals as hypotheses

Restatements of the conditional theorems
`Riesz1.Internal.gapsDisc_bias_block_bounds_of_rigidity`, `gapsDisc_bias_average_of_rigidity`,
`gapsDisc_bias_of_rigidity` and `gapsDisc_bias_uniform_of_rigidity`. The rigidity hypothesis is
replaced by the externals `Riesz1.External.BakryEmery` and `Riesz1.External.PrekopaLeindler`.

The theorem for Corollary 1 is `gapsDisc_bias_label`. Besides the two restatements it proves
that the explicit bound
`m^{3s/4-1} + m^{3s/4} / k^{s/2}`, with `m = ⌊√k⌋`, tends to zero along `k_N → ∞`.
-/

public section

noncomputable section

open MeasureTheory Filter Finset Set Topology
open scoped ENNReal

namespace Riesz1

/-- The block bounds used in the bias removal, with the externals as hypotheses. -/
theorem gapsDisc_bias_block_bounds (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s)
    (hs1 : s < 1) :
    ∃ D W : ℝ, 0 < D ∧ 0 < W ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (i : ℤ) (j r : ℕ), r ≤ (N : ℕ) / 2 →
      Integrable (fun X : Configuration N => blockLength X i r - r)
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ∧
      (∫ X, |blockLength X i r - r|
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤ D * (r : ℝ) ^ (3 * s / 4) ∧
      Integrable (fun X : Configuration N => selectionWeight X j * |blockLength X i r - r|)
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ∧
      (∫ X, selectionWeight X j * |blockLength X i r - r|
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
          W * D * (r : ℝ) ^ (3 * s / 4) :=
  Internal.gapsDisc_bias_block_bounds_of_rigidity beta s hbeta hs hs1 hPL
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1)

/-- The averaged bias bound for a Lipschitz test function, with the externals as hypotheses. -/
theorem gapsDisc_bias_average (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (k : ℕ) (hk : 1 ≤ k ∧ k ≤ (N : ℕ) / 2) (m : ℕ),
      1 ≤ m → m ≤ (N : ℕ) / 2 → ∀ (f : ℝ → ℝ),
      LipschitzWith 1 f → (∀ t, |f t| ≤ 1) →
      |(∫ X, selectionWeight X 0 * f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0 k hk)
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) -
        ∫ X, f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0 k hk)
          ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N| ≤
      C * ((m : ℝ) ^ (3 * s / 4 - 1) + (m : ℝ) ^ (3 * s / 4) / (k : ℝ) ^ (s / 2)) :=
  Internal.gapsDisc_bias_average_of_rigidity beta s hbeta hs hs1 hPL
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1)

/-- The bias bound of Corollary 1, with the externals as hypotheses. -/
theorem gapsDisc_bias (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (k : ℕ) (hk : 1 ≤ k ∧ k ≤ (N : ℕ) / 2) (f : ℝ → ℝ),
      LipschitzWith 1 f → (∀ t, |f t| ≤ 1) →
      |(∫ X, selectionWeight X 0 * f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0 k hk)
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) -
        ∫ X, f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0 k hk)
          ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N| ≤
      C * ((gapBiasWindow k : ℝ) ^ (3 * s / 4 - 1) +
        (gapBiasWindow k : ℝ) ^ (3 * s / 4) / (k : ℝ) ^ (s / 2)) :=
  Internal.gapsDisc_bias_of_rigidity beta s hbeta hs hs1 hPL
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1)

/-- The bias removal uniformly over bounded Lipschitz test functions, with the externals as
hypotheses. -/
theorem gapsDisc_bias_uniform (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    {ι : Type*} {l : Filter ι} (N : ι → ℕ+) (k : ι → ℕ)
    (hk : Tendsto k l atTop) (hvalid : ∀ n, 1 ≤ k n ∧ k n ≤ (N n : ℕ) / 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in l, ∀ (f : ℝ → ℝ), LipschitzWith 1 f → (∀ t, |f t| ≤ 1) →
      |(∫ X, selectionWeight X 0 *
          f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0 (k n) (hvalid n))
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)) -
        ∫ X, f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0 (k n) (hvalid n))
          ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)| < ε :=
  Internal.gapsDisc_bias_uniform_of_rigidity beta s hbeta hs hs1 hPL
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1) N k hk hvalid ε hε

/-- For `k ≥ 1`, the second term of the bias bound satisfies
`⌊√k⌋^{3s/4} / k^{s/2} ≤ k^{-s/8}`, because `⌊√k⌋² ≤ k`. -/
lemma gapBiasWindow_pow_div_le (s : ℝ) (hs : 0 < s) (k : ℕ) (hk : 1 ≤ k) :
    (gapBiasWindow k : ℝ) ^ (3 * s / 4) / (k : ℝ) ^ (s / 2) ≤ (k : ℝ) ^ (-(s / 8)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hm2 : ((gapBiasWindow k : ℕ) : ℝ) ^ (2 : ℝ) ≤ (k : ℝ) := by
    rw [Real.rpow_two]
    exact_mod_cast Nat.sqrt_le' k
  have hm0 : (0 : ℝ) ≤ (gapBiasWindow k : ℝ) := Nat.cast_nonneg _
  have hpow : (gapBiasWindow k : ℝ) ^ (3 * s / 4) ≤ (k : ℝ) ^ (3 * s / 8) := by
    calc (gapBiasWindow k : ℝ) ^ (3 * s / 4)
        = (((gapBiasWindow k : ℕ) : ℝ) ^ (2 : ℝ)) ^ (3 * s / 8) := by
          rw [← Real.rpow_mul hm0]
          congr 1
          ring
      _ ≤ (k : ℝ) ^ (3 * s / 8) :=
          Real.rpow_le_rpow (by positivity) hm2 (by positivity)
  calc (gapBiasWindow k : ℝ) ^ (3 * s / 4) / (k : ℝ) ^ (s / 2)
      ≤ (k : ℝ) ^ (3 * s / 8) / (k : ℝ) ^ (s / 2) := by gcongr
    _ = (k : ℝ) ^ (-(s / 8)) := by
      rw [← Real.rpow_sub hk0]
      congr 1
      ring

/-- The explicit bias bound `m^{3s/4-1} + m^{3s/4} / k^{s/2}`, with `m = ⌊√k⌋`, tends to zero
along any sequence `k_n → ∞`. -/
lemma gapBiasWindow_bound_tendsto {ι : Type*} {l : Filter ι} (s : ℝ) (hs : 0 < s)
    (hs1 : s < 1) (k : ι → ℕ) (hk : Tendsto k l atTop) :
    Tendsto (fun n => (gapBiasWindow (k n) : ℝ) ^ (3 * s / 4 - 1) +
      (gapBiasWindow (k n) : ℝ) ^ (3 * s / 4) / (k n : ℝ) ^ (s / 2)) l (𝓝 0) := by
  have hm : Tendsto (fun n => (gapBiasWindow (k n) : ℝ)) l atTop := by
    have h1 : Tendsto (fun j : ℕ => gapBiasWindow j) atTop atTop :=
      tendsto_atTop_atTop.2 fun b => ⟨b * b, fun j hj => Nat.le_sqrt.2 hj⟩
    exact (tendsto_natCast_atTop_atTop.comp h1).comp hk
  have hkR : Tendsto (fun n => (k n : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hk
  have ht1 : Tendsto (fun n => (gapBiasWindow (k n) : ℝ) ^ (3 * s / 4 - 1)) l (𝓝 0) := by
    have e : 3 * s / 4 - 1 = -(1 - 3 * s / 4) := by ring
    simp only [e]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp hm
  have hg : Tendsto (fun n => (k n : ℝ) ^ (-(s / 8))) l (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp hkR
  have ht2 : Tendsto (fun n => (gapBiasWindow (k n) : ℝ) ^ (3 * s / 4) /
      (k n : ℝ) ^ (s / 2)) l (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ hg
    · exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · filter_upwards [hk.eventually_ge_atTop 1] with n hn
      exact gapBiasWindow_pow_div_le s hs (k n) hn
  have := ht1.add ht2
  rwa [add_zero] at this

/-- Corollary 1, with the externals as hypotheses. It states the bias bound
with constant depending only on `s, β`, the
uniform removal of the bias over bounded Lipschitz test functions along `k_N → ∞`, and the
convergence to zero of the explicit bound along `k_N → ∞`. -/
theorem gapsDisc_bias_label (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
    (∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (k : ℕ) (hk : 1 ≤ k ∧ k ≤ (N : ℕ) / 2) (f : ℝ → ℝ),
      LipschitzWith 1 f → (∀ t, |f t| ≤ 1) →
      |(∫ X, selectionWeight X 0 * f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0 k hk)
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) -
        ∫ X, f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0 k hk)
          ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N| ≤
      C * ((gapBiasWindow k : ℝ) ^ (3 * s / 4 - 1) +
        (gapBiasWindow k : ℝ) ^ (3 * s / 4) / (k : ℝ) ^ (s / 2))) ∧
    (∀ {ι : Type*} {l : Filter ι} (N : ι → ℕ+) (k : ι → ℕ),
      Tendsto k l atTop → (hvalid : ∀ n, 1 ≤ k n ∧ k n ≤ (N n : ℕ) / 2) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in l, ∀ (f : ℝ → ℝ), LipschitzWith 1 f → (∀ t, |f t| ≤ 1) →
      |(∫ X, selectionWeight X 0 *
          f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0 (k n) (hvalid n))
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)) -
        ∫ X, f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0 (k n) (hvalid n))
          ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)| < ε) ∧
    (∀ {ι : Type*} {l : Filter ι} (k : ι → ℕ), Tendsto k l atTop →
      Tendsto (fun n => (gapBiasWindow (k n) : ℝ) ^ (3 * s / 4 - 1) +
        (gapBiasWindow (k n) : ℝ) ^ (3 * s / 4) / (k n : ℝ) ^ (s / 2)) l (𝓝 0)) := by
  refine ⟨gapsDisc_bias hBE hPL beta s hbeta hs hs1, fun N k hk hvalid ε hε =>
    gapsDisc_bias_uniform hBE hPL beta s hbeta hs hs1 N k hk hvalid ε hε,
    fun k hk => gapBiasWindow_bound_tendsto s hs hs1 k hk⟩

end Riesz1

end
end
