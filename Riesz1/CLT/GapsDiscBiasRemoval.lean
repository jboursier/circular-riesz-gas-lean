/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscBiasBounds
public import Riesz1.CLT.GapsDiscBiasRate

/-!
# Removal of the nearest-particle bias, conditional on rigidity

Both assertions of Corollary 1: its finite-particle
bound for the square-root averaging window and its uniform disappearance.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Riesz1.Internal

/-- The bias bound, with its constant chosen before the particle number, block length
and bounded Lipschitz test. -/
theorem gapsDisc_bias_of_rigidity (beta s : ℝ) (hbeta : 0 < beta)
    (hs : 0 < s) (hs1 : s < 1) (hPL : External.PrekopaLeindler)
    (hRig : RigidityConclusion beta s hbeta hs hs1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (k : ℕ) (hk : 1 ≤ k ∧ k ≤ (N : ℕ) / 2) (f : ℝ → ℝ),
      LipschitzWith 1 f → (∀ t, |f t| ≤ 1) →
      |(∫ X, selectionWeight X 0 * f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0 k hk)
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) -
        ∫ X, f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0 k hk)
          ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N| ≤
      C * ((gapBiasWindow k : ℝ) ^ (3 * s / 4 - 1) +
        (gapBiasWindow k : ℝ) ^ (3 * s / 4) / (k : ℝ) ^ (s / 2)) := by
  obtain ⟨C, hC, hb⟩ := gapsDisc_bias_average_of_rigidity beta s hbeta hs hs1 hPL hRig
  exact ⟨C, hC, fun N hN k hk f hf hfb => hb N hN k hk (gapBiasWindow k)
    (gapBiasWindow_pos hk.1) ((gapBiasWindow_le k).trans hk.2) f hf hfb⟩

/-- Uniform disappearance of the bias along diverging admissible block lengths.
The eventual quantifier is outside the quantifier over all tests. -/
theorem gapsDisc_bias_uniform_of_rigidity (beta s : ℝ) (hbeta : 0 < beta)
    (hs : 0 < s) (hs1 : s < 1) (hPL : External.PrekopaLeindler)
    (hRig : RigidityConclusion beta s hbeta hs hs1)
    {ι : Type*} {l : Filter ι} (N : ι → ℕ+) (k : ι → ℕ)
    (hk : Tendsto k l atTop) (hvalid : ∀ n, 1 ≤ k n ∧ k n ≤ (N n : ℕ) / 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in l, ∀ (f : ℝ → ℝ), LipschitzWith 1 f → (∀ t, |f t| ≤ 1) →
      |(∫ X, selectionWeight X 0 *
          f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0 (k n) (hvalid n))
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)) -
        ∫ X, f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0 (k n) (hvalid n))
          ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)| < ε := by
  obtain ⟨C, _, hb⟩ := gapsDisc_bias_of_rigidity beta s hbeta hs hs1 hPL hRig
  have ht := (gapsDisc_bias_rate_tendsto_zero (⟨s, hs, hs1⟩ : RieszExponent) k hk).const_mul C
  have he : ∀ᶠ n in l, C * ((gapBiasWindow (k n) : ℝ) ^ (3 * s / 4 - 1) +
      (gapBiasWindow (k n) : ℝ) ^ (3 * s / 4) / (k n : ℝ) ^ (s / 2)) < ε := by
    exact ht.eventually (gt_mem_nhds (by simpa only [mul_zero] using hε))
  filter_upwards [he] with n hn
  intro f hf hfb
  have hN : 2 ≤ (N n : ℕ) := by have := hvalid n; omega
  exact (hb (N n) hN (k n) (hvalid n) f hf hfb).trans_lt hn

end Riesz1.Internal

end
end
