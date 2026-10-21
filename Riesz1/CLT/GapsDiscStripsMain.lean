/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscStripsDifference
public import Riesz1.CLT.GapsDiscStrips

/-!
# Small boundary strips

Part of the proof of Corollary 1, with the variance theorem as a hypothesis in the form of its
conclusion `Internal.QuantitativeVarianceConclusion`. The three assertions are the bound on the
centred count of a deterministic arc of length `t ≤ 1/4`, the bound on the difference of two
symmetric arcs with fixed half-width `a` and scales `ℓ_N → ℓ > 0`, and the limit of that bound.

Each arc is written as the arc count `arcCount c (t / 2)`, the open arc of length `t` centred at `c`.
Every arc of length `t` is of this form up to its endpoints, which carry no particles almost surely.
The scales `ℓ_N` lie in `(0, 1]` as all scales do here. There the arc has length
`2aℓ < 1`, so the centring `2 a N ℓ` is its mean. For larger scales the mean is `min(2aℓ, 1)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Riesz1

namespace Internal

/-- **Small boundary strips**, part of the proof of Corollary 1, under the variance
conclusion. Three assertions hold. The centred count of every arc of length `t ≤ 1/4` has the
stated `L¹` bound. For fixed `a` and scales `ℓ_N → ℓ > 0`, the symmetric difference of the two
normalized arc counts is bounded by `C (N^{-s/2} + t_N^{s/2})` with `t_N = a|ℓ_N - ℓ|`. That bound
tends to zero. -/
theorem strips_of_variance_clt (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hQV : Internal.QuantitativeVarianceConclusion beta s hbeta hs hs1) :
    (∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (c : UnitAddCircle) (t : ℝ), 0 < t → t ≤ 1 / 4 →
      ∫ X, |arcCount c (t / 2) X - (N : ℝ) * t| ∂(gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N) ≤
        if (N : ℝ) * t < 1 then 2 * ((N : ℝ) * t) else C * ((N : ℝ) * t) ^ (s / 2)) ∧
    (∀ a : ℝ, 0 < a → a < 1 / 2 → ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (lN l : ℝ), 0 < lN → lN ≤ 1 →
      0 < l → l ≤ 1 → a * |lN - l| ≤ 1 / 4 →
        (N : ℝ) ^ (-s / 2) *
          ∫ X, |(arcCount 0 (a * lN) X - (N : ℝ) * (2 * (a * lN))) -
            (arcCount 0 (a * l) X - (N : ℝ) * (2 * (a * l)))|
            ∂(gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N) ≤
          C * ((N : ℝ) ^ (-s / 2) + (a * |lN - l|) ^ (s / 2))) ∧
    (∀ a : ℝ, 0 < a → a < 1 / 2 → ∀ (ℓ : ℕ+ → ℝ) (l : ℝ), (∀ N, 0 < ℓ N ∧ ℓ N ≤ 1) → 0 < l →
      l ≤ 1 → Tendsto ℓ atTop (𝓝 l) →
        Tendsto (fun N : ℕ+ => (N : ℝ) ^ (-s / 2) *
          ∫ X, |(arcCount 0 (a * ℓ N) X - (N : ℝ) * (2 * (a * ℓ N))) -
            (arcCount 0 (a * l) X - (N : ℝ) * (2 * (a * l)))|
            ∂(gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N)) atTop (𝓝 0)) := by
  refine ⟨gapsDisc_strips_arc beta s hbeta hs hs1 hQV, fun a ha0 ha1 => ?_, fun a ha0 ha1 ℓ l hℓ hl0 hl1 hlim => ?_⟩
  · exact gapsDisc_strips_shift beta s hbeta hs hs1 hQV a ha0 ha1
  · obtain ⟨C, hC, hbound⟩ := gapsDisc_strips_shift beta s hbeta hs hs1 hQV a ha0 ha1
    -- the right-hand side tends to zero: `N^{-s/2} → 0` and `(a|ℓ_N - l|)^{s/2} → 0`
    have hNt : Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)) atTop atTop :=
      PNat.tendsto_comp_val_iff.2 tendsto_natCast_atTop_atTop
    have hpow : Tendsto (fun N : ℕ+ => (N : ℝ) ^ (-s / 2)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (show (0 : ℝ) < s / 2 by positivity)).comp hNt
      simpa only [Function.comp_def, neg_div] using h
    have hdist : Tendsto (fun N : ℕ+ => a * |ℓ N - l|) atTop (𝓝 0) := by
      simpa using (((hlim.sub_const l).abs).const_mul a)
    have hdist' : Tendsto (fun N : ℕ+ => (a * |ℓ N - l|) ^ (s / 2)) atTop (𝓝 0) := by
      have h := hdist.rpow_const (p := s / 2) (Or.inr (by positivity))
      simpa [Real.zero_rpow (show s / 2 ≠ 0 by positivity)] using h
    have hsmall : ∀ᶠ N : ℕ+ in atTop, a * |ℓ N - l| ≤ 1 / 4 :=
      hdist.eventually (ge_mem_nhds (by norm_num))
    have hupper : Tendsto (fun N : ℕ+ => C * ((N : ℝ) ^ (-s / 2) + (a * |ℓ N - l|) ^ (s / 2)))
        atTop (𝓝 0) := by
      simpa using (hpow.add hdist').const_mul C
    refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hupper
    · exact mul_nonneg (by positivity) (integral_nonneg fun X => abs_nonneg _)
    · filter_upwards [hsmall] with N hN
      exact hbound N (ℓ N) l (hℓ N).1 (hℓ N).2 hl0 hl1 hN

end Internal

end Riesz1

end
end
