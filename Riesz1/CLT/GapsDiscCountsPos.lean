/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscCountsCoupling
public import Riesz1.CLT.GapsDiscCountsFixed

/-!
# Interval counts along subsequences with a positive limit scale

Part of Corollary 1, the case of a positive limit scale `g`. Along a
subsequence of particle numbers on which the scale converges to `g > 0`, the count law at the scale
`ℓ_k` is within bounded-Lipschitz distance `o(1)` of the count law at the constant scale `g`
(`counts_pos_coupling`), which converges to the normal limit by `fixed_scale_tendsto`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Riesz1

/-- The particle number as a real number. -/
lemma particleNumber_cast (n : ℕ) : ((particleNumber n : ℕ+) : ℝ) = (n : ℝ) + 1 := by
  simp [particleNumber]

/-- Along any sequence of indices tending to infinity, the particle numbers tend to infinity. -/
lemma tendsto_particleNumber_real {ι : Type*} {l : Filter ι} (ns : ι → ℕ)
    (hns : Tendsto ns l atTop) :
    Tendsto (fun i => ((particleNumber (ns i) : ℕ+) : ℝ)) l atTop := by
  simp_rw [particleNumber_cast]
  exact tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hns)

/-- The difference of two normalized counts is integrable. -/
lemma integrable_normalizedCount_diff (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2) (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1) (ell : Scales)
    (N : ℕ+) :
    Integrable (fun X : Configuration N => normalizedCount ⟨(beta, s), hbeta, hs, hs1⟩ a ha0 ha1
        ell N X - normalizedCount ⟨(beta, s), hbeta, hs, hs1⟩ a ha0 ha1
          (constScales g hg0 hg1) N X) (gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N) := by
  set P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩ with hPdef
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hmemA : MemLp (arcIndicator 0 (a * (ell N).val)) 2 volume := by
    simpa using (memLp_arcIndicator 0 (a * (ell N).val)).re
  have hmemG : MemLp (arcIndicator 0 (a * g)) 2 volume := by
    simpa using (memLp_arcIndicator 0 (a * g)).re
  have hLa := integrable_abs_arcCount_sub P N 0 (a * (ell N).val)
    ((N : ℝ) * (2 * (a * (ell N).val))) hmemA
  have hLg := integrable_abs_arcCount_sub P N 0 (a * g) ((N : ℝ) * (2 * (a * g))) hmemG
  have hfun : (fun X : Configuration N => normalizedCount P a ha0 ha1 ell N X -
      normalizedCount P a ha0 ha1 (constScales g hg0 hg1) N X) =
        fun X => (N : ℝ) ^ (-P.val.2 / 2) * countFactor P a (ell N).val *
            (arcCount 0 (a * (ell N).val) X - (N : ℝ) * (2 * (a * (ell N).val))) -
          (N : ℝ) ^ (-P.val.2 / 2) * countFactor P a g *
            (arcCount 0 (a * g) X - (N : ℝ) * (2 * (a * g))) := by
    funext X
    rw [normalizedCount_eq_countFactor P ha0 ha1 ell N X,
      normalizedCount_const_eq P ha0 ha1 g hg0 hg1 N X]
  rw [hfun]
  exact (hLa.const_mul _).sub (hLg.const_mul _)

/-- **Coupling along a positive limit scale.** Let `ns` tend to infinity along which the scale
`(ell (particleNumber (ns k))).val` converges to `g ∈ (0, 1]`. Then the bounded-Lipschitz distance
between the count laws at the scales `ℓ_k` and at the constant scale `g` tends to zero. -/
theorem counts_pos_coupling (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hQV : Internal.QuantitativeVarianceConclusion beta s hbeta hs hs1)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2) (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) (ell : Scales)
    (hℓ : Tendsto (fun k => (ell (particleNumber (ns k))).val) atTop (𝓝 g)) :
    Tendsto (fun k => blDistance
        (countLaw ⟨(beta, s), hbeta, hs, hs1⟩ ha0 ha1 ell (particleNumber (ns k)))
        (countLaw ⟨(beta, s), hbeta, hs, hs1⟩ ha0 ha1 (constScales g hg0 hg1)
          (particleNumber (ns k)))) atTop (𝓝 0) := by
  obtain ⟨C, K, hC, hK, hest⟩ := integral_normalizedCount_sub_le beta s hbeta hs hs1 hQV a ha0 ha1
    g hg0 hg1
  set P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩ with hPdef
  -- the real bound and its limit
  have hA : Tendsto (fun k => countFactor P a (ell (particleNumber (ns k))).val) atTop
      (𝓝 (countFactor P a g)) := countFactor_tendsto P ha0 ha1 hg0 hg1 _ hℓ
  have hN : Tendsto (fun k => ((particleNumber (ns k) : ℕ+) : ℝ)) atTop atTop :=
    tendsto_particleNumber_real ns hns
  have hB : Tendsto (fun k => ((particleNumber (ns k) : ℕ+) : ℝ) ^ (-s / 2)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := s / 2) (by linarith)).comp hN
    simp only [Function.comp_def] at h
    rw [show -s / 2 = -(s / 2) by ring]
    exact h
  have hdist : Tendsto (fun k => a * |(ell (particleNumber (ns k))).val - g|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => |(ell (particleNumber (ns k))).val - g|) atTop (𝓝 0) := by
      have := (hℓ.sub_const g).abs
      simpa using this
    simpa using h1.const_mul a
  have hCpow : Tendsto (fun k => (a * |(ell (particleNumber (ns k))).val - g|) ^ (s / 2))
      atTop (𝓝 0) := by
    have hcont : Continuous (fun x : ℝ => x ^ (s / 2)) := Real.continuous_rpow_const (by linarith)
    have h := (hcont.tendsto 0).comp hdist
    have h0 : (0 : ℝ) ^ (s / 2) = 0 := Real.zero_rpow (by positivity)
    simp only [Function.comp_def, h0] at h
    exact h
  have hsqrt : Tendsto (fun k => Real.sqrt K * |countFactor P a (ell (particleNumber (ns k))).val -
      countFactor P a g|) atTop (𝓝 0) := by
    have h := ((hA.sub_const (countFactor P a g)).abs).const_mul (Real.sqrt K)
    simpa using h
  -- the real upper bound tends to zero
  have hupper : Tendsto (fun k => countFactor P a (ell (particleNumber (ns k))).val *
      (C * (((particleNumber (ns k) : ℕ+) : ℝ) ^ (-s / 2) +
        (a * |(ell (particleNumber (ns k))).val - g|) ^ (s / 2))) +
      Real.sqrt K * |countFactor P a (ell (particleNumber (ns k))).val -
        countFactor P a g|) atTop (𝓝 0) := by
    have h := (hA.mul ((hB.add hCpow).const_mul C)).add hsqrt
    have h0 : countFactor P a g * (C * (0 + 0)) + 0 = 0 := by ring
    simpa [h0] using h
  have hupperE : Tendsto (fun k => ENNReal.ofReal (countFactor P a (ell (particleNumber (ns k))).val *
      (C * (((particleNumber (ns k) : ℕ+) : ℝ) ^ (-s / 2) +
        (a * |(ell (particleNumber (ns k))).val - g|) ^ (s / 2))) +
      Real.sqrt K * |countFactor P a (ell (particleNumber (ns k))).val -
        countFactor P a g|)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal hupper
    simpa using this
  -- the eventual coupling bound
  have hev : ∀ᶠ k in atTop, a * |(ell (particleNumber (ns k))).val - g| ≤ 1 / 4 := by
    have : ∀ᶠ x in 𝓝 (0 : ℝ), x ≤ 1 / 4 := eventually_le_nhds (by norm_num)
    exact hdist.eventually this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupperE
    (Eventually.of_forall fun k => zero_le) ?_
  filter_upwards [hev] with k hk
  have hX : Measurable (fun X : Configuration (particleNumber (ns k)) =>
      normalizedCount P a ha0 ha1 ell (particleNumber (ns k)) X) :=
    measurable_normalizedCount P a ha0 ha1 ell
  have hY : Measurable (fun X : Configuration (particleNumber (ns k)) =>
      normalizedCount P a ha0 ha1 (constScales g hg0 hg1) (particleNumber (ns k)) X) :=
    measurable_normalizedCount P a ha0 ha1 (constScales g hg0 hg1)
  have hint := integrable_normalizedCount_diff beta s hbeta hs hs1 a ha0 ha1 g hg0 hg1 ell
    (particleNumber (ns k))
  have : IsProbabilityMeasure (gibbsMeasure P (particleNumber (ns k))) :=
    (modelWellDefined P (particleNumber (ns k))).2.2
  have hcoup := blDistance_map_le_ofReal_integral_abs_sub
    (gibbsMeasure P (particleNumber (ns k))) hX hY hint.abs
  refine hcoup.trans (ENNReal.ofReal_le_ofReal ?_)
  exact hest ell (particleNumber (ns k)) hk

end Riesz1

end
end
