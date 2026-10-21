/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscCountsZero
public import Riesz1.CLT.GapsDiscCountsPos
public import Riesz1.CLT.GapsDiscCountsFixed
public import Riesz1.CLT.BLDistance

/-!
# Interval counts without a limit of the scale

Part of Corollary 1, the normal limit of the normalized arc counts
`Fluct_N[1_{(-aℓ_N, aℓ_N)}] / sqrt(N^s V_s(2aℓ_N))` for every scale sequence with `N ℓ_N → ∞`, with
no assumption on the limit of `ℓ_N`.

Every subsequence of particle numbers has a further subsequence on which the scales converge to
some `g ∈ [0, 1]` (compactness). For `g > 0` the count law is close to the count law at the constant
scale `g` (`counts_pos_coupling`), which converges (`fixed_scale_tendsto`). For `g = 0` the scale
sequence along the subsequence is extended to a full mesoscopic sequence tending to zero
(`exists_filler`), and the CLT rate applies (`counts_zero_tendsto`). Throughout, the main theorems enter as explicit hypotheses, in the
form of the conclusions `Internal.QuantitativeVarianceConclusion` and `Internal.CLTConclusion`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Riesz1

/-- The count law depends on the scale only through its value at the particle number. -/
lemma countLaw_congr (P : Parameters) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (ell ell' : Scales)
    (N : ℕ+) (h : ell' N = ell N) :
    countLaw P ha0 ha1 ell' N = countLaw P ha0 ha1 ell N := by
  unfold countLaw
  congr 1
  funext X
  unfold normalizedCount
  rw [h]

/-- **Interval counts, the limit of the scale unrestricted.** For a mesoscopic scale sequence
`ℓ` (that is, `N ℓ_N → ∞`), the bounded-Lipschitz distance of the count laws to the normal limit of
variance `v_s` tends to zero along the particle numbers. -/
theorem counts_tendsto (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hQV : Internal.QuantitativeVarianceConclusion beta s hbeta hs hs1)
    (hCLT : Internal.CLTConclusion beta s hbeta hs hs1) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (ell : Scales) (hmeso : Mesoscopic ell) :
    Tendsto (fun n => blDistance
        (countLaw ⟨(beta, s), hbeta, hs, hs1⟩ ha0 ha1 ell (particleNumber n))
        (normalProbOf (countVariance ⟨(beta, s), hbeta, hs, hs1⟩))) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hx : ∀ k, (ell (particleNumber (ns k))).val ∈ Set.Icc (0 : ℝ) 1 := fun k =>
    ⟨(ell _).property.1.le, (ell _).property.2⟩
  obtain ⟨g, hg, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hx
  refine ⟨φ, ?_⟩
  have hT : Tendsto (fun k => ns (φ k)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hℓ : Tendsto (fun k => (ell (particleNumber (ns (φ k)))).val) atTop (𝓝 g) := hlim
  rcases eq_or_lt_of_le hg.1 with h0 | hpos
  · -- the limit scale is zero: extend the subsequence to a mesoscopic scale sequence
    rw [← h0] at hℓ
    have hM : Tendsto (fun k => ((ns (φ k) + 1 : ℕ) : ℝ) *
        (ell (particleNumber (ns (φ k)))).val) atTop atTop := hmeso.comp hT
    obtain ⟨ell', hell'eq, hmeso', hℓ'⟩ := exists_filler ell (fun k => ns (φ k)) hT hℓ hM
    have hzero := counts_zero_tendsto beta s hbeta hs hs1 hCLT a ha0 ha1 ell' hmeso' hℓ'
    refine (hzero.comp hT).congr fun k => ?_
    simp only [Function.comp_apply]
    rw [countLaw_congr ⟨(beta, s), hbeta, hs, hs1⟩ ha0 ha1 ell ell' _ (hell'eq k)]
  · -- the limit scale is positive
    have hg1 : g ≤ 1 := hg.2
    have hA := counts_pos_coupling beta s hbeta hs hs1 hQV a ha0 ha1 g hpos hg1
      (fun k => ns (φ k)) hT ell hℓ
    have hB := (fixed_scale_tendsto beta s hbeta hs hs1 hCLT a ha0 ha1 g hpos hg1).comp hT
    have hsum := hA.add hB
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun k => zero_le) fun k => ?_
    exact blDistance_triangle _ _ _

namespace Internal

/-- **Interval counts** (the count part of Corollary 1), with the two main
theorems as explicit hypotheses. For every `a ∈ (0, 1/2)` and every scale sequence with
`N ℓ_N → ∞`, the normalized count is square-root-positive and measurable, and it converges in law
to the normal law of variance `v_s = countVariance P`. -/
theorem counts_of_variance_clt (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s)
    (hs1 : s < 1)
    (hQV : Internal.QuantitativeVarianceConclusion beta s hbeta hs hs1)
    (hCLT : Internal.CLTConclusion beta s hbeta hs hs1) :
    ∀ (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2), ∀ ell : Scales, Mesoscopic ell →
      (∀ N : ℕ+, 0 < Real.sqrt ((N : ℝ) ^ s *
          periodicZeta (parametersExponent ⟨(beta, s), hbeta, hs, hs1⟩)
            ((2 * a * (ell N).val : ℝ) : UnitAddCircle)) ∧
        AEMeasurable (normalizedCount ⟨(beta, s), hbeta, hs, hs1⟩ a ha ha1 ell N)
          (gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N)) ∧
      ConvergesInLaw
        (fun n => (gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ (particleNumber n)).map
          (normalizedCount ⟨(beta, s), hbeta, hs, hs1⟩ a ha ha1 ell (particleNumber n)))
        (normalLaw (Real.toNNReal (countVariance ⟨(beta, s), hbeta, hs, hs1⟩))) := by
  intro a ha ha1 ell hmeso
  refine ⟨fun N => ⟨?_, (measurable_normalizedCount _ a ha ha1 ell).aemeasurable⟩, ?_⟩
  · have hℓ0 : 0 < (ell N).val := (ell N).property.1
    have hℓ1 : (ell N).val ≤ 1 := (ell N).property.2
    have hV := periodicZeta_pos (parametersExponent ⟨(beta, s), hbeta, hs, hs1⟩)
      (t := 2 * a * (ell N).val) (by positivity) (by nlinarith)
    have hN : (0 : ℝ) < (N : ℝ) := by positivity
    exact Real.sqrt_pos.mpr (mul_pos (Real.rpow_pos_of_pos hN _) hV)
  · exact convergesInLaw_of_blDistance_tendsto_zero
      (fun n => countLaw ⟨(beta, s), hbeta, hs, hs1⟩ ha ha1 ell (particleNumber n))
      (normalProbOf (countVariance ⟨(beta, s), hbeta, hs, hs1⟩))
      (counts_tendsto beta s hbeta hs hs1 hQV hCLT a ha ha1 ell hmeso)

end Internal

end Riesz1

end
end
