/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscSelectedGap
public import Riesz1.Unconditional.GapsDiscBias
public import Riesz1.CLT.SelectionBounds
public import Riesz1.CLT.VaryingLimit

/-!
# The gap CLT at the first label

The gap assertion in the proof of Corollary 1. The centred gap at the
label `0`, `(S_{1,k_N} - k_N) / b_{N,k_N}`, converges in law to the normal law of variance `v_s`.

The proof compares it with the centred gap at the nearest particle `J`. The nearest-particle
selection identity `E f(X_J) = E[w_1 f(X_1)]` and the uniform bias bound
`|E[w_1 f(X_1)] - E f(X_1)| → 0` over bounded Lipschitz tests give `E f(X_1) - E f(X_J) → 0`.
Since `X_J` converges in law (`selected_gap_law_of_variance_clt`), so does `X_1`, by the
test-function criterion `convergesInLaw_of_blTest`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

namespace Riesz1

/-- The block sum over the first `k` gaps at a label is the block length. -/
lemma gapOf_gapFrom_nat {N : ℕ+} (X : Configuration N) (i : ℤ) (r : ℕ) :
    gapOf (gapFrom X i) (r : ℤ) = gap X (i + r) := by
  have h : gapOf (gapFrom X i) ((0 : ℤ) + r) = gap X (i + 0 + r) := by
    rw [gapFrom_eq_shiftFin, gapOf_shiftFin, ← gap_eq_gapOf_gapVector, add_assoc]
  simpa using h

/-- The measurability of a coordinate of the gap vector at an integer label. -/
lemma measurable_gapOf_coord {N : ℕ+} (r : ℤ) :
    Measurable (fun g : Fin (N : ℕ) → ℝ => gapOf g r) :=
  measurable_pi_apply _

/-- The nearest-particle selection identity for a centred gap functional:
`E f(X_J) = E[w_1 f(X_1)]` for every bounded measurable `f`, with `X_J` the centred gap at the
nearest particle and `X_1` the centred gap at the label `0`. -/
theorem selection_centeredGap (P : Parameters) {N : ℕ+} (hN : 2 ≤ (N : ℕ)) (σ : RieszExponent)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ (N : ℕ) / 2) (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    ∫ X, f (centeredGap σ X (nearestLabel X) k hk) ∂(gibbsMeasure P N) =
      ∫ X, selectionWeight X 0 * f (centeredGap σ X 0 k hk) ∂(gibbsMeasure P N) := by
  let F : (Fin (N : ℕ) → ℝ) → ℝ := fun g =>
    f ((∑ r ∈ range k, gapOf g (r : ℤ) - (k : ℝ)) / gapScale σ N k)
  have hg : Measurable (fun g : Fin (N : ℕ) → ℝ =>
      (∑ r ∈ range k, gapOf g (r : ℤ) - (k : ℝ)) / gapScale σ N k) :=
    ((Finset.measurable_sum (range k) fun r _ => measurable_gapOf_coord (N := N) (r : ℤ)).sub_const
      _).div_const _
  have hF : Measurable F := hf.comp hg
  have hsel := nearest_selection_bounded P hN F hF 1 fun g => hb _
  have e1 : ∀ X : Configuration N,
      F (gapFrom X (nearestLabel X)) = f (centeredGap σ X (nearestLabel X) k hk) := by
    intro X
    simp only [F, centeredGap]
    congr 2
    simp only [gapOf_gapFrom_nat]
    rw [← blockLength_eq_sum]
  have e0 : ∀ X : Configuration N, F (gapFrom X 0) = f (centeredGap σ X 0 k hk) := by
    intro X
    simp only [F, centeredGap]
    congr 2
    simp only [gapOf_gapFrom_nat]
    rw [← blockLength_eq_sum]
  simp only [e1, e0] at hsel
  exact hsel

namespace Internal

/-- The gap assertion in the proof of Corollary 1, at the label `0`. Under the main theorems as
hypotheses (in the form of their conclusions), the Bakry–Émery criterion `hBE` and the
Prékopa–Leindler inequality `hPL`, the centred gap at the label `0`, normalized by `b_{N,k_N}`,
converges in law to the normal law of variance `v_s`. -/
theorem gap_label_zero_of_variance_clt (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hQV : Internal.QuantitativeVarianceConclusion beta s hbeta hs hs1)
    (hCLT : Internal.CLTConclusion beta s hbeta hs hs1)
    (k : ℕ+ → ℕ) (hk : ∀ N : ℕ+, 2 ≤ (N : ℕ) → 1 ≤ k N ∧ k N ≤ (N : ℕ) / 2)
    (hkt : Tendsto (fun n => k (particleNumber n)) atTop atTop) :
    ConvergesInLaw
      (fun n => (gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ (particleNumber (n + 1))).map
        (fun X => centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0
          (k (particleNumber (n + 1))) (hk _ (two_le_particleNumber_succ n))))
      (normalLaw (countVariance ⟨(beta, s), hbeta, hs, hs1⟩).toNNReal) := by
  have hJ := Internal.selected_gap_law_of_variance_clt hBE hPL beta s hbeta hs hs1 hQV hCLT k hk hkt
  set P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩ with hP
  have hPN : ∀ N : ℕ+, IsProbabilityMeasure (gibbsMeasure P N) := fun N => (modelWellDefined P N).2.2
  have hkt' : Tendsto (fun n => k (particleNumber (n + 1))) atTop atTop :=
    hkt.comp (tendsto_add_atTop_nat 1)
  have hvalid : ∀ n, 1 ≤ k (particleNumber (n + 1)) ∧
      k (particleNumber (n + 1)) ≤ ((particleNumber (n + 1) : ℕ+) : ℕ) / 2 :=
    fun n => hk _ (two_le_particleNumber_succ n)
  have hbias : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ f : ℝ → ℝ, LipschitzWith 1 f →
      (∀ t, |f t| ≤ 1) → |(∫ X, selectionWeight X 0 * f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent)
          X 0 (k (particleNumber (n + 1))) (hvalid n))
        ∂gibbsMeasure P (particleNumber (n + 1))) -
        ∫ X, f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0 (k (particleNumber (n + 1)))
          (hvalid n)) ∂gibbsMeasure P (particleNumber (n + 1))| < ε :=
    fun ε hε => gapsDisc_bias_uniform hBE hPL beta s hbeta hs hs1
      (fun n => particleNumber (n + 1)) (fun n => k (particleNumber (n + 1))) hkt' hvalid ε hε
  -- the limit law and the measurability of the two gap families
  have hlim : IsProbabilityMeasure (normalLaw (countVariance P).toNNReal) := by
    unfold normalLaw
    infer_instance
  refine convergesInLaw_of_blTest _ _ (fun n => ?_) hlim fun f hf => ?_
  · exact (Measure.isProbabilityMeasure_map_iff
      (measurable_centeredGap (⟨s, hs, hs1⟩ : RieszExponent) 0 _ _).aemeasurable).2
      (hPN _)
  · have hfc : Continuous f := hf.1.continuous
    have hfb : ∀ t, |f t| ≤ 1 := fun t => hf.2.1 t
    have hbdd : ∀ x y, dist (f x) (f y) ≤ 2 := fun x y => by
      rw [Real.dist_eq]
      linarith [abs_sub (f x) (f y), hfb x, hfb y]
    -- the selected-gap law converges against the bounded continuous test `f`
    have hJf := hJ.2.2 (BoundedContinuousFunction.mkOfBound ⟨f, hfc⟩ 2 hbdd)
    -- the two centred gaps differ by the bias, which vanishes uniformly over Lipschitz tests
    have hdiff : Tendsto (fun n =>
        (∫ X, f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0 (k (particleNumber (n + 1)))
            (hvalid n)) ∂gibbsMeasure P (particleNumber (n + 1))) -
        ∫ X, f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X (nearestLabel X)
            (k (particleNumber (n + 1))) (hvalid n)) ∂gibbsMeasure P (particleNumber (n + 1)))
        atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [hbias ε hε] with n hn
      have hLip : LipschitzWith 1 f := LipschitzWith.of_dist_le_mul fun x y => by
        simp only [Real.dist_eq, NNReal.coe_one, one_mul]
        exact abs_sub_le_of_blTest hf x y
      have hn' := hn f hLip hfb
      rw [Real.dist_eq, sub_zero,
        selection_centeredGap P (two_le_particleNumber_succ n) (⟨s, hs, hs1⟩ : RieszExponent)
          (k (particleNumber (n + 1))) (hvalid n) f hfc.measurable hfb]
      rw [abs_sub_comm]
      exact hn'
    -- the integral against the nearest-particle law is the integral against the label-zero law
    have hsplit : ∀ n, (∫ x, f x ∂((gibbsMeasure P (particleNumber (n + 1))).map
          (fun X => centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0
            (k (particleNumber (n + 1))) (hvalid n)))) =
        (∫ x, f x ∂((gibbsMeasure P (particleNumber (n + 1))).map
          (fun X => centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X (nearestLabel X)
            (k (particleNumber (n + 1))) (hvalid n)))) +
        ((∫ X, f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X 0
            (k (particleNumber (n + 1))) (hvalid n)) ∂gibbsMeasure P (particleNumber (n + 1))) -
        ∫ X, f (centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X (nearestLabel X)
            (k (particleNumber (n + 1))) (hvalid n)) ∂gibbsMeasure P (particleNumber (n + 1))) := by
      intro n
      rw [integral_map (measurable_centeredGap (⟨s, hs, hs1⟩ : RieszExponent) 0 _ _).aemeasurable
          hfc.aestronglyMeasurable,
        integral_map (measurable_centeredGap_nearest (⟨s, hs, hs1⟩ : RieszExponent) _ _).aemeasurable
          hfc.aestronglyMeasurable]
      ring
    have hfin := hJf.add hdiff
    rw [add_zero] at hfin
    exact hfin.congr fun n => (hsplit n).symm

end Internal

end Riesz1

end
end
