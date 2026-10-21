/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Distribution functions at moving thresholds

Three general facts used to pass from convergence in law to convergence of probabilities of
events with thresholds that depend on the index.

* `tendsto_cdf_moving`: monotone distribution functions converging pointwise to a continuous limit
  converge along any moving threshold `c_n → c`.
* `gaussianReal_cdf_neg`: the centred normal law is symmetric, `1 - Φ(-x) = Φ(x)`.
* `sandwich_toReal_le`: an event `{G ≤ u}` is sandwiched between two integer threshold events of
  the form `{r ≤ Δ}` up to an increment event, under an identity relating the three.
-/

@[expose] public section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace Riesz1

/-- Monotone functions `F n` that converge pointwise to a continuous `Φ` converge along thresholds
`c n → c`: the squeeze `F n (c - δ) ≤ F n (c n) ≤ F n (c + δ)` gives the limit `Φ c`, and the
continuity of `Φ` lets `δ` tend to zero. -/
theorem tendsto_cdf_moving {F : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ} (hmono : ∀ n, Monotone (F n))
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (Φ x))) (hΦ : Continuous Φ)
    {c : ℕ → ℝ} {c₀ : ℝ} (hc : Tendsto c atTop (𝓝 c₀)) :
    Tendsto (fun n => F n (c n)) atTop (𝓝 (Φ c₀)) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- lower bound: pick a point `y < c₀` with `Φ y > a`
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
      ((hΦ.tendsto c₀).eventually (lt_mem_nhds ha))
    have hy : a < Φ (c₀ - δ / 2) := hball (by
      rw [Real.dist_eq]
      rw [show c₀ - δ / 2 - c₀ = -(δ / 2) by ring, abs_neg, abs_of_pos (by positivity)]
      linarith)
    filter_upwards [(hlim (c₀ - δ / 2)).eventually (lt_mem_nhds hy),
      hc.eventually (Metric.ball_mem_nhds c₀ (by positivity : (0 : ℝ) < δ / 2))] with n hn hcn
    have hle : c₀ - δ / 2 ≤ c n := by
      rw [Real.dist_eq, abs_lt] at hcn
      linarith [hcn.1]
    exact lt_of_lt_of_le hn (hmono n hle)
  · -- upper bound: pick a point `y > c₀` with `Φ y < a`
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
      ((hΦ.tendsto c₀).eventually (gt_mem_nhds ha))
    have hy : Φ (c₀ + δ / 2) < a := hball (by
      rw [Real.dist_eq]
      rw [show c₀ + δ / 2 - c₀ = δ / 2 by ring, abs_of_pos (by positivity)]
      linarith)
    filter_upwards [(hlim (c₀ + δ / 2)).eventually (gt_mem_nhds hy),
      hc.eventually (Metric.ball_mem_nhds c₀ (by positivity : (0 : ℝ) < δ / 2))] with n hn hcn
    have hle : c n ≤ c₀ + δ / 2 := by
      rw [Real.dist_eq, abs_lt] at hcn
      linarith [hcn.2]
    exact lt_of_le_of_lt (hmono n hle) hn


/-- A sequence of extended nonnegative reals tends to zero when it is eventually below every
positive real number. -/
lemma tendsto_zero_of_forall_ofReal {f : ℕ → ℝ≥0∞}
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, f n ≤ ENNReal.ofReal δ) :
    Tendsto f atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases ht : ε = ⊤
  · exact Eventually.of_forall fun n => ht ▸ le_top
  · have hδ : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' ht
    filter_upwards [h _ hδ] with n hn
    rwa [ENNReal.ofReal_toReal ht] at hn

/-- The centred normal law with positive variance is symmetric about `0` and atomless, so its
distribution function satisfies `1 - Φ(-x) = Φ(x)`. -/
theorem gaussianReal_cdf_neg {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    1 - ProbabilityTheory.cdf (gaussianReal 0 v) (-x) = ProbabilityTheory.cdf (gaussianReal 0 v) x := by
  have hprob : IsProbabilityMeasure (gaussianReal 0 v) := inferInstance
  -- the reflection leaves the law unchanged: `μ(Iic (-x)) = μ(Ici x)`
  have hsym : gaussianReal 0 v (Iic (-x)) = gaussianReal 0 v (Ici x) := by
    have h := congrArg (fun m : Measure ℝ => m (Ici x)) (gaussianReal_map_neg (μ := 0) (v := v))
    simp only [neg_zero] at h
    rw [Measure.map_apply measurable_neg measurableSet_Ici] at h
    rw [← h]
    congr 1
    ext y
    simp only [mem_preimage, mem_Iic, mem_Ici]
    constructor <;> intro hy <;> linarith
  -- no atoms: `μ{x} = 0`
  have hatom : gaussianReal 0 v {x} = 0 :=
    (gaussianReal_absolutelyContinuous 0 hv) Real.volume_singleton
  -- `μ(Ici x) + μ(Iio x) = 1` and `μ(Iic x) = μ(Iio x)`
  have hsplit : gaussianReal 0 v (Ici x) + gaussianReal 0 v (Iio x) = 1 := by
    have hd : Disjoint (Iio x) (Ici x) :=
      Set.disjoint_left.2 fun y hy1 hy2 => not_lt.2 hy2 hy1
    rw [add_comm, ← measure_union hd measurableSet_Ici, Iio_union_Ici, measure_univ]
  have hIic : gaussianReal 0 v (Iic x) = gaussianReal 0 v (Iio x) := by
    have hu : Iic x = Iio x ∪ {x} := by
      ext y
      simp only [mem_Iic, mem_union, mem_Iio, mem_singleton_iff]
      constructor
      · intro hy; rcases lt_or_eq_of_le hy with h | h
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h)
        · exact h.le
        · exact le_of_eq h
    have hd : Disjoint (Iio x) {x} := Set.disjoint_singleton_right.2 (lt_irrefl x)
    rw [hu, measure_union hd (measurableSet_singleton x), hatom, add_zero]
  -- pass to real values
  have hfin : ∀ A : Set ℝ, gaussianReal 0 v A ≠ ⊤ := fun A => measure_ne_top _ _
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real, measureReal_def,
    measureReal_def, hsym]
  have hIic' : (gaussianReal 0 v (Iic x)).toReal = (gaussianReal 0 v (Iio x)).toReal := by
    rw [hIic]
  have hsplit' : (gaussianReal 0 v (Ici x)).toReal + (gaussianReal 0 v (Iio x)).toReal = 1 := by
    rw [← ENNReal.toReal_add (hfin _) (hfin _), hsplit, ENNReal.toReal_one]
  linarith

/-- The probability that an integer-valued variable is at least `r` is one minus the probability
that it is at most `r - 1`. -/
theorem int_ge_toReal_eq_one_sub {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {Δ : Ω → ℤ} (hΔ : Measurable Δ) (r : ℤ) :
    (μ {ω | r ≤ Δ ω}).toReal = 1 - (μ {ω | Δ ω ≤ r - 1}).toReal := by
  have hcompl : {ω | Δ ω ≤ r - 1} = {ω | r ≤ Δ ω}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, not_le]
    omega
  have hmeas : MeasurableSet {ω | r ≤ Δ ω} := measurableSet_le measurable_const hΔ
  rw [hcompl, prob_compl_eq_one_sub hmeas, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
    ENNReal.toReal_one, sub_sub_cancel]

/-- A sandwich for an event `{G ≤ u}` by integer threshold events for a variable `Δ`, with the
increments `T r` entering through the identity `r ≤ Δ ↔ G + r/b + T r ≤ 0`. The thresholds
`rLow, rHigh` satisfy `rLow/b ≤ -(u + ε)` and `-(u - ε) ≤ rHigh/b`. The increment events are `{ε ≤ |T r|}`. -/
theorem sandwich_toReal_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G Δ : Ω → ℝ) (T : ℤ → Ω → ℝ) {u ε : ℝ} (_hε : 0 < ε) (rLow rHigh : ℤ)
    (b : ℝ) (_hb : 0 < b)
    (hidLow : ∀ ω, (rLow : ℝ) ≤ Δ ω ↔ G ω + (rLow : ℝ) / b + T rLow ω ≤ 0)
    (hidHigh : ∀ ω, (rHigh : ℝ) ≤ Δ ω ↔ G ω + (rHigh : ℝ) / b + T rHigh ω ≤ 0)
    (hLow : (rLow : ℝ) / b ≤ -(u + ε)) (hHigh : -(u - ε) ≤ (rHigh : ℝ) / b) :
    (μ {ω | G ω ≤ u}).toReal ≤
        (μ {ω | (rLow : ℝ) ≤ Δ ω}).toReal + (μ {ω | ε ≤ |T rLow ω|}).toReal ∧
      (μ {ω | (rHigh : ℝ) ≤ Δ ω}).toReal ≤
        (μ {ω | G ω ≤ u}).toReal + (μ {ω | ε ≤ |T rHigh ω|}).toReal := by
  have hfin : ∀ A : Set Ω, μ A ≠ ⊤ := fun A => measure_ne_top _ _
  have hlow : {ω | G ω ≤ u} ⊆ {ω | (rLow : ℝ) ≤ Δ ω} ∪ {ω | ε ≤ |T rLow ω|} := by
    intro ω hω
    by_cases hτ : ε ≤ |T rLow ω|
    · exact Or.inr hτ
    · left
      have hτ' : |T rLow ω| < ε := not_le.1 hτ
      have hT : T rLow ω < ε := (lt_of_le_of_lt (le_abs_self _) hτ')
      have hGu : G ω ≤ u := hω
      show (rLow : ℝ) ≤ Δ ω
      rw [hidLow]
      have hdiv : (rLow : ℝ) / b ≤ -(u + ε) := hLow
      linarith
  have hhigh : {ω | (rHigh : ℝ) ≤ Δ ω} ⊆ {ω | G ω ≤ u} ∪ {ω | ε ≤ |T rHigh ω|} := by
    intro ω hω
    by_cases hτ : ε ≤ |T rHigh ω|
    · exact Or.inr hτ
    · left
      have hτ' : |T rHigh ω| < ε := not_le.1 hτ
      have hT : -ε < T rHigh ω := by
        have := neg_abs_le (T rHigh ω)
        linarith
      have hr : G ω + (rHigh : ℝ) / b + T rHigh ω ≤ 0 := (hidHigh ω).1 hω
      show G ω ≤ u
      linarith
  have h1 : (μ {ω | G ω ≤ u}).toReal ≤
      (μ ({ω | (rLow : ℝ) ≤ Δ ω} ∪ {ω | ε ≤ |T rLow ω|})).toReal :=
    ENNReal.toReal_mono (hfin _) (measure_mono hlow)
  have h2 : (μ ({ω | (rLow : ℝ) ≤ Δ ω} ∪ {ω | ε ≤ |T rLow ω|})).toReal ≤
      (μ {ω | (rLow : ℝ) ≤ Δ ω}).toReal + (μ {ω | ε ≤ |T rLow ω|}).toReal := by
    rw [← ENNReal.toReal_add (hfin _) (hfin _)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin _, hfin _⟩) (measure_union_le _ _)
  have h3 : (μ {ω | (rHigh : ℝ) ≤ Δ ω}).toReal ≤
      (μ ({ω | G ω ≤ u} ∪ {ω | ε ≤ |T rHigh ω|})).toReal :=
    ENNReal.toReal_mono (hfin _) (measure_mono hhigh)
  have h4 : (μ ({ω | G ω ≤ u} ∪ {ω | ε ≤ |T rHigh ω|})).toReal ≤
      (μ {ω | G ω ≤ u}).toReal + (μ {ω | ε ≤ |T rHigh ω|}).toReal := by
    rw [← ENNReal.toReal_add (hfin _) (hfin _)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin _, hfin _⟩) (measure_union_le _ _)
  exact ⟨le_trans h1 h2, le_trans h3 h4⟩

end Riesz1

end
