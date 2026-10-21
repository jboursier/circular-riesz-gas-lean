/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Tail bounds for probability measures

General tail bounds used by the probability estimate of Lemma 5.2.
They hold on an arbitrary measurable space.

* `measure_le_ofReal_of_real_le` turns a bound on the real measure of a set into a bound on its
  extended measure, for a finite measure.
* `measure_le_ofReal_div_of_lintegral_le` is Markov's inequality for a measurable real function,
  with a bound on its lower Lebesgue integral.
* `sum_measure_le_ofReal_of_card_le` bounds a finite union of sets, each of small measure, by a
  count times that measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A bound on the real measure of a set gives the same bound on the extended measure, for a
finite measure. -/
theorem measure_le_ofReal_of_real_le (μ : Measure Ω) [IsFiniteMeasure μ] (s : Set Ω) {x : ℝ}
    (h : μ.real s ≤ x) : μ s ≤ ENNReal.ofReal x := by
  have h' : (μ s).toReal ≤ x := h
  calc μ s = ENNReal.ofReal (μ s).toReal := (ENNReal.ofReal_toReal (measure_ne_top μ s)).symm
    _ ≤ ENNReal.ofReal x := ENNReal.ofReal_le_ofReal h'

/-- **Markov's inequality** in the form used for inverse moments. If the lower integral of `f`
is at most `C` and `0 < c`, then `μ {c ≤ f}` is at most `C / c`. -/
theorem measure_le_ofReal_div_of_lintegral_le (μ : Measure Ω) {f : Ω → ℝ} (hf : Measurable f)
    {C c : ℝ} (hc : 0 < c) (hint : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal C) :
    μ {x | c ≤ f x} ≤ ENNReal.ofReal (C / c) := by
  have hε0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have hM := meas_ge_le_lintegral_div (μ := μ) hf.ennreal_ofReal.aemeasurable hε0
    ENNReal.ofReal_ne_top
  calc μ {x | c ≤ f x} ≤ μ {x | ENNReal.ofReal c ≤ ENNReal.ofReal (f x)} :=
        measure_mono fun x hx => ENNReal.ofReal_le_ofReal (show c ≤ f x from hx)
    _ ≤ (∫⁻ x, ENNReal.ofReal (f x) ∂μ) / ENNReal.ofReal c := hM
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal c := ENNReal.div_le_div_right hint _
    _ = ENNReal.ofReal (C / c) := (ENNReal.ofReal_div_of_pos hc).symm

/-- **Sum of tail bounds.** If each of the `card s` sets has measure at most `ofReal a`, and
`card s ≤ n`, then their sum has measure at most `ofReal (n a)`. -/
theorem sum_measure_le_ofReal_of_card_le (μ : Measure Ω) {ι : Type*} (s : Finset ι)
    (f : ι → Set Ω) {a n : ℝ} (ha : 0 ≤ a) (hn : (s.card : ℝ) ≤ n)
    (hf : ∀ i ∈ s, μ (f i) ≤ ENNReal.ofReal a) :
    ∑ i ∈ s, μ (f i) ≤ ENNReal.ofReal (n * a) := by
  calc ∑ i ∈ s, μ (f i) ≤ ∑ _i ∈ s, ENNReal.ofReal a := Finset.sum_le_sum hf
    _ = (s.card : ENNReal) * ENNReal.ofReal a := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal (s.card * a) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (n * a) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hn ha)

end Riesz1

end
end
