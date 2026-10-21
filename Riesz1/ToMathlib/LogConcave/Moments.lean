/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Tails and moments from an exponential moment

Let `Y ≥ 0` be a random variable with `E exp (c Y) ≤ A` for some `c > 0`. Markov's inequality
applied to `exp (c Y)` gives the tail bound `P(Y > u) ≤ A exp (-c u)`. The pointwise bound
`y ^ p ≤ (p / e) ^ p c ^ (-p) exp (c y)` for `y ≥ 0` then gives the moment bound
`E Y ^ p ≤ A (p / e) ^ p c ^ (-p)`.
-/

public section

open MeasureTheory

namespace Riesz1

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Tail bound from an exponential moment.** Let `c > 0`. Let `Y : Ω → ℝ` be a measurable,
nonnegative random variable on a probability space with `exp (c Y)` integrable and
`E exp (c Y) ≤ A`. Then for every real `u`, `P(u < Y) ≤ A exp (-c u)`. -/
theorem tail_le_of_exp_moment_le {c A : ℝ} (hc : 0 < c) (Y : Ω → ℝ) (_hY : Measurable Y)
    (_hY0 : ∀ ω, 0 ≤ Y ω) (hint : Integrable (fun ω => Real.exp (c * Y ω)) P)
    (hA : ∫ ω, Real.exp (c * Y ω) ∂P ≤ A) (u : ℝ) :
    P.real {ω | u < Y ω} ≤ A * Real.exp (-c * u) := by
  have hnn : 0 ≤ᵐ[P] fun ω => Real.exp (c * Y ω) :=
    Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnn hint (Real.exp (c * u))
  have hsub : {ω | u < Y ω} ⊆ {ω | Real.exp (c * u) ≤ Real.exp (c * Y ω)} := by
    intro ω hω
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω.le hc.le)
  have hpos : 0 < Real.exp (c * u) := Real.exp_pos _
  have hP : P.real {ω | u < Y ω} ≤ P.real {ω | Real.exp (c * u) ≤ Real.exp (c * Y ω)} :=
    measureReal_mono hsub
  -- Markov: `exp (c u) P(u < Y) ≤ E exp (c Y) ≤ A`.
  have key : Real.exp (c * u) * P.real {ω | u < Y ω} ≤ A :=
    calc Real.exp (c * u) * P.real {ω | u < Y ω}
        ≤ Real.exp (c * u) * P.real {ω | Real.exp (c * u) ≤ Real.exp (c * Y ω)} :=
          mul_le_mul_of_nonneg_left hP hpos.le
      _ ≤ ∫ ω, Real.exp (c * Y ω) ∂P := hmarkov
      _ ≤ A := hA
  have hinv : A * Real.exp (-c * u) = A / Real.exp (c * u) := by
    rw [neg_mul, Real.exp_neg, div_eq_mul_inv]
  rw [hinv, le_div_iff₀ hpos]
  linarith [mul_comm (Real.exp (c * u)) (P.real {ω | u < Y ω})]

/-- For `p > 0` and `z ≥ 0`, `z ^ p ≤ (p / e) ^ p exp z`. -/
lemma rpow_le_div_exp_mul_exp {p z : ℝ} (hp : 0 < p) (hz : 0 ≤ z) :
    z ^ p ≤ (p / Real.exp 1) ^ p * Real.exp z := by
  rcases hz.eq_or_lt with rfl | hz
  · rw [Real.zero_rpow hp.ne']
    positivity
  · rw [Real.rpow_def_of_pos hz, Real.rpow_def_of_pos (div_pos hp (Real.exp_pos 1)),
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlog : Real.log (p / Real.exp 1) = Real.log p - 1 := by
      rw [Real.log_div hp.ne' (Real.exp_pos 1).ne', Real.log_exp]
    rw [hlog]
    -- Using `log x ≤ x - 1` at `x = z / p` and multiplying by `p`.
    have hlog_le : Real.log (z / p) ≤ z / p - 1 := Real.log_le_sub_one_of_pos (div_pos hz hp)
    rw [Real.log_div hz.ne' hp.ne'] at hlog_le
    have hmul : p * (Real.log z - Real.log p) ≤ p * (z / p - 1) :=
      mul_le_mul_of_nonneg_left hlog_le hp.le
    have hcancel : p * (z / p) = z := mul_div_cancel₀ z hp.ne'
    nlinarith [hmul, hcancel]

omit [IsProbabilityMeasure P] in
/-- **Moment bound from an exponential moment.** With the hypotheses of
`Riesz1.tail_le_of_exp_moment_le`, for every `p > 0` the variable `Y ^ p` is integrable and
`E Y ^ p ≤ A (p / e) ^ p / c ^ p`. The bound holds on any measure space, so the probability
hypothesis is omitted here. -/
theorem moment_le_of_exp_moment_le {c A : ℝ} (hc : 0 < c) (Y : Ω → ℝ) (hY : Measurable Y)
    (hY0 : ∀ ω, 0 ≤ Y ω) (hint : Integrable (fun ω => Real.exp (c * Y ω)) P)
    (hA : ∫ ω, Real.exp (c * Y ω) ∂P ≤ A) (p : ℝ) (hp : 0 < p) :
    Integrable (fun ω => Y ω ^ p) P ∧
      ∫ ω, Y ω ^ p ∂P ≤ A * (p / Real.exp 1) ^ p / c ^ p := by
  set K : ℝ := (p / Real.exp 1) ^ p / c ^ p with hK
  have hK0 : 0 ≤ K := by positivity
  -- Pointwise domination `Y ^ p ≤ K exp (c Y)`, from `(c y) ^ p ≤ (p / e) ^ p exp (c y)`.
  have hbound : ∀ ω, Y ω ^ p ≤ K * Real.exp (c * Y ω) := by
    intro ω
    have hz := rpow_le_div_exp_mul_exp (z := c * Y ω) hp (mul_nonneg hc.le (hY0 ω))
    rw [Real.mul_rpow hc.le (hY0 ω)] at hz
    rw [hK, div_mul_eq_mul_div, le_div_iff₀ (Real.rpow_pos_of_pos hc p)]
    linarith [mul_comm (c ^ p) (Y ω ^ p), mul_comm ((p / Real.exp 1) ^ p) (Real.exp (c * Y ω))]
  have hmeas : AEStronglyMeasurable (fun ω => Y ω ^ p) P :=
    (hY.pow_const p).aestronglyMeasurable
  have hint' : Integrable (fun ω => K * Real.exp (c * Y ω)) P := hint.const_mul K
  have hYint : Integrable (fun ω => Y ω ^ p) P := by
    refine hint'.mono' hmeas (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hY0 ω) p)]
    exact hbound ω
  refine ⟨hYint, ?_⟩
  calc ∫ ω, Y ω ^ p ∂P ≤ ∫ ω, K * Real.exp (c * Y ω) ∂P :=
        integral_mono hYint hint' hbound
    _ = K * ∫ ω, Real.exp (c * Y ω) ∂P := integral_const_mul K _
    _ ≤ K * A := mul_le_mul_of_nonneg_left hA hK0
    _ = A * (p / Real.exp 1) ^ p / c ^ p := by rw [hK]; ring

end Riesz1
