/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.Variance
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic

/-!
# Variance of a three-term remainder

The elementary measure-theoretic step of Proposition 5.6.
Finiteness is established before passing from the extended variance
to its real value. All statements hold on an arbitrary finite measure space.
-/

public section

open MeasureTheory

namespace Riesz1

/-- A square-integrable variable has finite variance. -/
theorem variance_ne_top_of_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {F : Ω → ℝ} (hF : MemLp F 2 μ) :
    variance μ F (hF.integrable one_le_two) ≠ ⊤ := by
  rw [variance, ← ProbabilityTheory.evariance_eq_lintegral_ofReal]
  exact hF.evariance_ne_top

/-- The real value of the variance is its centered square integral. -/
theorem variance_toReal_of_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {F : Ω → ℝ} (hF : MemLp F 2 μ) :
    (variance μ F (hF.integrable one_le_two)).toReal =
      ∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ := by
  rw [variance, ← ProbabilityTheory.evariance_eq_lintegral_ofReal]
  exact ProbabilityTheory.variance_eq_integral hF.aemeasurable

/-- Centering and Cauchy--Schwarz for three summands. The scalar factors
are unrestricted, and no independence is required. -/
theorem centeredIntegral_three_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {E A Q : Ω → ℝ}
    (hE : MemLp E 2 μ) (hA : MemLp A 2 μ) (hQ : MemLp Q 2 μ) (a β : ℝ) :
    (∫ x, ((E x - a * (β * A x - Q x)) -
      ∫ y, (E y - a * (β * A y - Q y)) ∂μ) ^ 2 ∂μ) ≤
      3 * (∫ x, (E x - ∫ y, E y ∂μ) ^ 2 ∂μ) +
      3 * a ^ 2 * β ^ 2 * (∫ x, (A x - ∫ y, A y ∂μ) ^ 2 ∂μ) +
      3 * a ^ 2 * (∫ x, (Q x - ∫ y, Q y ∂μ) ^ 2 ∂μ) := by
  have hEc := hE.sub (memLp_const (∫ x, E x ∂μ))
  have hAc := hA.sub (memLp_const (∫ x, A x ∂μ))
  have hQc := hQ.sub (memLp_const (∫ x, Q x ∂μ))
  have hR := hE.sub ((hA.const_mul β).sub hQ |>.const_mul a)
  have hiβA : Integrable (fun x => β * A x) μ := (hA.const_mul β).integrable one_le_two
  have hiβAQ : Integrable (fun x => β * A x - Q x) μ :=
    hiβA.sub (hQ.integrable one_le_two)
  have hiaβAQ : Integrable (fun x => a * (β * A x - Q x)) μ := hiβAQ.const_mul a
  have hmean : (∫ y, (E y - a * (β * A y - Q y)) ∂μ) =
      (∫ y, E y ∂μ) - a * (β * (∫ y, A y ∂μ) - ∫ y, Q y ∂μ) := by
    rw [integral_sub (hE.integrable one_le_two) hiaβAQ,
      integral_const_mul, integral_sub hiβA
        (hQ.integrable one_le_two), integral_const_mul]
  have hb (x : Ω) : ((E x - a * (β * A x - Q x)) -
      ∫ y, (E y - a * (β * A y - Q y)) ∂μ) ^ 2 ≤
      3 * (E x - ∫ y, E y ∂μ) ^ 2 +
      3 * a ^ 2 * β ^ 2 * (A x - ∫ y, A y ∂μ) ^ 2 +
      3 * a ^ 2 * (Q x - ∫ y, Q y ∂μ) ^ 2 := by
    rw [hmean]
    nlinarith [sq_nonneg ((E x - ∫ y, E y ∂μ) + a * β * (A x - ∫ y, A y ∂μ)),
      sq_nonneg ((E x - ∫ y, E y ∂μ) - a * (Q x - ∫ y, Q y ∂μ)),
      sq_nonneg (a * β * (A x - ∫ y, A y ∂μ) + a * (Q x - ∫ y, Q y ∂μ))]
  have hiE : Integrable (fun x => 3 * (E x - ∫ y, E y ∂μ) ^ 2) μ :=
    hEc.integrable_sq.const_mul 3
  have hiA : Integrable (fun x => 3 * a ^ 2 * β ^ 2 * (A x - ∫ y, A y ∂μ) ^ 2) μ :=
    hAc.integrable_sq.const_mul (3 * a ^ 2 * β ^ 2)
  have hiQ : Integrable (fun x => 3 * a ^ 2 * (Q x - ∫ y, Q y ∂μ) ^ 2) μ :=
    hQc.integrable_sq.const_mul (3 * a ^ 2)
  have hiEA : Integrable (fun x => 3 * (E x - ∫ y, E y ∂μ) ^ 2 +
      3 * a ^ 2 * β ^ 2 * (A x - ∫ y, A y ∂μ) ^ 2) μ := hiE.add hiA
  calc
    _ ≤ ∫ x, (3 * (E x - ∫ y, E y ∂μ) ^ 2 +
        3 * a ^ 2 * β ^ 2 * (A x - ∫ y, A y ∂μ) ^ 2 +
        3 * a ^ 2 * (Q x - ∫ y, Q y ∂μ) ^ 2) ∂μ :=
      integral_mono (hR.sub (memLp_const _)).integrable_sq
        (((hEc.integrable_sq.const_mul 3).add
          (hAc.integrable_sq.const_mul (3 * a ^ 2 * β ^ 2))).add
          (hQc.integrable_sq.const_mul (3 * a ^ 2))) hb
    _ = _ := by
      rw [integral_add hiEA hiQ, integral_add hiE hiA]
      simp only [integral_const_mul]

end Riesz1
