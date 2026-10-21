/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.LipschitzClip
public import Riesz1.ToMathlib.WeightedSobolev.L2Facts
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Convergence of clipped value and gradient candidates

For any square-integrable pair `(F, G)`, clipping `F` at integer radii
and restricting `G` to the strict sublevel sets converges in the
sum-of-squares norm. This is the dominated-convergence step
for the weighted Sobolev completion. Membership of these pairs in a Sobolev
graph requires the separate chain rule and is not asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Riesz1.WeightedSobolev

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  {μ : Measure Ω} {F : Ω → ℝ} {G : Ω → E}

/-- The clipped value is square integrable. -/
theorem memLp_clipReal (hF : MemLp F 2 μ) {R : ℝ} (hR : 0 ≤ R) :
    MemLp (fun x => clipReal R (F x)) 2 μ := by
  apply (lipschitzWith_clipReal R).comp_memLp _ hF
  exact clipReal_eq_of_abs_le (by simpa using hR)

/-- The strict-sublevel gradient candidate is square integrable. -/
theorem memLp_truncatedGradient (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) (R : ℝ) :
    MemLp ({x | |F x| < R}.indicator G) 2 μ :=
  MemLp.indicator (nullMeasurableSet_lt hF.aestronglyMeasurable.norm.aemeasurable
    aemeasurable_const) hG

/-- Clipped values and the proposed truncation gradients converge in the
prescribed squared integral norm, before asserting Sobolev membership. -/
theorem tendsto_truncation_pair_error (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    Tendsto (fun n : ℕ => ∫ x,
      (clipReal (n : ℝ) (F x) - F x) ^ 2 +
        ‖({y | |F y| < (n : ℝ)}.indicator G) x - G x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  let err := fun n : ℕ => fun x => (clipReal (n : ℝ) (F x) - F x) ^ 2 +
    ‖({y | |F y| < (n : ℝ)}.indicator G) x - G x‖ ^ 2
  have hm (n : ℕ) : AEStronglyMeasurable (err n) μ :=
    (((memLp_clipReal hF (Nat.cast_nonneg n)).sub hF).aestronglyMeasurable.pow 2).add
      (((memLp_truncatedGradient hF hG n).sub hG).aestronglyMeasurable.norm.pow 2)
  have hb : Integrable (fun x => 4 * (F x) ^ 2 + ‖G x‖ ^ 2) μ :=
    (hF.integrable_sq.const_mul 4).add hG.norm.integrable_sq
  have he (n : ℕ) (x : Ω) : ‖err n x‖ ≤ 4 * (F x) ^ 2 + ‖G x‖ ^ 2 := by
    have hclip : |clipReal (n : ℝ) (F x) - F x| ≤ 2 * |F x| := by
      exact (abs_sub _ _).trans (by linarith [abs_clipReal_le (r := F x) (Nat.cast_nonneg n)])
    have hsq := mul_self_le_mul_self (abs_nonneg _) hclip
    simp only [← sq, sq_abs, mul_pow] at hsq
    have hg : ‖({y | |F y| < (n : ℝ)}.indicator G) x - G x‖ ^ 2 ≤ ‖G x‖ ^ 2 := by
      by_cases hx : |F x| < (n : ℝ)
      · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hx, sub_self,
          norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sq_nonneg]
      · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hx, zero_sub,
          norm_neg, le_refl]
    rw [Real.norm_of_nonneg (by dsimp [err]; positivity)]
    dsimp [err]
    linarith
  have hl : ∀ᵐ x ∂μ, Tendsto (fun n => err n x) atTop (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (⌈|F x|⌉₊ + 1)] with n hn
    have hh : |F x| < (n : ℝ) := by
      have hceil := Nat.le_ceil |F x|
      have hcast : (⌈|F x|⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
      linarith
    simp only [err, clipReal_eq_of_abs_le hh.le, Set.indicator_apply, Set.mem_ofPred_eq,
      ite_eq_left hh, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero]
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence (fun x => 4 * (F x) ^ 2 + ‖G x‖ ^ 2)
      hm hb (fun n => Eventually.of_forall (he n)) hl

end Riesz1.WeightedSobolev

end
