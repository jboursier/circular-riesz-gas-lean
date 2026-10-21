/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.VarianceFiniteSum
public import Riesz1.Frozen.Variance

/-!
# The extended variance of a sum of two variables

The two-term specialization of finite variance summation. Both first
moment certificates are explicit and no conversion to real numbers is
needed.
-/

public section

open MeasureTheory

namespace Riesz1

/-- The variance of a sum is at most twice the sum of the variances. -/
theorem variance_add_le_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {F G : Ω → ℝ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    variance μ (fun x => F x+G x) ((hF.add hG).integrable one_le_two) ≤
      2*(variance μ F (hF.integrable one_le_two)+variance μ G (hG.integrable one_le_two)) := by
  let H : Fin 2 → Ω → ℝ := ![F, G]
  have hH : ∀ j, MemLp (H j) 2 μ := by
    intro j
    fin_cases j
    · exact hF
    · exact hG
  obtain ⟨hi, hv⟩ := variance_finsetSum_le μ 2 H hH
  simpa only [Fin.sum_univ_two, H, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Nat.cast_ofNat] using hv

end Riesz1
