/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

/-!
# Products of numbers in the unit interval

A finite product of real numbers in `[0, 1]` lies in `[0, 1]`. Mathlib's `Finset.prod_le_one`
needs an ordered monoid structure that `ℝ` lacks under multiplication, so this is proved directly.
It is used for the good-event cutoff of Lemma 5.2.
-/

@[expose] public section

noncomputable section

namespace Riesz1

/-- **Product bound in the unit interval.** If every factor `f i` with `i ∈ s` lies in `[0, 1]`,
then the product over `s` lies in `[0, 1]`. -/
theorem prod_mem_unitInterval {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    0 ≤ ∏ i ∈ s, f i ∧ ∏ i ∈ s, f i ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    obtain ⟨ih0, ih1⟩ := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have ha0 := h0 a (Finset.mem_insert_self a s)
    have ha1 := h1 a (Finset.mem_insert_self a s)
    constructor
    · exact mul_nonneg ha0 ih0
    · nlinarith

/-- A product of two numbers in `[0, 1]` lies in `[0, 1]`. -/
theorem mul_le_one_of_unitInterval {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb1 : b ≤ 1) :
    a * b ≤ 1 := by
  nlinarith

end Riesz1

end
end
