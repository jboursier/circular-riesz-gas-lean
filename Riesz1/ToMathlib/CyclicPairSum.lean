/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic

/-!
# Summing a translation invariant pair function

A pair function depending only on the group difference has one copy of each
nonzero displacement per starting point. The zero diagonal is omitted explicitly.
-/

public section

open scoped BigOperators

namespace Riesz1

/-- Count all ordered pairs by displacement in a finite additive group. -/
lemma sum_offDiag_eq_card_mul_sum {G : Type*} [Fintype G] [DecidableEq G] [AddGroup G]
    (f : G → G → ℝ) (q : G → ℝ) (hq : q 0 = 0)
    (hf : ∀ i j, f i j = q (j - i)) :
    (∑ p ∈ (Finset.univ : Finset G).offDiag, f p.1 p.2) =
      (Fintype.card G : ℝ) * ∑ k : G, q k := by
  classical
  have he : (∑ p ∈ (Finset.univ : Finset G).offDiag, f p.1 p.2) =
      ∑ p ∈ (Finset.univ : Finset G) ×ˢ Finset.univ, f p.1 p.2 := by
    apply Finset.sum_subset
    · intro p _
      simp
    · intro p _ hp
      have hd : p.1 = p.2 := by simpa only [Finset.mem_offDiag, Finset.mem_univ,
        true_and, not_not] using hp
      rw [hd, hf, sub_self, hq]
  rw [he, Finset.sum_product]
  simp_rw [hf]
  have hi (i : G) : (∑ j : G, q (j - i)) = ∑ k : G, q k :=
    (Equiv.subRight i).sum_comp q
  simp_rw [hi]
  simp [nsmul_eq_mul]

end Riesz1
