/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic

/-!
# Sums over the pairs of an integer block

Reindexing consecutive integer labels by a finite type, with each unordered
pair counted once. This is used to compare block energies with their lift
coordinate formulas.
-/

public section

open Finset

namespace Riesz1.Internal

/-- Reindex the pairs of `[k,k+L]` by the ordered pairs of `Fin (L+1)`. -/
theorem sum_integer_block_pairs {A : Type*} [AddCommMonoid A]
    (k : ℤ) (L : ℕ) (f : ℤ → ℤ → A) :
    (∑ i : Fin (L + 1), ∑ j ∈ univ.filter (i < ·), f (k + i.val) (k + j.val)) =
      ∑ p ∈ Icc k (k + L), ∑ q ∈ Ioc p (k + L), f p q := by
  apply Finset.sum_bij (fun (i : Fin (L + 1)) _ => k + (i.val : ℤ))
  · intro i _
    have hi := i.isLt
    simp only [mem_Icc]
    omega
  · intro i _ j _ h
    apply Fin.ext
    omega
  · intro p hp
    simp only [mem_Icc] at hp
    refine ⟨⟨(p - k).toNat, by omega⟩, mem_univ _, ?_⟩
    dsimp
    omega
  · intro i _
    apply Finset.sum_bij (fun (j : Fin (L + 1)) _ => k + (j.val : ℤ))
    · intro j hj
      have hij := (mem_filter.mp hj).2
      have hj' := j.isLt
      simp only [mem_Ioc]
      rw [Fin.lt_def] at hij
      omega
    · intro j _ j' _ h
      apply Fin.ext
      omega
    · intro q hq
      simp only [mem_Ioc] at hq
      have hi := i.isLt
      refine ⟨⟨(q - k).toNat, by omega⟩, ?_, ?_⟩
      · apply mem_filter.mpr
        refine ⟨mem_univ _, ?_⟩
        rw [Fin.lt_def]
        dsimp
        omega
      · dsimp
        omega
    · intro j _
      rfl

end Riesz1.Internal

end
