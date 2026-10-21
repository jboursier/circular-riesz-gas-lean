/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleInnerMarkSeparation
public import Mathlib.Data.Finset.Sort

/-!
# Selecting the fixed interior marks

Retain real marks in a fixed inner interval and
include zero to ensure a nonempty family. Sorting the finite set removes
duplicates and fixes an enumeration before every observation circle.
The analytic preservation of transport regularity is a separate step.
-/

public section

namespace Riesz1.Internal

/-- A fixed nonempty, uniformly separated inner marked family containing
every original real mark in the inner interval. Repetitions in the original
data are allowed. Zero supplies a harmless additional smooth mark. -/
theorem regMicro_select_inner_marks {ι : Type*} [Fintype ι]
    (a : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) (hrhalf : r < 1/2) :
    ∃ (n : ℕ+) (b : Fin (n : ℕ) → ℝ) (δ : ℝ),
      0 < δ ∧ Function.Injective b ∧ (∀ j, |b j| ≤ r) ∧
      (∃ j, b j = 0) ∧
      (∀ i, |a i| ≤ r → ∃ j, b j = a i) ∧
      (∀ j, b j = 0 ∨ ∃ i, b j = a i ∧ |a i| ≤ r) ∧
      ∀ (L : ℝ), 1 ≤ L → ∀ i j, i ≠ j →
        δ ≤ dist (b i : AddCircle L) (b j : AddCircle L) := by
  classical
  let S := insert 0 ((Finset.univ.image a).filter (fun x => |x| ≤ r))
  have hS : 0 < S.card := Finset.card_pos.mpr ⟨0, Finset.mem_insert_self _ _⟩
  let n : ℕ+ := ⟨S.card, hS⟩
  let b : Fin (n : ℕ) → ℝ := S.orderEmbOfFin rfl
  have hb : Function.Injective b := (S.orderEmbOfFin rfl).injective
  have hmem (j : Fin (n : ℕ)) : b j ∈ S := S.orderEmbOfFin_mem rfl j
  have hcover (x : ℝ) (hx : x ∈ S) : ∃ j, b j = x := by
    have hh : x ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [S.range_orderEmbOfFin rfl]
      exact hx
    exact hh
  have hinner (j : Fin (n : ℕ)) : |b j| ≤ r := by
    rcases Finset.mem_insert.mp (hmem j) with he | he
    · simpa only [he, abs_zero] using hr
    · exact (Finset.mem_filter.mp he).2
  obtain ⟨δ, hδ, hsep⟩ := exists_uniform_circle_separation_of_inner b hb hrhalf hinner
  refine ⟨n, b, δ, hδ, hb, hinner, hcover 0 (Finset.mem_insert_self _ _), ?_, ?_, hsep⟩
  · intro i hi
    apply hcover
    exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩)
  · intro j
    rcases Finset.mem_insert.mp (hmem j) with he | he
    · exact Or.inl he
    · obtain ⟨hm, hi⟩ := Finset.mem_filter.mp he
      obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hm
      exact Or.inr ⟨i, heq.symm, heq ▸ hi⟩

end Riesz1.Internal
