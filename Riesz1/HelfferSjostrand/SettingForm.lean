/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Topology.DenseEmbedding

/-!
# Internal associated-operator construction

The Hilbert-space uniqueness argument, separated
from the construction of the concrete weighted Sobolev space.
The domain and operator below are defined by the variational identity itself.
None of these results asserts a density theorem for that Sobolev space.
-/

@[expose] public section

noncomputable section

namespace Riesz1.Internal

variable {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Elements of a form domain that admit an ambient Hilbert-space representative. -/
def formOperatorDomain (j : V → E) (B : V → V → ℝ) : Set V :=
  {f | ∃ a : E, ∀ h : V, B f h = inner ℝ a (j h)}

/-- Dense range alone makes the variational representative unique. -/
theorem formRepresentative_unique (j : V → E) (hj : DenseRange j) (B : V → V → ℝ)
    (f : V) {a b : E} (ha : ∀ h, B f h = inner ℝ a (j h))
    (hb : ∀ h, B f h = inner ℝ b (j h)) : a = b := by
  apply (InnerProductSpace.toDual ℝ E).injective
  ext x
  have heq : (fun x => inner ℝ a x) = fun x => inner ℝ b x :=
    hj.equalizer (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
      (funext fun h => (ha h).symm.trans (hb h))
  exact congrFun heq x

theorem formRepresentative_existsUnique (j : V → E) (hj : DenseRange j) (B : V → V → ℝ)
    (f : formOperatorDomain j B) : ∃! a : E, ∀ h : V, B f.val h = inner ℝ a (j h) := by
  obtain ⟨a, ha⟩ := f.property
  exact ⟨a, ha, fun b hb => formRepresentative_unique j hj B f.val hb ha⟩

/-- The unique ambient representative of a form, on its full variational domain. -/
def formOperator (j : V → E) (hj : DenseRange j) (B : V → V → ℝ)
    (f : formOperatorDomain j B) : E :=
  (formRepresentative_existsUnique j hj B f).exists.choose

theorem formOperator_spec (j : V → E) (hj : DenseRange j) (B : V → V → ℝ)
    (f : formOperatorDomain j B) (h : V) :
    B f.val h = inner ℝ (formOperator j hj B f) (j h) :=
  (formRepresentative_existsUnique j hj B f).exists.choose_spec h

theorem formOperator_eq_iff (j : V → E) (hj : DenseRange j) (B : V → V → ℝ)
    (f : formOperatorDomain j B) (a : E) :
    formOperator j hj B f = a ↔ ∀ h, B f.val h = inner ℝ a (j h) := by
  constructor
  · intro h
    rw [← h]
    exact formOperator_spec j hj B f
  · exact formRepresentative_unique j hj B f.val (formOperator_spec j hj B f)

/-- Symmetry of an associated operator follows from symmetry of its form. -/
theorem formOperator_symmetric (j : V → E) (hj : DenseRange j) (B : V → V → ℝ)
    (hB : ∀ f h, B f h = B h f) (f g : formOperatorDomain j B) :
    inner ℝ (formOperator j hj B f) (j g.val) =
      inner ℝ (j f.val) (formOperator j hj B g) := by
  rw [← formOperator_spec j hj B f g.val, real_inner_comm,
    ← formOperator_spec j hj B g f.val]
  exact hB _ _

theorem formOperator_nonnegative (j : V → E) (hj : DenseRange j) (B : V → V → ℝ)
    (hB : ∀ f, 0 ≤ B f f) (f : formOperatorDomain j B) :
    0 ≤ inner ℝ (formOperator j hj B f) (j f.val) := by
  rw [← formOperator_spec j hj B f f.val]
  exact hB _

end Riesz1.Internal

end
