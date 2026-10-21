/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Conjugation of partial linear operators

The conjugated operator acts on the full inverse image of the original
domain. Its graph is specified by the actual three composing maps.
-/

@[expose] public section

namespace Riesz1

variable {𝕜 E F : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]

/-- `U A U⁻¹` on the full transported domain. -/
def conjugatePartialOperator (U : E ≃ₗ[𝕜] F) (A : E →ₗ.[𝕜] E) : F →ₗ.[𝕜] F :=
  let D := A.domain.comap U.symm.toLinearMap
  { domain := D
    toFun := U.toLinearMap.comp (A.toFun.comp
      ((U.symm.toLinearMap.comp D.subtype).codRestrict A.domain (fun x => x.property))) }

theorem mem_conjugatePartialOperator_domain (U : E ≃ₗ[𝕜] F) (A : E →ₗ.[𝕜] E) (f : F) :
    f ∈ (conjugatePartialOperator U A).domain ↔ U.symm f ∈ A.domain := Iff.rfl

theorem mem_conjugatePartialOperator_graph (U : E ≃ₗ[𝕜] F) (A : E →ₗ.[𝕜] E) (f a : F) :
    (f, a) ∈ (conjugatePartialOperator U A).graph ↔ (U.symm f, U.symm a) ∈ A.graph := by
  simp only [LinearPMap.mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left]
  constructor
  · rintro ⟨hf, ha⟩
    refine ⟨hf, ?_⟩
    apply U.injective
    exact ha.trans (U.apply_symm_apply a).symm
  · rintro ⟨hf, ha⟩
    refine ⟨hf, ?_⟩
    change U (A ⟨U.symm f, hf⟩) = a
    rw [ha, U.apply_symm_apply]

theorem conjugatePartialOperator_on_graph (U : E ≃ₗ[𝕜] F) (A : E →ₗ.[𝕜] E)
    {f a : E} (h : (f, a) ∈ A.graph) : (U f, U a) ∈ (conjugatePartialOperator U A).graph := by
  rw [mem_conjugatePartialOperator_graph, U.symm_apply_apply, U.symm_apply_apply]
  exact h

end Riesz1
