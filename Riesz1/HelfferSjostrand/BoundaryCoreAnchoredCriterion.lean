/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BoundaryCoreAnchoredTests
public import Riesz1.ToMathlib.NonnegativeOperatorCore

/-!
# The anchored closure and form-core criterion

The shifted-kernel obligation is internal. The final
theorem must discharge it from admissibility.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1.Internal

variable {n : ℕ} {c : ℝ} (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)

/-- Graph approximation implies form approximation on the anchored Hilbert space. -/
theorem dense_anchoredSourceTestSobolev_of_graph_closure
    (hcl : (anchoredTestL2Operator χ hc).graph.topologicalClosure =
      (anchoredNeumannL2Operator χ hc).graph) :
    Dense (anchoredSourceTestSobolev χ hc : Set (PoissonAnchoredSpace χ hc)) := by
  let T : (Lp ℝ 2 (anchoredMeasureE χ) × Lp ℝ 2 (anchoredMeasureE χ)) →L[ℝ]
      PoissonAnchoredSpace χ hc := (anchoredNeumannResolvent χ hc).comp (graphShift 1)
  have hmap : ∀ p ∈ (anchoredTestL2Operator χ hc).graph,
      T p ∈ anchoredSourceTestSobolev χ hc := by
    rintro ⟨f, a⟩ hp
    obtain ⟨hf, ha⟩ := (mem_anchoredTestL2Operator_graph χ hc f a).mp hp
    obtain ⟨φ, hφ⟩ := (mem_anchoredTestL2Domain χ hc f).mp hf
    rw [anchoredNeumannL2Operator_graph, mem_anchoredNeumannL2Graph] at ha
    obtain ⟨v, hv, hva⟩ := ha
    have he : v = anchoredTestHilbert χ hc φ :=
      poissonAnchoredValue_injective χ hc (hv.trans hφ.symm)
    change anchoredNeumannResolvent χ hc (a + (1 : ℝ) • f) ∈ anchoredSourceTestSobolev χ hc
    rw [one_smul, ← hv, anchoredNeumannResolvent_graph_input χ hc hva, he]
    exact ⟨φ, rfl⟩
  have hsub : range (anchoredNeumannResolvent χ hc) ⊆
      closure (anchoredSourceTestSobolev χ hc : Set (PoissonAnchoredSpace χ hc)) := by
    rintro _ ⟨g, rfl⟩
    let v := anchoredNeumannResolvent χ hc g
    let f := poissonAnchoredValue χ hc v
    let a := g - f
    have ha : (v, a) ∈ anchoredNeumannHilbertGraph χ hc :=
      anchoredNeumannResolvent_mem_graph χ hc g
    have hp : (f, a) ∈ closure ((anchoredTestL2Operator χ hc).graph : Set _) := by
      change (f, a) ∈ (anchoredTestL2Operator χ hc).graph.topologicalClosure
      rw [hcl, anchoredNeumannL2Operator_graph, mem_anchoredNeumannL2Graph]
      exact ⟨v, rfl, ha⟩
    have hTp := image_closure_subset_closure_image T.continuous ⟨_, hp, rfl⟩
    have he : T (f, a) = v := by
      change anchoredNeumannResolvent χ hc (a + (1 : ℝ) • f) = v
      rw [one_smul]
      exact anchoredNeumannResolvent_graph_input χ hc ha
    rw [he] at hTp
    exact closure_mono (by rintro _ ⟨p, hp, rfl⟩; exact hmap p hp) hTp
  have hd : DenseRange (anchoredNeumannResolvent χ hc) :=
    denseRange_adjoint_of_injective _ (poissonAnchoredValue_injective χ hc)
  intro v
  exact (isClosed_closure.closure_subset_iff.mpr hsub) (hd v)

/-- The precise anchored shifted-kernel obligation gives the operator and form cores. -/
theorem anchored_boundary_core_of_shift_kernel {lam : ℝ} (hlam : 1 ≤ lam)
    (hker : ∀ u : Lp ℝ 2 (anchoredMeasureE χ),
      (∀ f : anchoredTestSubmodule n,
        inner ℝ
          ((memLp_anchoredLangevinExpr χ hc f.property.1 f.property.2.1 f.property.2.2).toLp
            (anchoredLangevinExpr χ f.val) +
              lam • poissonAnchoredValue χ hc (anchoredTestHilbert χ hc f)) u = 0) → u = 0) :
    (anchoredTestL2Operator χ hc).closure = anchoredNeumannL2Operator χ hc ∧
      IsSelfAdjoint (anchoredTestL2Operator χ hc).closure ∧
      (anchoredNeumannL2Operator χ hc).HasCore (anchoredTestL2Domain χ hc) ∧
      Dense (anchoredSourceTestSobolev χ hc : Set (PoissonAnchoredSpace χ hc)) := by
  have hcl : (anchoredTestL2Operator χ hc).graph.topologicalClosure =
      (anchoredNeumannL2Operator χ hc).graph := by
    refine graph_closure_eq_of_shift_kernel _ _ (anchoredNeumannL2Operator_selfAdjoint χ hc).isClosed
      (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le) ?_ hlam ?_
    · rintro ⟨f, a⟩ hp
      rw [anchoredNeumannL2Operator_graph, mem_anchoredNeumannL2Graph] at hp
      obtain ⟨v, hv, ha⟩ := hp
      rw [← hv, ← ha v]
      exact real_inner_self_nonneg
    · intro u hu
      apply hker u
      intro f
      exact hu _ (anchoredTestL2Operator_on_test χ hc f)
  have he : (anchoredTestL2Operator χ hc).closure = anchoredNeumannL2Operator χ hc := by
    apply LinearPMap.eq_of_eq_graph
    rw [← (anchoredTestL2Operator_isClosable χ hc).graph_closure_eq_closure_graph, hcl]
  exact ⟨he, he ▸ anchoredNeumannL2Operator_selfAdjoint χ hc,
    ⟨anchoredTestL2Domain_le_neumann χ hc, he⟩,
    dense_anchoredSourceTestSobolev_of_graph_closure χ hc hcl⟩

end Riesz1.Internal
