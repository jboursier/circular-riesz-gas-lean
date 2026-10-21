/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BoundaryCoreTests
public import Riesz1.ToMathlib.NonnegativeOperatorCore

/-!
# Reduction of the scalar boundary core to its shifted kernel

All functional analytic consequences of a vanishing shifted kernel are
proved here. The kernel condition is confined to an internal helper.
This file does not assert the scalar boundary core itself.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Riesz1

variable {N : ℕ+}

/-- Recovery of a Sobolev input from an ambient Neumann graph pair. -/
theorem hsNeumannResolvent_graph_input {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)
    {v : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))}
    {a : Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))}
    (hv : (v, a) ∈ hsNeumannGraph (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    hsNeumannResolvent _ (a + hsSobolevValue _ v) = v := by
  apply hsSobolevValue_injective χ hc
  exact (mem_hsNeumannL2Graph_iff_resolvent _ _ _).mp
    ((mem_hsNeumannL2Graph _ _ _).mpr ⟨v, rfl, hv⟩)

namespace Internal

/-- Graph approximation by the test functions gives form approximation.
The graph-to-form map is the continuous resolvent applied to `a + f`. -/
theorem dense_hsSourceTestSobolev_of_graph_closure {c : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (hcl : (hsTestL2Operator χ hc).graph.topologicalClosure = (hsNeumannL2Operator χ hc).graph) :
    Dense (hsSourceTestSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) :
      Set (HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))) := by
  let ν := (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
  let T : (Lp ℝ 2 ν × Lp ℝ 2 ν) →L[ℝ] HsSobolev ν :=
    (hsNeumannResolvent ν).comp (graphShift 1)
  have hmap : ∀ p ∈ (hsTestL2Operator χ hc).graph, T p ∈ hsSourceTestSobolev ν := by
    rintro ⟨f, a⟩ hp
    obtain ⟨hf, ha⟩ := (mem_hsTestL2Operator_graph χ hc f a).mp hp
    obtain ⟨φ, hφ⟩ := (mem_hsTestL2Domain ν f).mp hf
    rw [hsNeumannL2Operator_graph, mem_hsNeumannL2Graph] at ha
    obtain ⟨v, hv, hva⟩ := ha
    have he : v = hsSobolevOfSmooth ν ⟨φ.toFun, φ.smoothOnClosure⟩ :=
      (hsSobolevValue_injective χ hc) (hv.trans hφ.symm)
    change hsNeumannResolvent ν (a + (1 : ℝ) • f) ∈ hsSourceTestSobolev ν
    rw [one_smul, ← hv, hsNeumannResolvent_graph_input χ hc hva, he]
    exact ⟨φ, rfl⟩
  have hsub : hsNeumannDomain ν ⊆ closure (hsSourceTestSobolev ν : Set (HsSobolev ν)) := by
    intro v hv
    obtain ⟨a, ha⟩ := (hsNeumannDomain_iff ν v).mp hv
    have hp : (hsSobolevValue ν v, a) ∈
        closure ((hsTestL2Operator χ hc).graph : Set (Lp ℝ 2 ν × Lp ℝ 2 ν)) := by
      change (hsSobolevValue ν v, a) ∈ (hsTestL2Operator χ hc).graph.topologicalClosure
      rw [hcl, hsNeumannL2Operator_graph, mem_hsNeumannL2Graph]
      exact ⟨v, rfl, ha⟩
    have hTp := image_closure_subset_closure_image T.continuous ⟨_, hp, rfl⟩
    have he : T (hsSobolevValue ν v, a) = v := by
      change hsNeumannResolvent ν (a + (1 : ℝ) • hsSobolevValue ν v) = v
      rw [one_smul]
      exact hsNeumannResolvent_graph_input χ hc ha
    rw [he] at hTp
    exact closure_mono (by rintro _ ⟨p, hp, rfl⟩; exact hmap p hp) hTp
  intro v
  exact (isClosed_closure.closure_subset_iff.mpr hsub) (dense_hsNeumannDomain χ hc v)

/-- The exact remaining kernel obligation for the real quotient core
implies closure equality, essential self-adjointness, and both cores.
The hypothesis is an internal proof obligation, not an added hypothesis
on the scalar boundary core. -/
theorem scalar_boundary_core_of_shift_kernel {c : ℝ} (hN : 2 ≤ (N : ℕ))
    (χ : HsPairPotentials N c) (hc : 0 < c) {lam : ℝ} (hlam : 1 ≤ lam)
    (hker : ∀ u : Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)),
      (∀ f : HsTestFunction N,
        inner ℝ
          ((memLp_hsLangevin hN χ f
            (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))).toLp (hsLangevin χ f) +
            lam • hsSobolevValue _ (hsSobolevOfSmooth _ ⟨f.toFun, f.smoothOnClosure⟩)) u = 0) →
        u = 0) :
    (hsTestL2Operator χ hc).closure = hsNeumannL2Operator χ hc ∧
      IsSelfAdjoint (hsTestL2Operator χ hc).closure ∧
      (hsNeumannL2Operator χ hc).HasCore
        (hsTestL2Domain (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) ∧
      Dense (hsSourceTestSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) :
        Set (HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))) := by
  let ν := (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
  have hcl : (hsTestL2Operator χ hc).graph.topologicalClosure = (hsNeumannL2Operator χ hc).graph := by
    refine graph_closure_eq_of_shift_kernel _ _ (hsNeumannL2Operator_selfAdjoint χ hc).isClosed
      (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le) ?_ hlam ?_
    · rintro ⟨f, a⟩ hp
      rw [hsNeumannL2Operator_graph, mem_hsNeumannL2Graph] at hp
      obtain ⟨v, hv, ha⟩ := hp
      rw [← hv]
      exact hsNeumannGraph_nonnegative ν ⟨(_, _), ha⟩
    · intro u hu
      apply hker u
      intro f
      exact hu _ (hsTestL2Operator_on_test hN χ hc f)
  have he : (hsTestL2Operator χ hc).closure = hsNeumannL2Operator χ hc := by
    apply LinearPMap.eq_of_eq_graph
    rw [← (hsTestL2Operator_isClosable χ hc).graph_closure_eq_closure_graph, hcl]
  refine ⟨he, he ▸ hsNeumannL2Operator_selfAdjoint χ hc, ?_,
    dense_hsSourceTestSobolev_of_graph_closure χ hc hcl⟩
  exact ⟨hsTestL2Domain_le_neumann hN χ hc, he⟩

end Internal

end Riesz1
