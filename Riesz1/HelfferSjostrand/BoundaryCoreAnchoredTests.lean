/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BoundaryCoreAnchoredNeumann
public import Riesz1.HelfferSjostrand.VectorEnergyAnchored

/-!
# The anchored scalar source operator

The existing compact smooth test submodule gives the source domain in
the existing Hilbert form space and in ambient L².
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

variable {n : ℕ} {c : ℝ} (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)

/-- Inclusion of the existing anchored tests in the smooth form core. -/
def anchoredTestSmooth (n : ℕ) : anchoredTestSubmodule n →ₗ[ℝ]
    Variational.smoothCore (anchoredSimplex n) :=
  { toFun := fun f => ⟨f.val, univ, isOpen_univ, subset_univ _, f.property.1.contDiffOn⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- The actual compact smooth anchored tests as elements of the Hilbert form space. -/
def anchoredTestHilbert : anchoredTestSubmodule n →ₗ[ℝ] PoissonAnchoredSpace χ hc := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact ((Variational.smoothJet (anchoredMeasureE χ) (anchoredSimplex n)
    (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex χ)).comp (anchoredTestSmooth n)).codRestrict
      (PoissonAnchoredSpace χ hc)
      (fun f => Submodule.le_topologicalClosure _ ⟨anchoredTestSmooth n f, rfl⟩)

/-- Agreement with the anchored Sobolev test map. -/
theorem anchoredTestHilbert_equiv (f : anchoredTestSubmodule n) :
    poissonAnchoredEquiv χ hc (anchoredTestHilbert χ hc f) =
      anchoredSobolevOfTest χ hc f.val f.property.1 f.property.2.1 := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  apply Subtype.ext
  apply Prod.ext <;> apply Lp.ext
  · exact (WeightedSobolev.memLp_of_smoothNearClosure (isBounded_anchoredSimplex n)
      (ae_mem_anchoredSimplex χ) (anchoredTestSmooth n f).property).1.coeFn_toLp.trans
        (isAnchoredH1_of_testFunction χ f.val f.property.1 f.property.2.1
          inferInstance).1.coeFn_toLp.symm
  · exact (WeightedSobolev.memLp_of_smoothNearClosure (isBounded_anchoredSimplex n)
      (ae_mem_anchoredSimplex χ) (anchoredTestSmooth n f).property).2.coeFn_toLp.trans
        (isAnchoredH1_of_testFunction χ f.val f.property.1 f.property.2.1
          inferInstance).2.1.coeFn_toLp.symm

/-- The source-test subspace of the existing anchored form space. -/
def anchoredSourceTestSobolev : Submodule ℝ (PoissonAnchoredSpace χ hc) :=
  (anchoredTestHilbert χ hc).range

/-- The source-test domain in ambient anchored L². -/
def anchoredTestL2Domain : Submodule ℝ (Lp ℝ 2 (anchoredMeasureE χ)) :=
  (anchoredSourceTestSobolev χ hc).map (poissonAnchoredValue χ hc).toLinearMap

theorem mem_anchoredTestL2Domain (v : Lp ℝ 2 (anchoredMeasureE χ)) :
    v ∈ anchoredTestL2Domain χ hc ↔ ∃ f : anchoredTestSubmodule n,
      poissonAnchoredValue χ hc (anchoredTestHilbert χ hc f) = v := by
  constructor
  · rintro ⟨_, ⟨f, rfl⟩, hv⟩
    exact ⟨f, hv⟩
  · rintro ⟨f, rfl⟩
    exact ⟨_, ⟨f, rfl⟩, rfl⟩

theorem dense_anchoredTestL2Domain :
    Dense (anchoredTestL2Domain χ hc : Set (Lp ℝ 2 (anchoredMeasureE χ))) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  have hd := Internal.denseRange_of_chart_tests (anchoredMeasureE χ)
    (anchoredTestL2Domain χ hc).subtype id MeasurableEmbedding.id
    (anchoredSimplex n) (isOpen_anchoredSimplex n) (ae_mem_anchoredSimplex χ)
  apply (hd ?_).mono
  · rintro _ ⟨v, rfl⟩
    exact v.property
  · intro f hf hfc hfU
    let g : anchoredTestSubmodule n := ⟨f, hf, hfc, hfU⟩
    refine ⟨⟨_, (mem_anchoredTestL2Domain χ hc _).mpr ⟨g, rfl⟩⟩, ?_⟩
    exact (WeightedSobolev.memLp_of_smoothNearClosure (isBounded_anchoredSimplex n)
      (ae_mem_anchoredSimplex χ) (anchoredTestSmooth n g).property).1.coeFn_toLp

/-- Every anchored test has exactly its differential Neumann output. -/
theorem anchoredTestHilbert_mem_graph (f : anchoredTestSubmodule n) :
    (anchoredTestHilbert χ hc f,
      (memLp_anchoredLangevinExpr χ hc f.property.1 f.property.2.1 f.property.2.2).toLp
        (anchoredLangevinExpr χ f.val)) ∈ anchoredNeumannHilbertGraph χ hc := by
  apply (mem_anchoredNeumannHilbertGraph_iff χ hc _ _).mpr
  have he := anchoredTestHilbert_equiv χ hc f
  have h := isAnchoredLangevin_of_testFunction χ hc f.property.1 f.property.2.1 f.property.2.2
  have h' := isAnchoredLangevin_congr χ h h.1.1.coeFn_toLp.symm
    h.1.2.1.coeFn_toLp.symm h.2.1.coeFn_toLp.symm
  change IsAnchoredLangevin χ (poissonAnchoredEquiv χ hc (anchoredTestHilbert χ hc f)).val.1
    (poissonAnchoredEquiv χ hc (anchoredTestHilbert χ hc f)).val.2 _
  rw [he]
  exact h'

theorem anchoredTestL2Domain_le_neumann :
    anchoredTestL2Domain χ hc ≤ (anchoredNeumannL2Operator χ hc).domain := by
  intro v hv
  obtain ⟨f, rfl⟩ := (mem_anchoredTestL2Domain χ hc v).mp hv
  exact ⟨(_, _), (mem_anchoredNeumannL2Graph χ hc _ _).mpr
    ⟨_, rfl, anchoredTestHilbert_mem_graph χ hc f⟩, rfl⟩

/-- `L₀*` on the whole source test domain, with its actual variational output. -/
def anchoredTestL2Operator :
    Lp ℝ 2 (anchoredMeasureE χ) →ₗ.[ℝ] Lp ℝ 2 (anchoredMeasureE χ) :=
  (anchoredNeumannL2Operator χ hc).domRestrict (anchoredTestL2Domain χ hc)

theorem anchoredTestL2Operator_domain :
    (anchoredTestL2Operator χ hc).domain = anchoredTestL2Domain χ hc :=
  inf_eq_left.mpr (anchoredTestL2Domain_le_neumann χ hc)

theorem anchoredTestL2Operator_isClosable : (anchoredTestL2Operator χ hc).IsClosable :=
  (anchoredNeumannL2Operator_selfAdjoint χ hc).isClosed.isClosable.leIsClosable
    LinearPMap.domRestrict_le

theorem mem_anchoredTestL2Operator_graph (v a : Lp ℝ 2 (anchoredMeasureE χ)) :
    (v, a) ∈ (anchoredTestL2Operator χ hc).graph ↔
      v ∈ anchoredTestL2Domain χ hc ∧ (v, a) ∈ (anchoredNeumannL2Operator χ hc).graph := by
  rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
  simp only [Subtype.exists, exists_and_left, exists_eq_left]
  constructor
  · rintro ⟨hv, he⟩
    exact ⟨hv.1, hv.2, (LinearPMap.domRestrict_apply rfl).symm.trans he⟩
  · rintro ⟨hv, ha, he⟩
    exact ⟨⟨hv, ha⟩, (LinearPMap.domRestrict_apply rfl).trans he⟩

theorem anchoredTestL2Operator_on_test (f : anchoredTestSubmodule n) :
    (poissonAnchoredValue χ hc (anchoredTestHilbert χ hc f),
      (memLp_anchoredLangevinExpr χ hc f.property.1 f.property.2.1 f.property.2.2).toLp
        (anchoredLangevinExpr χ f.val)) ∈ (anchoredTestL2Operator χ hc).graph := by
  rw [mem_anchoredTestL2Operator_graph]
  refine ⟨(mem_anchoredTestL2Domain χ hc _).mpr ⟨f, rfl⟩, ?_⟩
  rw [anchoredNeumannL2Operator_graph, mem_anchoredNeumannL2Graph]
  exact ⟨_, rfl, anchoredTestHilbert_mem_graph χ hc f⟩

end Riesz1
