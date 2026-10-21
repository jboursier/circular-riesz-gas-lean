/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.ComplexL2Graph

/-!
# Complexification of real L² partial operators

The domain and graph are the componentwise complexifications of the
original operator. Dense domains, graph closure and self-adjointness
transfer to complex L².
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

theorem complexifyL2Graph_zero_fst (A : Lp ℝ 2 μ →ₗ.[ℝ] Lp ℝ 2 μ)
    {p : Lp ℂ 2 μ × Lp ℂ 2 μ} (hp : p ∈ complexifyL2Graph μ A.graph) (hz : p.1 = 0) : p.2 = 0 := by
  apply complexL2_ext μ
  · rw [map_zero]
    exact A.graph_fst_eq_zero_snd hp.1 (by change complexL2Re μ p.1 = 0; rw [hz, map_zero])
  · rw [map_zero]
    exact A.graph_fst_eq_zero_snd hp.2 (by change complexL2Im μ p.1 = 0; rw [hz, map_zero])

/-- The complex-linear operator whose real and imaginary parts are the original real operator. -/
def complexifyL2Operator (A : Lp ℝ 2 μ →ₗ.[ℝ] Lp ℝ 2 μ) : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ where
  domain := (complexifyL2Graph μ A.graph).map (LinearMap.fst ℂ _ _)
  toFun := (complexifyL2Graph μ A.graph).toLinearPMapAux
    (fun _ hp hz => complexifyL2Graph_zero_fst μ A hp hz)

theorem complexifyL2Operator_graph (A : Lp ℝ 2 μ →ₗ.[ℝ] Lp ℝ 2 μ) :
    (complexifyL2Operator μ A).graph = complexifyL2Graph μ A.graph := by
  have hg : ∀ p, p ∈ complexifyL2Graph μ A.graph → p.1 = 0 → p.2 = 0 :=
    fun _ hp hz => complexifyL2Graph_zero_fst μ A hp hz
  have he : complexifyL2Operator μ A = (complexifyL2Graph μ A.graph).toLinearPMap := by
    apply LinearPMap.ext (f := complexifyL2Operator μ A)
      (g := (complexifyL2Graph μ A.graph).toLinearPMap) rfl
    intro x hx hy
    exact (Submodule.toLinearPMap_apply_aux hg ⟨x, hx⟩).symm
  rw [he]
  exact Submodule.toLinearPMap_graph_eq _ hg

/-- The full complex graph is specified by the two original real graph equations. -/
theorem mem_complexifyL2Operator_graph (A : Lp ℝ 2 μ →ₗ.[ℝ] Lp ℝ 2 μ)
    (f a : Lp ℂ 2 μ) :
    (f, a) ∈ (complexifyL2Operator μ A).graph ↔
      (complexL2Re μ f, complexL2Re μ a) ∈ A.graph ∧
        (complexL2Im μ f, complexL2Im μ a) ∈ A.graph := by
  rw [complexifyL2Operator_graph]
  rfl

/-- The complexification applies the real operator separately to both components. -/
theorem complexifyL2Operator_on_pair (A : Lp ℝ 2 μ →ₗ.[ℝ] Lp ℝ 2 μ)
    {f g a b : Lp ℝ 2 μ} (hf : (f, a) ∈ A.graph) (hg : (g, b) ∈ A.graph) :
    (complexL2OfPair μ (f, g), complexL2OfPair μ (a, b)) ∈ (complexifyL2Operator μ A).graph := by
  rw [mem_complexifyL2Operator_graph]
  simp only [complexL2Re_ofPair, complexL2Im_ofPair]
  exact ⟨hf, hg⟩

theorem complexifyL2Operator_domain (A : Lp ℝ 2 μ →ₗ.[ℝ] Lp ℝ 2 μ) :
    (complexifyL2Operator μ A).domain = complexifyL2Submodule μ A.domain := by
  ext f
  rw [LinearPMap.mem_domain_iff, complexifyL2Operator_graph]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨LinearPMap.mem_domain_of_mem_graph ha.1, LinearPMap.mem_domain_of_mem_graph ha.2⟩
  · intro hf
    obtain ⟨a, ha⟩ := LinearPMap.mem_domain_iff.mp hf.1
    obtain ⟨b, hb⟩ := LinearPMap.mem_domain_iff.mp hf.2
    refine ⟨complexL2OfPair μ (a, b), ?_, ?_⟩
    · change (complexL2Re μ f, complexL2Re μ (complexL2OfPair μ (a, b))) ∈ A.graph
      rw [complexL2Re_ofPair]
      exact ha
    · change (complexL2Im μ f, complexL2Im μ (complexL2OfPair μ (a, b))) ∈ A.graph
      rw [complexL2Im_ofPair]
      exact hb

theorem dense_complexifyL2Operator_domain (A : Lp ℝ 2 μ →ₗ.[ℝ] Lp ℝ 2 μ)
    (hA : Dense (A.domain : Set (Lp ℝ 2 μ))) :
    Dense ((complexifyL2Operator μ A).domain : Set (Lp ℂ 2 μ)) := by
  have hr : DenseRange (complexL2OfPair μ) :=
    (show Function.Surjective (complexL2OfPair μ) from
      fun f => ⟨_, complexL2OfPair_re_im μ f⟩).denseRange
  have hdA : DenseRange A.domain.subtype := by
    intro x
    apply closure_mono (s := (A.domain : Set (Lp ℝ 2 μ))) ?_ (hA x)
    intro y hy
    exact ⟨⟨y, hy⟩, rfl⟩
  have hd : DenseRange (fun p : A.domain × A.domain => (p.1.val, p.2.val)) :=
    hdA.prodMap hdA
  apply (hr.comp hd (complexL2OfPair μ).continuous).mono
  rintro _ ⟨⟨r, i⟩, rfl⟩
  rw [complexifyL2Operator_domain]
  change complexL2Re μ (complexL2OfPair μ (r.val, i.val)) ∈ A.domain ∧
    complexL2Im μ (complexL2OfPair μ (r.val, i.val)) ∈ A.domain
  rw [complexL2Re_ofPair, complexL2Im_ofPair]
  exact ⟨r.property, i.property⟩

/-- Complexification preserves closability. -/
theorem complexifyL2Operator_isClosable {A : Lp ℝ 2 μ →ₗ.[ℝ] Lp ℝ 2 μ}
    (hA : A.IsClosable) : (complexifyL2Operator μ A).IsClosable := by
  refine ⟨complexifyL2Operator μ A.closure, ?_⟩
  rw [complexifyL2Operator_graph, complexifyL2Graph_closure,
    hA.graph_closure_eq_closure_graph, complexifyL2Operator_graph]

/-- The complex operator closure is exactly the complexification of the real closure. -/
theorem complexifyL2Operator_closure {A : Lp ℝ 2 μ →ₗ.[ℝ] Lp ℝ 2 μ} (hA : A.IsClosable) :
    (complexifyL2Operator μ A).closure = complexifyL2Operator μ A.closure := by
  apply LinearPMap.eq_of_eq_graph
  rw [← (complexifyL2Operator_isClosable μ hA).graph_closure_eq_closure_graph,
    complexifyL2Operator_graph, complexifyL2Graph_closure,
    hA.graph_closure_eq_closure_graph, complexifyL2Operator_graph]

/-- A real self-adjoint operator gives a complex self-adjoint operator. -/
theorem complexifyL2Operator_selfAdjoint {A : Lp ℝ 2 μ →ₗ.[ℝ] Lp ℝ 2 μ}
    (hA : IsSelfAdjoint A) : IsSelfAdjoint (complexifyL2Operator μ A) := by
  have hg : A.graph.adjoint = A.graph := by
    rw [← LinearPMap.adjoint_graph_eq_graph_adjoint hA.dense_domain]
    exact congrArg LinearPMap.graph hA
  change (complexifyL2Operator μ A).adjoint = complexifyL2Operator μ A
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (dense_complexifyL2Operator_domain μ A hA.dense_domain),
    complexifyL2Operator_graph, complexifyL2Graph_adjoint μ hg]

end Riesz1
