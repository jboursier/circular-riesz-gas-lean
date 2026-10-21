/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.PoissonEquationAnchoredSpace
public import Riesz1.HelfferSjostrand.VectorEnergyTruncationGradient
public import Riesz1.HelfferSjostrand.BoundaryCoreResolvent
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# The anchored variational operator in ambient L²

The Hilbert realization already identified with `AnchoredSobolev` supplies
the resolvent. Its graph is exactly the anchored Neumann relation.
This is the anchored extension step.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

variable {n : ℕ} {c : ℝ} (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)

/-- The value projection on the anchored Hilbert space is injective. -/
theorem poissonAnchoredValue_injective : Function.Injective (poissonAnchoredValue χ hc) := by
  intro f g h
  have hg := IsAnchoredH1.grad_ae_eq_of_value_ae_eq χ hc
    (poissonAnchoredEquiv χ hc f).property (poissonAnchoredEquiv χ hc g).property
    (MeasureTheory.Lp.ext_iff.mp h)
  apply Subtype.ext
  apply (WithLp.equiv 2 _).injective
  exact Prod.ext h (Lp.ext hg)

/-- The entire anchored form graph, in the existing Hilbert coordinates. -/
def anchoredNeumannHilbertGraph :
    Submodule ℝ (PoissonAnchoredSpace χ hc × Lp ℝ 2 (anchoredMeasureE χ)) where
  carrier := {p | ∀ h, inner ℝ (poissonAnchoredGradient χ hc p.1)
    (poissonAnchoredGradient χ hc h) = inner ℝ p.2 (poissonAnchoredValue χ hc h)}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq h
    change inner ℝ (poissonAnchoredGradient χ hc (p.1 + q.1)) _ =
      inner ℝ (p.2 + q.2) _
    rw [map_add, inner_add_left, hp, hq, inner_add_left]
  smul_mem' := by
    intro a p hp h
    change inner ℝ (poissonAnchoredGradient χ hc (a • p.1)) _ = inner ℝ (a • p.2) _
    rw [map_smul, real_inner_smul_left, hp, real_inner_smul_left]

/-- This is precisely the full anchored Neumann relation. -/
theorem mem_anchoredNeumannHilbertGraph_iff (f : PoissonAnchoredSpace χ hc)
    (a : Lp ℝ 2 (anchoredMeasureE χ)) :
    (f, a) ∈ anchoredNeumannHilbertGraph χ hc ↔
      IsAnchoredLangevin χ (poissonAnchoredValue χ hc f) (poissonAnchoredGradient χ hc f) a := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  constructor
  · intro h
    refine ⟨(poissonAnchoredEquiv χ hc f).property, Lp.memLp a, fun H K hHK => ?_⟩
    have hpair := WeightedSobolev.IsWeightedH1.congr hHK
      hHK.1.coeFn_toLp.symm hHK.2.1.coeFn_toLp.symm
    let v : PoissonAnchoredSpace χ hc :=
      (poissonAnchoredEquiv χ hc).symm ⟨(hHK.1.toLp H, hHK.2.1.toLp K), hpair⟩
    have hh := h v
    change inner ℝ (poissonAnchoredGradient χ hc f) (hHK.2.1.toLp K) =
      inner ℝ a (hHK.1.toLp H) at hh
    rw [L2.inner_def, L2.inner_def] at hh
    calc
      _ = ∫ y, inner ℝ (poissonAnchoredGradient χ hc f y) (hHK.2.1.toLp K y)
          ∂anchoredMeasureE χ := integral_congr_ae (hHK.2.1.coeFn_toLp.mono fun y hy => by dsimp only; rw [hy])
      _ = ∫ y, inner ℝ (a y) (hHK.1.toLp H y) ∂anchoredMeasureE χ := hh
      _ = _ := integral_congr_ae (hHK.1.coeFn_toLp.mono fun y hy => by dsimp only; rw [hy]; simp only [Real.inner_apply, mul_comm])
  · intro h v
    have hv := (poissonAnchoredEquiv χ hc v).property
    change IsAnchoredH1 χ (poissonAnchoredValue χ hc v) (poissonAnchoredGradient χ hc v) at hv
    change inner ℝ (poissonAnchoredGradient χ hc f) (poissonAnchoredGradient χ hc v) =
      inner ℝ a (poissonAnchoredValue χ hc v)
    simpa only [L2.inner_def, Real.inner_apply] using h.2.2 _ _ hv

/-- The anchored resolvent at `-1`, defined on all of ambient L². -/
def anchoredNeumannResolvent :
    Lp ℝ 2 (anchoredMeasureE χ) →L[ℝ] PoissonAnchoredSpace χ hc :=
  (poissonAnchoredValue χ hc).adjoint

/-- The sum of value and energy pairings is the anchored Hilbert inner product. -/
theorem poissonAnchored_inner_eq (f h : PoissonAnchoredSpace χ hc) :
    inner ℝ f h = inner ℝ (poissonAnchoredValue χ hc f) (poissonAnchoredValue χ hc h) +
      inner ℝ (poissonAnchoredGradient χ hc f) (poissonAnchoredGradient χ hc h) :=
  WithLp.prod_inner_apply f.val h.val

/-- Resolvent values solve the complete anchored Neumann equation. -/
theorem anchoredNeumannResolvent_mem_graph (g : Lp ℝ 2 (anchoredMeasureE χ)) :
    (anchoredNeumannResolvent χ hc g,
      g - poissonAnchoredValue χ hc (anchoredNeumannResolvent χ hc g)) ∈
        anchoredNeumannHilbertGraph χ hc := by
  intro h
  have he := (poissonAnchoredValue χ hc).adjoint_inner_left h g
  rw [poissonAnchored_inner_eq] at he
  change inner ℝ (poissonAnchoredValue χ hc (anchoredNeumannResolvent χ hc g)) _ +
    inner ℝ (poissonAnchoredGradient χ hc (anchoredNeumannResolvent χ hc g)) _ = _ at he
  rw [inner_sub_left]
  linarith

/-- The resolvent recovers every anchored operator-domain element. -/
theorem anchoredNeumannResolvent_graph_input {f : PoissonAnchoredSpace χ hc}
    {a : Lp ℝ 2 (anchoredMeasureE χ)} (ha : (f, a) ∈ anchoredNeumannHilbertGraph χ hc) :
    anchoredNeumannResolvent χ hc (a + poissonAnchoredValue χ hc f) = f := by
  apply ext_inner_right ℝ
  intro h
  rw [anchoredNeumannResolvent, ContinuousLinearMap.adjoint_inner_left, inner_add_left,
    poissonAnchored_inner_eq, ← ha h]
  ring

/-- The variational graph with both coordinates in ambient L². -/
def anchoredNeumannL2Graph : Submodule ℝ
    (Lp ℝ 2 (anchoredMeasureE χ) × Lp ℝ 2 (anchoredMeasureE χ)) :=
  (anchoredNeumannHilbertGraph χ hc).map
    ((poissonAnchoredValue χ hc).toLinearMap.prodMap LinearMap.id)

theorem mem_anchoredNeumannL2Graph (f a : Lp ℝ 2 (anchoredMeasureE χ)) :
    (f, a) ∈ anchoredNeumannL2Graph χ hc ↔ ∃ v : PoissonAnchoredSpace χ hc,
      poissonAnchoredValue χ hc v = f ∧ (v, a) ∈ anchoredNeumannHilbertGraph χ hc := by
  constructor
  · rintro ⟨⟨v, b⟩, hvb, h⟩
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    change poissonAnchoredValue χ hc v = f at hfst
    change b = a at hsnd
    exact ⟨v, hfst, hsnd ▸ hvb⟩
  · rintro ⟨v, hv, hg⟩
    exact ⟨(v, a), hg, Prod.ext hv rfl⟩

theorem mem_anchoredNeumannL2Graph_iff_resolvent (f a : Lp ℝ 2 (anchoredMeasureE χ)) :
    (f, a) ∈ anchoredNeumannL2Graph χ hc ↔
      poissonAnchoredValue χ hc (anchoredNeumannResolvent χ hc (a + f)) = f := by
  rw [mem_anchoredNeumannL2Graph]
  constructor
  · rintro ⟨v, hv, hg⟩
    rw [← hv, anchoredNeumannResolvent_graph_input χ hc hg]
  · intro he
    refine ⟨_, he, ?_⟩
    have hg := anchoredNeumannResolvent_mem_graph χ hc (a + f)
    rwa [he, add_sub_cancel_right] at hg

theorem anchoredNeumannResolvent_value_symmetric (g h : Lp ℝ 2 (anchoredMeasureE χ)) :
    inner ℝ (poissonAnchoredValue χ hc (anchoredNeumannResolvent χ hc g)) h =
      inner ℝ g (poissonAnchoredValue χ hc (anchoredNeumannResolvent χ hc h)) := by
  calc
    _ = inner ℝ (anchoredNeumannResolvent χ hc g) (anchoredNeumannResolvent χ hc h) :=
      ((poissonAnchoredValue χ hc).adjoint_inner_right _ h).symm
    _ = _ := (poissonAnchoredValue χ hc).adjoint_inner_left _ g

/-- The anchored graph is its own Hilbert adjoint graph. -/
theorem anchoredNeumannL2Graph_adjoint :
    (anchoredNeumannL2Graph χ hc).adjoint = anchoredNeumannL2Graph χ hc := by
  apply le_antisymm
  · rintro ⟨f, a⟩ hp
    rw [mem_anchoredNeumannL2Graph_iff_resolvent]
    apply ext_inner_left ℝ
    intro g
    have hg : (poissonAnchoredValue χ hc (anchoredNeumannResolvent χ hc g),
        g - poissonAnchoredValue χ hc (anchoredNeumannResolvent χ hc g)) ∈
          anchoredNeumannL2Graph χ hc :=
      (mem_anchoredNeumannL2Graph χ hc _ _).mpr
        ⟨_, rfl, anchoredNeumannResolvent_mem_graph χ hc g⟩
    have hh := (Submodule.mem_adjoint_iff _ _).mp hp _ _ hg
    change inner ℝ (g - poissonAnchoredValue χ hc (anchoredNeumannResolvent χ hc g)) f -
      inner ℝ (poissonAnchoredValue χ hc (anchoredNeumannResolvent χ hc g)) a = 0 at hh
    rw [inner_sub_left] at hh
    rw [← anchoredNeumannResolvent_value_symmetric, inner_add_right]
    linarith
  · rintro ⟨f, a⟩ hp
    obtain ⟨v, hv, hg⟩ := (mem_anchoredNeumannL2Graph χ hc f a).mp hp
    apply (Submodule.mem_adjoint_iff _ _).mpr
    intro h b hhb
    obtain ⟨w, hw, hwb⟩ := (mem_anchoredNeumannL2Graph χ hc h b).mp hhb
    change inner ℝ b f - inner ℝ h a = 0
    rw [← hv, ← hw]
    have e₁ := hwb v
    have e₂ := hg w
    dsimp only [Prod.fst, Prod.snd] at e₁ e₂
    exact sub_eq_zero.mpr (e₁.symm.trans
      ((real_inner_comm _ _).trans (e₂.trans (real_inner_comm _ _))))

/-- The value projection has dense range, by the chart-test criterion. -/
theorem denseRange_poissonAnchoredValue : DenseRange (poissonAnchoredValue χ hc) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  apply Internal.denseRange_of_chart_tests (anchoredMeasureE χ)
    (poissonAnchoredValue χ hc).toLinearMap id MeasurableEmbedding.id
    (anchoredSimplex n) (isOpen_anchoredSimplex n) (ae_mem_anchoredSimplex χ)
  intro f hf hfc _
  exact ⟨(poissonAnchoredEquiv χ hc).symm (anchoredSobolevOfTest χ hc f hf hfc),
    (isAnchoredH1_of_testFunction χ f hf hfc inferInstance).1.coeFn_toLp⟩

theorem anchoredNeumannL2Graph_zero_fst
    {p : Lp ℝ 2 (anchoredMeasureE χ) × Lp ℝ 2 (anchoredMeasureE χ)}
    (hp : p ∈ anchoredNeumannL2Graph χ hc) (hz : p.1 = 0) : p.2 = 0 := by
  obtain ⟨v, hv, hg⟩ := (mem_anchoredNeumannL2Graph χ hc _ _).mp hp
  have hv0 : v = 0 := poissonAnchoredValue_injective χ hc (by rw [hv, hz, map_zero])
  have he : ∀ h, inner ℝ p.2 (poissonAnchoredValue χ hc h) = 0 := by
    intro h
    rw [← hg h, hv0, map_zero, inner_zero_left]
  apply ext_inner_right ℝ
  intro h
  rw [inner_zero_left]
  exact (denseRange_poissonAnchoredValue χ hc).induction_on h
    (isClosed_eq (continuous_const.inner continuous_id) continuous_const) he

/-- The actual anchored Neumann operator as a partially defined linear map. -/
def anchoredNeumannL2Operator :
    Lp ℝ 2 (anchoredMeasureE χ) →ₗ.[ℝ] Lp ℝ 2 (anchoredMeasureE χ) where
  domain := (anchoredNeumannL2Graph χ hc).map (LinearMap.fst ℝ _ _)
  toFun := (anchoredNeumannL2Graph χ hc).toLinearPMapAux
    (fun _ hp hz => anchoredNeumannL2Graph_zero_fst χ hc hp hz)

theorem anchoredNeumannL2Operator_graph :
    (anchoredNeumannL2Operator χ hc).graph = anchoredNeumannL2Graph χ hc := by
  have hg : ∀ p, p ∈ anchoredNeumannL2Graph χ hc → p.1 = 0 → p.2 = 0 :=
    fun _ hp hz => anchoredNeumannL2Graph_zero_fst χ hc hp hz
  have he : anchoredNeumannL2Operator χ hc = (anchoredNeumannL2Graph χ hc).toLinearPMap := by
    apply LinearPMap.ext (f := anchoredNeumannL2Operator χ hc)
      (g := (anchoredNeumannL2Graph χ hc).toLinearPMap) rfl
    intro x hx hy
    exact (Submodule.toLinearPMap_apply_aux hg ⟨x, hx⟩).symm
  rw [he]
  exact Submodule.toLinearPMap_graph_eq _ hg

theorem dense_anchoredNeumannL2Operator_domain :
    Dense ((anchoredNeumannL2Operator χ hc).domain : Set (Lp ℝ 2 (anchoredMeasureE χ))) := by
  have hR : DenseRange (anchoredNeumannResolvent χ hc) :=
    Internal.denseRange_adjoint_of_injective _ (poissonAnchoredValue_injective χ hc)
  have hd := (denseRange_poissonAnchoredValue χ hc).comp hR (poissonAnchoredValue χ hc).continuous
  apply hd.mono
  rintro _ ⟨g, rfl⟩
  exact ⟨(_, _), (mem_anchoredNeumannL2Graph χ hc _ _).mpr
    ⟨_, rfl, anchoredNeumannResolvent_mem_graph χ hc g⟩, rfl⟩

/-- The anchored variational Neumann operator is self-adjoint. -/
theorem anchoredNeumannL2Operator_selfAdjoint : IsSelfAdjoint (anchoredNeumannL2Operator χ hc) := by
  change (anchoredNeumannL2Operator χ hc).adjoint = anchoredNeumannL2Operator χ hc
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (dense_anchoredNeumannL2Operator_domain χ hc),
    anchoredNeumannL2Operator_graph, anchoredNeumannL2Graph_adjoint]

/-- Agreement with the function-valued anchored Neumann operator. -/
theorem anchoredNeumannL2Operator_on_domain (f : anchoredNeumannDomain χ) :
    (f.val.val.1, anchoredNeumannOperator χ f) ∈ (anchoredNeumannL2Operator χ hc).graph := by
  rw [anchoredNeumannL2Operator_graph, mem_anchoredNeumannL2Graph]
  exact ⟨(poissonAnchoredEquiv χ hc).symm f.val, rfl,
    (mem_anchoredNeumannHilbertGraph_iff χ hc _ _).mpr (anchoredNeumannOperator_spec χ f)⟩

end Riesz1
