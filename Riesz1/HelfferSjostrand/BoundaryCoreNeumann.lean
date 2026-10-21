/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BoundaryCoreResolvent
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# The ambient L² graph of the variational Neumann operator

The existing Sobolev graph is transported by its value projection. The
resolvent identifies its adjoint graph without a spectral theorem.
This is the self-adjoint-extension step of the scalar boundary core theorem.
Identification with the closure of the collision-free operator is separate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

variable {N : ℕ+} (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]

/-- The variational graph, with both entries represented in ambient `L²`. -/
def hsNeumannL2Graph : Submodule ℝ (Lp ℝ 2 μ × Lp ℝ 2 μ) :=
  (hsNeumannGraph μ).map ((hsSobolevValue μ).toLinearMap.prodMap (LinearMap.id))

theorem mem_hsNeumannL2Graph (f a : Lp ℝ 2 μ) :
    (f, a) ∈ hsNeumannL2Graph μ ↔
      ∃ v : HsSobolev μ, hsSobolevValue μ v = f ∧ (v, a) ∈ hsNeumannGraph μ := by
  constructor
  · rintro ⟨⟨v, b⟩, hvb, h⟩
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    change hsSobolevValue μ v = f at hfst
    change b = a at hsnd
    exact ⟨v, hfst, hsnd ▸ hvb⟩
  · rintro ⟨v, hv, hg⟩
    exact ⟨(v, a), hg, Prod.ext hv rfl⟩

/-- The resolvent parametrizes the entire ambient operator graph. -/
theorem mem_hsNeumannL2Graph_iff_resolvent (f a : Lp ℝ 2 μ) :
    (f, a) ∈ hsNeumannL2Graph μ ↔
      hsSobolevValue μ (hsNeumannResolvent μ (a + f)) = f := by
  rw [mem_hsNeumannL2Graph]
  constructor
  · rintro ⟨v, hv, hg⟩
    have he : hsNeumannResolvent μ (a + f) = v := by
      apply ext_inner_right ℝ
      intro h
      rw [hsNeumannResolvent, ContinuousLinearMap.adjoint_inner_left, inner_add_left,
        hsSobolev_inner_eq, hg h, hv]
      ring
    rw [he, hv]
  · intro he
    refine ⟨hsNeumannResolvent μ (a + f), he, ?_⟩
    have hg := hsNeumannResolvent_mem_graph μ (a + f)
    rwa [he, add_sub_cancel_right] at hg

/-- The bounded ambient resolvent is symmetric. -/
theorem hsNeumannResolvent_value_symmetric (g h : Lp ℝ 2 μ) :
    inner ℝ (hsSobolevValue μ (hsNeumannResolvent μ g)) h =
      inner ℝ g (hsSobolevValue μ (hsNeumannResolvent μ h)) := by
  calc
    _ = inner ℝ (hsNeumannResolvent μ g) (hsNeumannResolvent μ h) :=
      ((hsSobolevValue μ).adjoint_inner_right (hsNeumannResolvent μ g) h).symm
    _ = _ := (hsSobolevValue μ).adjoint_inner_left (hsNeumannResolvent μ h) g

/-- The ambient graph equals its Hilbert-space adjoint graph. -/
theorem hsNeumannL2Graph_adjoint : (hsNeumannL2Graph μ).adjoint = hsNeumannL2Graph μ := by
  apply le_antisymm
  · intro p hp
    rcases p with ⟨f, a⟩
    rw [mem_hsNeumannL2Graph_iff_resolvent]
    apply ext_inner_left ℝ
    intro g
    have hg : (hsSobolevValue μ (hsNeumannResolvent μ g),
        g - hsSobolevValue μ (hsNeumannResolvent μ g)) ∈ hsNeumannL2Graph μ :=
      (mem_hsNeumannL2Graph μ _ _).mpr
        ⟨_, rfl, hsNeumannResolvent_mem_graph μ g⟩
    have hh := (Submodule.mem_adjoint_iff _ _).mp hp _ _ hg
    change inner ℝ (g - hsSobolevValue μ (hsNeumannResolvent μ g)) f -
      inner ℝ (hsSobolevValue μ (hsNeumannResolvent μ g)) a = 0 at hh
    rw [inner_sub_left] at hh
    rw [← hsNeumannResolvent_value_symmetric, inner_add_right]
    linarith
  · intro p hp
    rcases p with ⟨f, a⟩
    obtain ⟨v, hv, hg⟩ := (mem_hsNeumannL2Graph μ f a).mp hp
    apply (Submodule.mem_adjoint_iff _ _).mpr
    intro h b hhb
    obtain ⟨w, hw, hwb⟩ := (mem_hsNeumannL2Graph μ h b).mp hhb
    change inner ℝ b f - inner ℝ h a = 0
    rw [← hv, ← hw]
    exact sub_eq_zero.mpr (hsNeumannGraph_symmetric μ ⟨(w, b), hwb⟩ ⟨(v, a), hg⟩)

/-- The ambient graph is single-valued, using the density in `L²`. -/
theorem hsNeumannL2Graph_zero_fst {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)
    {p : Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) ×
      Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))}
    (hp : p ∈ hsNeumannL2Graph (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (hz : p.1 = 0) : p.2 = 0 := by
  obtain ⟨v, hv, hg⟩ := (mem_hsNeumannL2Graph _ p.1 p.2).mp hp
  have hv0 : v = 0 := (hsSobolevValue_injective χ hc) (by rw [hv, hz, map_zero])
  apply Internal.formRepresentative_unique _ (denseRange_hsSobolevValue χ hc)
    (hsDirichletForm _) v
  · exact hg
  · intro h
    rw [hv0, hsDirichletForm, map_zero, inner_zero_left, inner_zero_left]

/-- The same Neumann operator as a partially defined linear map
on ambient `L²`. The graph certificate excludes any default branch. -/
def hsNeumannL2Operator {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c) :
    Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) →ₗ.[ℝ]
      Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) where
  domain := (hsNeumannL2Graph _).map (LinearMap.fst ℝ _ _)
  toFun := (hsNeumannL2Graph _).toLinearPMapAux
    (fun _ hp hz => hsNeumannL2Graph_zero_fst χ hc hp hz)

/-- The partially defined operator has exactly the existing variational graph. -/
theorem hsNeumannL2Operator_graph {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c) :
    (hsNeumannL2Operator χ hc).graph =
      hsNeumannL2Graph (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
  let ν := (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
  have hg : ∀ p, p ∈ hsNeumannL2Graph ν → p.1 = 0 → p.2 = 0 :=
    fun _ hp hz => hsNeumannL2Graph_zero_fst χ hc hp hz
  have he : hsNeumannL2Operator χ hc = (hsNeumannL2Graph ν).toLinearPMap := by
    apply LinearPMap.ext (f := hsNeumannL2Operator χ hc)
      (g := (hsNeumannL2Graph ν).toLinearPMap) rfl
    intro x hx hy
    exact (Submodule.toLinearPMap_apply_aux hg ⟨x, hx⟩).symm
  rw [he]
  exact Submodule.toLinearPMap_graph_eq _ hg

/-- Its full `L²` domain is dense. -/
theorem dense_hsNeumannL2Operator_domain {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c) :
    Dense ((hsNeumannL2Operator χ hc).domain : Set
      (Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))) := by
  let ν := (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
  have hR : DenseRange (hsNeumannResolvent ν) :=
    Internal.denseRange_adjoint_of_injective (hsSobolevValue ν) (hsSobolevValue_injective χ hc)
  have hd := (denseRange_hsSobolevValue χ hc).comp hR (hsSobolevValue ν).continuous
  apply hd.mono
  rintro _ ⟨g, rfl⟩
  change hsSobolevValue ν (hsNeumannResolvent ν g) ∈
    (hsNeumannL2Graph ν).map (LinearMap.fst ℝ _ _)
  exact ⟨(_, g - hsSobolevValue ν (hsNeumannResolvent ν g)),
    (mem_hsNeumannL2Graph ν _ _).mpr ⟨_, rfl, hsNeumannResolvent_mem_graph ν g⟩, rfl⟩

/-- The full variational Neumann operator is self-adjoint on `L²`. -/
theorem hsNeumannL2Operator_selfAdjoint {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c) :
    IsSelfAdjoint (hsNeumannL2Operator χ hc) := by
  change (hsNeumannL2Operator χ hc).adjoint = hsNeumannL2Operator χ hc
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (dense_hsNeumannL2Operator_domain χ hc),
    hsNeumannL2Operator_graph, hsNeumannL2Graph_adjoint]

/-- The value agrees with the single-valued Neumann operator. -/
theorem hsNeumannL2Operator_on_domain {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : hsNeumannDomain (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    (hsSobolevValue _ f.val, hsNeumannOperator χ hc f) ∈ (hsNeumannL2Operator χ hc).graph := by
  rw [hsNeumannL2Operator_graph, mem_hsNeumannL2Graph]
  exact ⟨f.val, rfl, hsNeumannOperator_mem_graph χ hc f⟩

end Riesz1
