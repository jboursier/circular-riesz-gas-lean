/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BoundaryCoreNeumann
public import Riesz1.HelfferSjostrand.IntegrationByPartsConsequences
public import Riesz1.HelfferSjostrand.SobolevDensity

/-!
# The collision-free scalar test operator

The actual test class of the paper, as a subspace of the Sobolev space
and as a densely defined restriction of the variational Neumann operator.
This supplies the domain and operator, and the domain used in another lemma.
No boundary-core density is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace Riesz1

namespace HsTestFunction

/-- Test functions are determined by their entire smooth lift. -/
theorem ext {N : ℕ+} {f g : HsTestFunction N} (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The zero test function. -/
def zero (N : ℕ+) : HsTestFunction N where
  toFun := 0
  smooth := contDiff_const
  periodic _ _ := rfl
  boundarySupport := ⟨1, zero_lt_one, fun _ hx => False.elim (hx rfl)⟩

/-- Addition preserves positive separation from the collision boundary. -/
def add {N : ℕ+} (f g : HsTestFunction N) : HsTestFunction N where
  toFun := f.toFun + g.toFun
  smooth := f.smooth.add g.smooth
  periodic k x := by simp only [Pi.add_apply, f.periodic, g.periodic]
  boundarySupport := by
    obtain ⟨δ, hδ, hf⟩ := f.boundarySupport
    obtain ⟨ε, hε, hg⟩ := g.boundarySupport
    refine ⟨min δ ε, lt_min hδ hε, fun x hx => ?_⟩
    by_cases hfx : f x = 0
    · have hgx : g x ≠ 0 := by
        intro hgx
        exact hx (by simp only [Pi.add_apply, hfx, hgx, add_zero])
      exact (ENNReal.ofReal_le_ofReal (min_le_right δ ε)).trans (hg x hgx)
    · exact (ENNReal.ofReal_le_ofReal (min_le_left δ ε)).trans (hf x hfx)

/-- Scalar multiplication preserves the test class, including scalar zero. -/
def smul {N : ℕ+} (a : ℝ) (f : HsTestFunction N) : HsTestFunction N where
  toFun := a • f.toFun
  smooth := f.smooth.const_smul a
  periodic k x := by simp only [Pi.smul_apply, f.periodic]
  boundarySupport := by
    obtain ⟨δ, hδ, hf⟩ := f.boundarySupport
    refine ⟨δ, hδ, fun x hx => hf x ?_⟩
    intro hfx
    exact hx (by simp only [Pi.smul_apply, hfx, smul_zero])

end HsTestFunction

variable {N : ℕ+} (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]

/-- The collision-free test functions inside the existing Sobolev completion.
Membership means representation by one actual `HsTestFunction`. -/
def hsSourceTestSobolev : Submodule ℝ (HsSobolev μ) where
  carrier := {v | ∃ f : HsTestFunction N,
    hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩ = v}
  zero_mem' := ⟨HsTestFunction.zero N, map_zero (hsSobolevOfSmooth μ)⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f.add g, map_add (hsSobolevOfSmooth μ)
      ⟨f.toFun, f.smoothOnClosure⟩ ⟨g.toFun, g.smoothOnClosure⟩⟩
  smul_mem' := by
    rintro a _ ⟨f, rfl⟩
    exact ⟨f.smul a, map_smul (hsSobolevOfSmooth μ) a ⟨f.toFun, f.smoothOnClosure⟩⟩

/-- The test domain in ambient `L²`, using the value map. -/
def hsTestL2Domain : Submodule ℝ (Lp ℝ 2 μ) :=
  (hsSourceTestSobolev μ).map (hsSobolevValue μ).toLinearMap

theorem mem_hsTestL2Domain (v : Lp ℝ 2 μ) :
    v ∈ hsTestL2Domain μ ↔ ∃ f : HsTestFunction N,
      hsSobolevValue μ (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩) = v := by
  constructor
  · rintro ⟨_, ⟨f, rfl⟩, hv⟩
    exact ⟨f, hv⟩
  · rintro ⟨f, rfl⟩
    exact ⟨_, ⟨f, rfl⟩, rfl⟩

variable {μ}

/-- Collision-free test functions are dense in `L²`. This needs no boundary
growth assumption and does not assert density in the form norm. -/
theorem dense_hsTestL2Domain {c : ℝ} (hN : 2 ≤ (N : ℕ))
    (χ : HsPairPotentials N c) (hc : 0 < c) :
    Dense (hsTestL2Domain
      (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) :
      Set (Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))) := by
  let ν := (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
  have hd := Internal.denseRange_of_chart_tests ν (hsTestL2Domain ν).subtype
    (hsLiftPoint N) (measurableEmbedding_hsLiftPoint N)
    (hsChamber N ∩ {x | x ⟨0, N.pos⟩ ∈ Ioo (0 : ℝ) 1})
    ((isOpen_hsChamber N).inter (isOpen_Ioo.preimage
      (EuclideanSpace.proj (𝕜 := ℝ) (⟨0, N.pos⟩ : Fin (N : ℕ))).continuous))
    (by
      filter_upwards [hsQuotientGibbsProbability_ae_open_strip χ hc] with x hx
      exact ⟨hsLiftPoint_mem_chamber N x, hx⟩)
  apply (hd ?_).mono
  · rintro _ ⟨v, rfl⟩
    exact v.property
  · intro g hg hgc hgU
    let f := hsTestFunctionOfCompact hN hg hgc (hgU.trans inter_subset_left)
    let v := hsSobolevValue ν (hsSobolevOfSmooth ν ⟨f.toFun, f.smoothOnClosure⟩)
    refine ⟨⟨v, (mem_hsTestL2Domain ν v).mpr ⟨f, rfl⟩⟩, ?_⟩
    have hv : (v : HsConfiguration N → ℝ) =ᵐ[ν] hsSmoothValue f.toFun :=
      (f.smoothOnClosure.memLp_value ν).coeFn_toLp
    change (v : HsConfiguration N → ℝ) =ᵐ[ν] hsSmoothValue g
    rw [← hsSmoothValue_vectorPeriodize hgc
      (subset_closure.trans (hgU.trans inter_subset_right))]
    exact hv

/-- `L₀` on precisely the collision-free test domain, as an ambient
partially defined operator. The output is the Neumann output. -/
def hsTestL2Operator {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c) :
    Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) →ₗ.[ℝ]
      Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) :=
  (hsNeumannL2Operator χ hc).domRestrict (hsTestL2Domain _)

/-- Every test-domain element lies in the full variational operator domain. -/
theorem hsTestL2Domain_le_neumann {c : ℝ} (hN : 2 ≤ (N : ℕ))
    (χ : HsPairPotentials N c) (hc : 0 < c) :
    hsTestL2Domain (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) ≤
      (hsNeumannL2Operator χ hc).domain := by
  intro v hv
  obtain ⟨f, rfl⟩ := (mem_hsTestL2Domain _ v).mp hv
  rw [← LinearPMap.graph_map_fst_eq_domain, hsNeumannL2Operator_graph]
  exact ⟨(_, _), (mem_hsNeumannL2Graph _ _ _).mpr
    ⟨_, rfl, hsLangevin_mem_neumannGraph hN χ hc f⟩, rfl⟩

/-- The domain of `L₀` is exactly the test subspace. -/
theorem hsTestL2Operator_domain {c : ℝ} (hN : 2 ≤ (N : ℕ))
    (χ : HsPairPotentials N c) (hc : 0 < c) :
    (hsTestL2Operator χ hc).domain =
      hsTestL2Domain (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) :=
  inf_eq_left.mpr (hsTestL2Domain_le_neumann hN χ hc)

/-- The operator is densely defined. -/
theorem dense_hsTestL2Operator_domain {c : ℝ} (hN : 2 ≤ (N : ℕ))
    (χ : HsPairPotentials N c) (hc : 0 < c) :
    Dense ((hsTestL2Operator χ hc).domain :
      Set (Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))) := by
  rw [hsTestL2Operator_domain hN χ hc]
  exact dense_hsTestL2Domain hN χ hc

/-- The operator is closable because it has the actual closed
Neumann extension. This alone does not identify its closure. -/
theorem hsTestL2Operator_isClosable {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c) :
    (hsTestL2Operator χ hc).IsClosable :=
  (hsNeumannL2Operator_selfAdjoint χ hc).isClosed.isClosable.leIsClosable
    LinearPMap.domRestrict_le

/-- Membership in the graph of `L₀` is exactly membership in the full
Neumann graph with a test-function input. -/
theorem mem_hsTestL2Operator_graph {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)
    (v a : Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    (v, a) ∈ (hsTestL2Operator χ hc).graph ↔
      v ∈ hsTestL2Domain (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) ∧
        (v, a) ∈ (hsNeumannL2Operator χ hc).graph := by
  rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
  simp only [Subtype.exists, exists_and_left, exists_eq_left]
  constructor
  · rintro ⟨hv, he⟩
    refine ⟨hv.1, hv.2, ?_⟩
    exact (LinearPMap.domRestrict_apply rfl).symm.trans he
  · rintro ⟨hv, ha, he⟩
    refine ⟨⟨hv, ha⟩, ?_⟩
    exact (LinearPMap.domRestrict_apply rfl).trans he

/-- On every actual test function the bundled operator is the differential
expression `∇H · ∇f - Δf`, as an `L²` class. -/
theorem hsTestL2Operator_on_test {c : ℝ} (hN : 2 ≤ (N : ℕ))
    (χ : HsPairPotentials N c) (hc : 0 < c) (f : HsTestFunction N) :
    (hsSobolevValue _ (hsSobolevOfSmooth _ ⟨f.toFun, f.smoothOnClosure⟩),
      (memLp_hsLangevin hN χ f
        (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))).toLp (hsLangevin χ f)) ∈
      (hsTestL2Operator χ hc).graph := by
  rw [mem_hsTestL2Operator_graph]
  exact ⟨(mem_hsTestL2Domain _ _).mpr ⟨f, rfl⟩,
    by rw [hsNeumannL2Operator_graph, mem_hsNeumannL2Graph]
       exact ⟨_, rfl, hsLangevin_mem_neumannGraph hN χ hc f⟩⟩

/-- The bundled operator is symmetric. -/
theorem hsTestL2Operator_symmetric {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c) :
    (hsTestL2Operator χ hc).IsFormalAdjoint (hsTestL2Operator χ hc) := by
  intro f g
  have hf := (hsTestL2Operator χ hc).mem_graph f
  have hg := (hsTestL2Operator χ hc).mem_graph g
  rw [mem_hsTestL2Operator_graph, hsNeumannL2Operator_graph, mem_hsNeumannL2Graph] at hf hg
  obtain ⟨v, hv, hva⟩ := hf.2
  obtain ⟨w, hw, hwb⟩ := hg.2
  rw [← hv, ← hw]
  exact hsNeumannGraph_symmetric _ ⟨(_, _), hva⟩ ⟨(_, _), hwb⟩

/-- The bundled operator is nonnegative. -/
theorem hsTestL2Operator_nonnegative {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : (hsTestL2Operator χ hc).domain) :
    0 ≤ inner ℝ (hsTestL2Operator χ hc f) f.val := by
  have hf := (hsTestL2Operator χ hc).mem_graph f
  rw [mem_hsTestL2Operator_graph, hsNeumannL2Operator_graph, mem_hsNeumannL2Graph] at hf
  obtain ⟨v, hv, hva⟩ := hf.2
  rw [← hv]
  exact hsNeumannGraph_nonnegative _ ⟨(_, _), hva⟩

end Riesz1
