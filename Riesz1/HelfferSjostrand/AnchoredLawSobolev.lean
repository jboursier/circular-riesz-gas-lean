/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.AnchoredLawWeight
public import Riesz1.ToMathlib.WeightedSobolev.Completion
public import Riesz1.ToMathlib.WeightedSobolev.TestDensity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# The Sobolev space and the Langevin operator of the anchored law `μ*`

The space `H¹(μ*)` and the scalar Langevin operator `L^{μ*}` are the weighted Sobolev
space and the Langevin operator, on the Euclidean simplex
`D_N^*` with coordinates indexed `2, …, N`.

The anchored law is transported to the Euclidean space `AnchoredEuclidean n`, where the gradient is
Euclidean. The space `H¹(μ*)` is `IsWeightedH1` on the simplex, which is the Euclidean
weighted Sobolev space. The Neumann element of `L^{μ*}` is unique in `L²(μ*)`, by the chart-test
density criterion `Riesz1.Internal.eq_zero_of_chart_tests`.

This file sets up the spaces and proves the two facts the Langevin operator needs first: smooth
compactly supported functions on `D_N^*` lie in `H¹(μ*)`, and the Neumann element is unique.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff InnerProductSpace

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- The Euclidean space carrying the anchored coordinates `y = (y_2, …, y_N)`. -/
abbrev AnchoredEuclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The Euclidean simplex `D_N^*`, as a subset of the Euclidean space of anchored coordinates. -/
def anchoredSimplex (n : ℕ) : Set (AnchoredEuclidean n) := WithLp.ofLp ⁻¹' anchoredDomain n

/-- The anchored law `μ*` transported to the Euclidean space of anchored coordinates. -/
def anchoredMeasureE (χ : HsPairPotentials n.succPNat c) : Measure (AnchoredEuclidean n) :=
  (hsAnchoredLaw χ).map (WithLp.toLp 2)

/-- The Euclidean simplex is open. -/
theorem isOpen_anchoredSimplex (n : ℕ) : IsOpen (anchoredSimplex n) :=
  (isOpen_anchoredDomain n).preimage (PiLp.continuous_ofLp 2 _)

/-- The Euclidean simplex is measurable. -/
theorem measurableSet_anchoredSimplex (n : ℕ) : MeasurableSet (anchoredSimplex n) :=
  (isOpen_anchoredSimplex n).measurableSet

/-- The anchored law is a probability measure on the Euclidean space. -/
theorem isProbabilityMeasure_anchoredMeasureE (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    IsProbabilityMeasure (anchoredMeasureE χ) := by
  have := isProbabilityMeasure_hsAnchoredLaw χ hc
  unfold anchoredMeasureE
  exact (Measure.isProbabilityMeasure_map_iff (PiLp.continuous_toLp 2 _).measurable.aemeasurable).mpr
    inferInstance

/-- The anchored law is concentrated on the Euclidean simplex, since it is absolutely continuous
with respect to Lebesgue measure restricted to `D_N^*`. -/
theorem ae_mem_anchoredSimplex (χ : HsPairPotentials n.succPNat c) :
    ∀ᵐ y ∂(anchoredMeasureE χ), y ∈ anchoredSimplex n := by
  unfold anchoredMeasureE
  rw [ae_map_iff (p := fun y : AnchoredEuclidean n => y ∈ anchoredSimplex n)
    (PiLp.continuous_toLp 2 _).measurable.aemeasurable (measurableSet_anchoredSimplex n)]
  have hac : hsAnchoredLaw χ ≪ volume.restrict (anchoredDomain n) := by
    unfold hsAnchoredLaw hsAnchoredWeight
    exact Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  have hD := hac.ae_le (ae_restrict_mem (measurableSet_anchoredDomain n))
  filter_upwards [hD] with y hy
  exact hy

/-- The Sobolev space `H¹(μ*)` of pairs `(F, G)`: the function `F` and its weak gradient `G`,
in the completion of smooth functions near the closed Euclidean simplex, for
the anchored law. -/
def IsAnchoredH1 (χ : HsPairPotentials n.succPNat c) (F : AnchoredEuclidean n → ℝ)
    (G : AnchoredEuclidean n → AnchoredEuclidean n) : Prop :=
  WeightedSobolev.IsWeightedH1 (anchoredMeasureE χ) (anchoredSimplex n) F G

/-- The scalar Langevin operator `L^{μ*}` of the anchored law, as its Neumann relation. The pair
`(F, G)` is in `H¹(μ*)`, and `A` is its image: `E(F, H) = ∫ A H dμ*` for every `(H, K)` in
`H¹(μ*)`, where the Dirichlet form is `E(F, H) = ∫ ⟪G, K⟫ dμ*`. -/
def IsAnchoredLangevin (χ : HsPairPotentials n.succPNat c) (F : AnchoredEuclidean n → ℝ)
    (G : AnchoredEuclidean n → AnchoredEuclidean n) (A : AnchoredEuclidean n → ℝ) : Prop :=
  IsAnchoredH1 χ F G ∧ MemLp A 2 (anchoredMeasureE χ) ∧
    ∀ (H : AnchoredEuclidean n → ℝ) (K : AnchoredEuclidean n → AnchoredEuclidean n),
      IsAnchoredH1 χ H K →
        ∫ y, inner ℝ (G y) (K y) ∂(anchoredMeasureE χ) = ∫ y, A y * H y ∂(anchoredMeasureE χ)

/-- The anchored Hamiltonian on the Euclidean space of anchored coordinates. -/
def hsAnchoredHamiltonianE (χ : HsPairPotentials n.succPNat c) (y : AnchoredEuclidean n) : ℝ :=
  hsAnchoredHamiltonian χ (WithLp.ofLp y)

/-- The scalar Langevin differential expression `L_0 f = ⟪∇H*, ∇f⟫ - Δf` of `μ*`. It is the intended value on `D_N^*`, where `H*` is smooth. This
file does not prove the integration by parts that identifies it with the Neumann operator. -/
def anchoredLangevinExpr (χ : HsPairPotentials n.succPNat c) (f : AnchoredEuclidean n → ℝ)
    (y : AnchoredEuclidean n) : ℝ :=
  inner ℝ (gradient (hsAnchoredHamiltonianE χ) y) (gradient f y) - Laplacian.laplacian f y

/-- A smooth compactly supported function lies in `H¹(μ*)`, with its own gradient as weak gradient.
In particular this holds for every element of the test class `𝒟_N^* = C_c^∞(D_N^*)`, since such a function is smooth with compact support in the Euclidean space. -/
theorem isAnchoredH1_of_testFunction (χ : HsPairPotentials n.succPNat c)
    (f : AnchoredEuclidean n → ℝ) (hf : ContDiff ℝ ∞ f) (hcs : HasCompactSupport f)
    (hμ : IsFiniteMeasure (anchoredMeasureE χ)) :
    IsAnchoredH1 χ f (gradient f) := by
  have hgrad : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ (AnchoredEuclidean n)).symm.continuous.comp
      (hf.continuous_fderiv (by simp))
  have hgcs : HasCompactSupport (gradient f) :=
    (hcs.fderiv (𝕜 := ℝ)).comp_left (g := (InnerProductSpace.toDual ℝ (AnchoredEuclidean n)).symm)
      (map_zero _)
  refine ⟨?_, ?_, fun _ => f, fun _ => ⟨univ, isOpen_univ, subset_univ _, hf.contDiffOn⟩,
    ?_, ?_⟩
  · exact hf.continuous.memLp_of_hasCompactSupport hcs
  · exact hgrad.memLp_of_hasCompactSupport hgcs
  · refine tendsto_const_nhds.congr' (Eventually.of_forall fun k => ?_)
    simp
  · refine tendsto_const_nhds.congr' (Eventually.of_forall fun k => ?_)
    simp

/-- The Neumann element of the anchored Langevin operator is unique in `L²(μ*)`. Two elements `A`
and `A'` with the same pair `(F, G)` integrate identically against every smooth compactly supported
test function in `D_N^*`, which lie in `H¹(μ*)`, so their difference is zero in `L²(μ*)` by the
chart-test density criterion. -/
theorem ae_eq_of_isAnchoredLangevin (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {F : AnchoredEuclidean n → ℝ} {G : AnchoredEuclidean n → AnchoredEuclidean n}
    {A A' : AnchoredEuclidean n → ℝ} (hA : IsAnchoredLangevin χ F G A)
    (hA' : IsAnchoredLangevin χ F G A') : A =ᵐ[anchoredMeasureE χ] A' := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  have hμ : IsFiniteMeasure (anchoredMeasureE χ) := inferInstance
  have hsub : MemLp (A - A') 2 (anchoredMeasureE χ) := hA.2.1.sub hA'.2.1
  have hAi : Integrable A (anchoredMeasureE χ) := hA.2.1.integrable (by norm_num)
  have hAi' : Integrable A' (anchoredMeasureE χ) := hA'.2.1.integrable (by norm_num)
  -- the difference integrates to zero against every test function on the simplex
  have htest : ∀ g : AnchoredEuclidean n → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ anchoredSimplex n →
        ∫ y, g y * (A - A') y ∂(anchoredMeasureE χ) = 0 := by
    intro g hg hgcs hgsupp
    have hmem := isAnchoredH1_of_testFunction χ g hg hgcs hμ
    have h1 := hA.2.2 g (gradient g) hmem
    have h2 := hA'.2.2 g (gradient g) hmem
    obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgcs
    have hI1 : Integrable (fun y => g y * A y) (anchoredMeasureE χ) :=
      hAi.bdd_mul hg.continuous.aestronglyMeasurable (ae_of_all _ fun y => by
        simpa using hC y)
    have hI2 : Integrable (fun y => g y * A' y) (anchoredMeasureE χ) :=
      hAi'.bdd_mul hg.continuous.aestronglyMeasurable (ae_of_all _ fun y => by
        simpa using hC y)
    have e1 : ∫ y, g y * A y ∂(anchoredMeasureE χ) = ∫ y, A y * g y ∂(anchoredMeasureE χ) :=
      integral_congr_ae (ae_of_all _ fun y => mul_comm _ _)
    have e2 : ∫ y, g y * A' y ∂(anchoredMeasureE χ) = ∫ y, A' y * g y ∂(anchoredMeasureE χ) :=
      integral_congr_ae (ae_of_all _ fun y => mul_comm _ _)
    simp only [Pi.sub_apply, mul_sub]
    rw [integral_sub hI1 hI2, e1, e2]
    linarith [h1, h2]
  -- the chart-test criterion gives the difference zero as an element of `L²(μ*)`
  have hchart : hsub.toLp (A - A') = 0 :=
    Internal.eq_zero_of_chart_tests (anchoredMeasureE χ) (fun y => y) MeasurableEmbedding.id
      (anchoredSimplex n) (isOpen_anchoredSimplex n) (ae_mem_anchoredSimplex χ) _
      fun g hg hgcs hgsupp => by
        refine (integral_congr_ae ?_).trans (htest g hg hgcs hgsupp)
        filter_upwards [hsub.coeFn_toLp] with y hy
        rw [hy]
  filter_upwards [hsub.coeFn_toLp, Lp.coeFn_zero ℝ 2 (anchoredMeasureE χ)] with y hy1 hy2
  rw [hchart] at hy1
  have hd : (A - A') y = 0 := by
    rw [← hy1, hy2]
    rfl
  exact sub_eq_zero.mp hd

end Riesz1

end
end
