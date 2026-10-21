/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.StrictConvCommutator
public import Riesz1.HelfferSjostrand.BoundaryCoreAnchored
public import Riesz1.HelfferSjostrand.BoundaryCoreAnchoredNeumann
public import Riesz1.HelfferSjostrand.BoundaryCoreAnchoredTests
public import Riesz1.HelfferSjostrand.GradientConvergenceAnchoredVector
public import Riesz1.HelfferSjostrand.PoissonEquationAnchored
public import Riesz1.HelfferSjostrand.AnchoredInverse

/-!
# The weak equation of the anchored gradient

Remark 3.2, the representation step. Let `φ` solve the scalar Poisson
equation `𝓛φ = F - ∫F` for the anchored law. The operator core gives tests `f_k` with
`f_k → φ` and `𝓛f_k → F - ∫F` in `L²`. The gradients `∇f_k` converge in the vector energy
space to a limit `G` with values `∇φ`, by `anchoredGradient_graph_convergence`. Pairing
`∇f_k` with a test tuple `u` and passing to the limit gives the weak equation of `G` against
every test tuple, hence against every element of `𝒱_{μ*}` by density. Uniqueness of the
vector inverse then identifies `G` with `T*∇F`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology InnerProductSpace

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- The Neumann graph point of a scalar Poisson solution: its value and its operator value
form a point of the `L²` graph of the anchored Neumann operator. -/
theorem poisson_solution_mem_graph (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    [IsProbabilityMeasure (anchoredMeasureE χ)] (F : Lp ℝ 2 (anchoredMeasureE χ))
    {φ : AnchoredSobolev χ} (hφ : AnchoredPoissonSolves χ hc F φ) :
    (φ.val.1, poissonCenter (anchoredMeasureE χ) F) ∈ (anchoredNeumannL2Operator χ hc).graph := by
  obtain ⟨hφL, he⟩ := hφ
  have h := anchoredNeumannL2Operator_on_domain χ hc ⟨φ, hφL⟩
  rw [he] at h
  exact h

/-- Approximation of the Neumann graph by anchored tests, from the operator core
`scalar_boundary_core_L3219_anchored_real` under admissibility: every graph point is a limit of
graph points of tests. -/
theorem exists_anchoredTest_approx (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {C_N : ℝ} (hadm : HsAdmissible χ C_N) {v a : Lp ℝ 2 (anchoredMeasureE χ)}
    (hva : (v, a) ∈ (anchoredNeumannL2Operator χ hc).graph) :
    ∃ f : ℕ → anchoredTestSubmodule n,
      Tendsto (fun k => poissonAnchoredValue χ hc (anchoredTestHilbert χ hc (f k))) atTop (𝓝 v) ∧
      Tendsto (fun k => (memLp_anchoredLangevinExpr χ hc (f k).property.1 (f k).property.2.1
        (f k).property.2.2).toLp (anchoredLangevinExpr χ (f k).val)) atTop (𝓝 a) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  have hclos := (scalar_boundary_core_L3219_anchored_real χ hc hadm).1
  have hgraph : (anchoredTestL2Operator χ hc).graph.topologicalClosure =
      (anchoredNeumannL2Operator χ hc).graph := by
    rw [(anchoredTestL2Operator_isClosable χ hc).graph_closure_eq_closure_graph, hclos]
  have hmem : (v, a) ∈ closure ((anchoredTestL2Operator χ hc).graph :
      Set (Lp ℝ 2 (anchoredMeasureE χ) × Lp ℝ 2 (anchoredMeasureE χ))) := by
    rw [← Submodule.topologicalClosure_coe, hgraph]
    exact hva
  obtain ⟨p, hp, hlim⟩ := mem_closure_iff_seq_limit.mp hmem
  have hpt (k : ℕ) : ∃ f : anchoredTestSubmodule n,
      poissonAnchoredValue χ hc (anchoredTestHilbert χ hc f) = (p k).1 ∧
        anchoredGradientSourceOperatorLin χ hc f = (p k).2 := by
    obtain ⟨h, hh1, hh2⟩ := (LinearPMap.mem_graph_iff _).mp (hp k)
    have hd : (h : Lp ℝ 2 (anchoredMeasureE χ)) ∈ anchoredTestL2Domain χ hc :=
      (anchoredTestL2Operator_domain χ hc).le h.2
    obtain ⟨f, hf⟩ := (mem_anchoredTestL2Domain χ hc _).mp hd
    have hsd : anchoredGradientSourceDomainLin χ hc f = h := Subtype.ext hf
    refine ⟨f, hf.trans hh1, ?_⟩
    calc anchoredGradientSourceOperatorLin χ hc f
        = (anchoredTestL2Operator χ hc) (anchoredGradientSourceDomainLin χ hc f) := rfl
      _ = (anchoredTestL2Operator χ hc) h := by rw [hsd]
      _ = (p k).2 := hh2
  choose f hf1 hf2 using hpt
  refine ⟨f, ?_, ?_⟩
  · exact Tendsto.congr (fun k => (hf1 k).symm) ((continuous_fst.tendsto (v, a)).comp hlim)
  · exact Tendsto.congr (fun k => (hf2 k).symm.trans (anchoredGradientSourceOperatorLin_eq χ hc (f k)))
      ((continuous_snd.tendsto (v, a)).comp hlim)

/-- The pairing of an `L²` class with the coefficient of a test tuple, as the integral used in
the weak equation. -/
theorem integral_coeff_pairing (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    [IsProbabilityMeasure (anchoredMeasureE χ)] (u : AnchoredVectorTest n)
    (x : Lp ℝ 2 (anchoredMeasureE χ)) :
    inner ℝ x ((memLp_anchoredWeakCoeff χ hc u).toLp (anchoredWeakCoeff χ u)) =
      ∫ y, x y * anchoredWeakCoeff χ u y ∂anchoredMeasureE χ := by
  rw [poisson_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [(memLp_anchoredWeakCoeff χ hc u).coeFn_toLp] with y hy
  rw [hy]

/-- The centered Poisson right-hand side pairs with a test coefficient as the uncentered one,
since the coefficient has zero mean. -/
theorem inner_poissonCenter_coeff (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    [IsProbabilityMeasure (anchoredMeasureE χ)] (u : AnchoredVectorTest n)
    (x : Lp ℝ 2 (anchoredMeasureE χ)) :
    inner ℝ (poissonCenter (anchoredMeasureE χ) x)
        ((memLp_anchoredWeakCoeff χ hc u).toLp (anchoredWeakCoeff χ u)) =
      ∫ y, x y * anchoredWeakCoeff χ u y ∂anchoredMeasureE χ := by
  have hone : inner ℝ (Lp.const 2 (anchoredMeasureE χ) (1 : ℝ))
      ((memLp_anchoredWeakCoeff χ hc u).toLp (anchoredWeakCoeff χ u)) = 0 := by
    rw [poisson_inner_eq_integral]
    refine (integral_congr_ae ?_).trans (integral_anchoredWeakCoeff_eq_zero χ hc u)
    filter_upwards [Lp.coeFn_const 2 (anchoredMeasureE χ) (1 : ℝ),
      (memLp_anchoredWeakCoeff χ hc u).coeFn_toLp] with y h1 h2
    simp only [h1, h2, Function.const_apply, one_mul]
  rw [poissonCenter, inner_sub_left, real_inner_smul_left, hone, mul_zero, sub_zero,
    integral_coeff_pairing χ hc u x]

/-- The gradient limit of approximating tests satisfies the weak equation of the non-gradient
problem against every test tuple. Remark 3.2, the pairing limit. -/
theorem anchoredGradient_limit_weak (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    [IsProbabilityMeasure (anchoredMeasureE χ)] (F : AnchoredSobolev χ) (f : ℕ → anchoredTestSubmodule n)
    (ha : Tendsto (fun k => (memLp_anchoredLangevinExpr χ hc (f k).property.1 (f k).property.2.1
        (f k).property.2.2).toLp (anchoredLangevinExpr χ (f k).val)) atTop
          (𝓝 (poissonCenter (anchoredMeasureE χ) F.val.1)))
    {G : AnchoredVectorSobolev χ (anchoredMeasureE χ)}
    (hG : Tendsto (fun k => anchoredGradientFieldLin χ hc (f k)) atTop (𝓝 G))
    (u : AnchoredVectorTest n) :
    anchoredVectorSobolevForm (anchoredMeasureE χ) G.val
        (anchoredVectorJet χ (anchoredMeasureE χ) u) =
      ∫ y, inner ℝ (F.val.2 y) (anchoredTestVector u y) ∂(anchoredMeasureE χ) := by
  have hseq (k : ℕ) : anchoredVectorSobolevForm (anchoredMeasureE χ)
      (anchoredGradientFieldLin χ hc (f k)).val (anchoredVectorJet χ (anchoredMeasureE χ) u) =
        inner ℝ ((memLp_anchoredLangevinExpr χ hc (f k).property.1 (f k).property.2.1
          (f k).property.2.2).toLp (anchoredLangevinExpr χ (f k).val))
          ((memLp_anchoredWeakCoeff χ hc u).toLp (anchoredWeakCoeff χ u)) := by
    have h1 : (anchoredGradientFieldLin χ hc (f k)).val =
        anchoredVectorJet χ (anchoredMeasureE χ) (anchoredGradientTestTuple (f k)) := rfl
    rw [h1, anchoredVectorSobolevForm_jet χ hc, anchoredVectorForm_gradientTest_coeff χ hc (f k) u,
      integral_coeff_pairing χ hc u]
    apply integral_congr_ae
    filter_upwards [(memLp_anchoredLangevinExpr χ hc (f k).property.1 (f k).property.2.1
      (f k).property.2.2).coeFn_toLp] with y hy
    rw [hy]
  have hD : Tendsto (fun k => (anchoredGradientFieldLin χ hc (f k)).val) atTop (𝓝 G.val) :=
    (continuous_subtype_val.tendsto G).comp hG
  have hlimL : Tendsto (fun k => anchoredVectorSobolevForm (anchoredMeasureE χ)
      (anchoredGradientFieldLin χ hc (f k)).val (anchoredVectorJet χ (anchoredMeasureE χ) u))
        atTop (𝓝 (anchoredVectorSobolevForm (anchoredMeasureE χ) G.val
          (anchoredVectorJet χ (anchoredMeasureE χ) u))) := by
    have hform (x : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) :
        anchoredVectorSobolevForm (anchoredMeasureE χ) x
          (anchoredVectorJet χ (anchoredMeasureE χ) u) =
        inner ℝ (anchoredInverseDerivatives (anchoredMeasureE χ) x)
          (anchoredInverseDerivatives (anchoredMeasureE χ)
            (anchoredVectorJet χ (anchoredMeasureE χ) u)) :=
      (anchoredInverseDerivatives_inner (anchoredMeasureE χ) x _).symm
    simp only [hform]
    exact (((anchoredInverseDerivatives (anchoredMeasureE χ)).continuous.tendsto _).comp hD).inner
      tendsto_const_nhds
  have hlimR : Tendsto (fun k => inner ℝ ((memLp_anchoredLangevinExpr χ hc (f k).property.1
      (f k).property.2.1 (f k).property.2.2).toLp (anchoredLangevinExpr χ (f k).val))
        ((memLp_anchoredWeakCoeff χ hc u).toLp (anchoredWeakCoeff χ u)))
      atTop (𝓝 (inner ℝ (poissonCenter (anchoredMeasureE χ) F.val.1)
        ((memLp_anchoredWeakCoeff χ hc u).toLp (anchoredWeakCoeff χ u)))) :=
    ha.inner tendsto_const_nhds
  have hL := tendsto_nhds_unique hlimL (by simpa only [hseq] using hlimR)
  rw [hL, inner_poissonCenter_coeff χ hc u F.val.1]
  exact (integral_inner_anchoredTestVector χ hc F.property u).symm

/-- Inner products with the inverse values of a test tuple are the integrals against the
test tuple. -/
theorem inner_anchoredInverseValues_jet (χ : HsPairPotentials n.succPNat c)
    [IsProbabilityMeasure (anchoredMeasureE χ)]
    (v : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ)) (u : AnchoredVectorTest n) :
    inner ℝ v (anchoredInverseValues (anchoredMeasureE χ) (anchoredVectorJet χ
      (anchoredMeasureE χ) u)) =
      ∫ y, inner ℝ (v y) (anchoredTestVector u y) ∂(anchoredMeasureE χ) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [anchoredInverseValues_jet_ae (anchoredMeasureE χ) χ u] with y hy
  rw [hy]

/-- Density: a vector energy element that satisfies the weak equation on every test jet satisfies
it on all of `𝒱_{μ*}`. -/
theorem anchoredVectorSobolev_weak_of_jets (χ : HsPairPotentials n.succPNat c)
    [IsProbabilityMeasure (anchoredMeasureE χ)] (G : AnchoredVectorSobolev χ (anchoredMeasureE χ))
    (v : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ))
    (hjet : ∀ u : AnchoredVectorTest n,
      anchoredVectorSobolevForm (anchoredMeasureE χ) G.val
          (anchoredVectorJet χ (anchoredMeasureE χ) u) =
        inner ℝ v (anchoredInverseValues (anchoredMeasureE χ)
          (anchoredVectorJet χ (anchoredMeasureE χ) u))) :
    ∀ h : AnchoredVectorSobolev χ (anchoredMeasureE χ),
      anchoredVectorSobolevForm (anchoredMeasureE χ) G.val h.val =
        inner ℝ v (anchoredInverseValues (anchoredMeasureE χ) h.val) := by
  have hf : Continuous (fun x : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ) =>
      anchoredVectorSobolevForm (anchoredMeasureE χ) G.val x) := by
    simp only [← anchoredInverseDerivatives_inner (anchoredMeasureE χ) G.val]
    exact continuous_const.inner (anchoredInverseDerivatives (anchoredMeasureE χ)).continuous
  have hg : Continuous (fun x : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ) =>
      inner ℝ v (anchoredInverseValues (anchoredMeasureE χ) x)) :=
    continuous_const.inner (anchoredInverseValues (anchoredMeasureE χ)).continuous
  have hK := isClosed_eq hf hg
  have hsub : (LinearMap.range (anchoredVectorJetLin χ (anchoredMeasureE χ)) :
      Set (Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ))) ⊆
      {x : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ) |
        anchoredVectorSobolevForm (anchoredMeasureE χ) G.val x =
          inner ℝ v (anchoredInverseValues (anchoredMeasureE χ) x)} := by
    rintro x ⟨u, rfl⟩
    exact hjet u
  have hcl := closure_minimal hsub hK
  intro h
  have hh : h.val ∈ closure ((LinearMap.range (anchoredVectorJetLin χ (anchoredMeasureE χ)) :
      Submodule ℝ (Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ))) :
        Set (Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ))) := by
    rw [← Submodule.topologicalClosure_coe]
    exact h.property
  exact hcl hh

/-- The weak equation determines the vector inverse: uniqueness of the solution of the vector
problem, applied to the gradient limit. -/
theorem anchoredVectorSobolev_eq_inverse_of_weak (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    [IsProbabilityMeasure (anchoredMeasureE χ)] (G : AnchoredVectorSobolev χ (anchoredMeasureE χ))
    (v : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ))
    (hweak : ∀ h : AnchoredVectorSobolev χ (anchoredMeasureE χ),
      anchoredVectorSobolevForm (anchoredMeasureE χ) G.val h.val =
        inner ℝ v (anchoredInverseValues (anchoredMeasureE χ) h.val)) :
    G = anchoredVectorInverse (anchoredMeasureE χ) χ hc (ae_mem_anchoredSimplex χ) v :=
  anchoredVectorInverse_unique (anchoredMeasureE χ) χ hc (ae_mem_anchoredSimplex χ) v G hweak

/-- Remark 3.2, representation: for every scalar solution `φ` of the
anchored Poisson equation with right side `F`, the gradient of `φ` is the vector solution
`T* ∇F`. -/
theorem anchoredPoisson_gradient_eq_inverse (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    [IsProbabilityMeasure (anchoredMeasureE χ)]
    {C_N : ℝ} (hadm : HsAdmissible χ C_N) (F : AnchoredSobolev χ) {φ : AnchoredSobolev χ}
    (hφ : AnchoredPoissonSolves χ hc F.val.1 φ) :
    φ.val.2 = anchoredInverseValues (anchoredMeasureE χ)
      (anchoredVectorInverse (anchoredMeasureE χ) χ hc (ae_mem_anchoredSimplex χ) F.val.2).val := by
  obtain ⟨f, hv, ha⟩ := exists_anchoredTest_approx χ hc hadm
    (poisson_solution_mem_graph χ hc F.val.1 hφ)
  obtain ⟨φ', G, hval, -, hgrad, hG⟩ := anchoredGradient_graph_convergence χ hc f φ.val.1
    (poissonCenter (anchoredMeasureE χ) F.val.1) hv ha
  have hψ : poissonAnchoredValue χ hc ((poissonAnchoredEquiv χ hc).symm φ) = φ.val.1 :=
    congrArg (fun x => x.val.1) ((poissonAnchoredEquiv χ hc).apply_symm_apply φ)
  have hφ' : φ' = (poissonAnchoredEquiv χ hc).symm φ :=
    poissonAnchoredValue_injective χ hc (hval.trans hψ.symm)
  have hgφ : anchoredInverseValues (anchoredMeasureE χ) G.val = φ.val.2 := by
    rw [hgrad, hφ']
    exact congrArg (fun x => x.val.2) ((poissonAnchoredEquiv χ hc).apply_symm_apply φ)
  have hweak := anchoredGradient_limit_weak χ hc F f ha hG
  have hjet : ∀ u : AnchoredVectorTest n,
      anchoredVectorSobolevForm (anchoredMeasureE χ) G.val
          (anchoredVectorJet χ (anchoredMeasureE χ) u) =
        inner ℝ F.val.2 (anchoredInverseValues (anchoredMeasureE χ)
          (anchoredVectorJet χ (anchoredMeasureE χ) u)) := fun u => by
    rw [hweak u, inner_anchoredInverseValues_jet χ]
  have hGeq := anchoredVectorSobolev_eq_inverse_of_weak χ hc G F.val.2
    (anchoredVectorSobolev_weak_of_jets χ G F.val.2 hjet)
  rw [← hgφ, hGeq]

end Riesz1

end
