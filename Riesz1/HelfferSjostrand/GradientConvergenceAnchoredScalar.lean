/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GradientConvergenceAnchoredEnergy
public import Riesz1.HelfferSjostrand.BoundaryCoreAnchoredTests

/-! # Scalar graph convergence on the anchored simplex

The anchored resolvent gives the scalar domain and form convergence
assertions of Proposition 3.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Riesz1

variable {n : ℕ} {c : ℝ}

theorem anchoredGradient_value_ae (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f : anchoredTestSubmodule n) :
    (poissonAnchoredValue χ hc (anchoredTestHilbert χ hc f) : AnchoredEuclidean n → ℝ) =ᵐ[anchoredMeasureE χ]
      f.val := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact (WeightedSobolev.memLp_of_smoothNearClosure (isBounded_anchoredSimplex n)
    (ae_mem_anchoredSimplex χ) (anchoredTestSmooth n f).property).1.coeFn_toLp

theorem anchoredGradient_gradient_ae (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f : anchoredTestSubmodule n) :
    (poissonAnchoredGradient χ hc (anchoredTestHilbert χ hc f) :
      AnchoredEuclidean n → AnchoredEuclidean n) =ᵐ[anchoredMeasureE χ] gradient f.val := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact (WeightedSobolev.memLp_of_smoothNearClosure (isBounded_anchoredSimplex n)
    (ae_mem_anchoredSimplex χ) (anchoredTestSmooth n f).property).2.coeFn_toLp

namespace Internal

theorem anchoredScalar_graph_limit (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f : ℕ → PoissonAnchoredSpace χ hc) (a : ℕ → Lp ℝ 2 (anchoredMeasureE χ))
    (hg : ∀ k, (f k, a k) ∈ anchoredNeumannHilbertGraph χ hc)
    (v b : Lp ℝ 2 (anchoredMeasureE χ))
    (hv : Tendsto (fun k => poissonAnchoredValue χ hc (f k)) atTop (𝓝 v))
    (hb : Tendsto a atTop (𝓝 b)) :
    ∃ φ : PoissonAnchoredSpace χ hc, poissonAnchoredValue χ hc φ = v ∧
      (φ, b) ∈ anchoredNeumannHilbertGraph χ hc ∧ Tendsto f atTop (𝓝 φ) := by
  let φ := anchoredNeumannResolvent χ hc (b + v)
  have he (k : ℕ) : anchoredNeumannResolvent χ hc (a k + poissonAnchoredValue χ hc (f k)) = f k :=
    anchoredNeumannResolvent_graph_input χ hc (hg k)
  have hlim : Tendsto f atTop (𝓝 φ) := by
    have h := ((anchoredNeumannResolvent χ hc).continuous.tendsto (b + v)).comp (hb.add hv)
    change Tendsto (fun k => anchoredNeumannResolvent χ hc (a k + poissonAnchoredValue χ hc (f k)))
      atTop (𝓝 φ) at h
    simpa only [he] using h
  have hval : poissonAnchoredValue χ hc φ = v :=
    tendsto_nhds_unique (((poissonAnchoredValue χ hc).continuous.tendsto φ).comp hlim) hv
  refine ⟨φ, hval, ?_, hlim⟩
  have h := anchoredNeumannResolvent_mem_graph χ hc (b + v)
  rwa [hval, add_sub_cancel_right] at h

end Internal

/-- Anchored scalar domain membership, operator value, and convergence in `H¹`. -/
theorem anchoredGradient_graph_convergence_scalar (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f : ℕ → anchoredTestSubmodule n) (v a : Lp ℝ 2 (anchoredMeasureE χ))
    (hv : Tendsto (fun k => poissonAnchoredValue χ hc (anchoredTestHilbert χ hc (f k))) atTop (𝓝 v))
    (ha : Tendsto (fun k => (memLp_anchoredLangevinExpr χ hc (f k).property.1
      (f k).property.2.1 (f k).property.2.2).toLp (anchoredLangevinExpr χ (f k).val)) atTop (𝓝 a)) :
    ∃ φ : PoissonAnchoredSpace χ hc, poissonAnchoredValue χ hc φ = v ∧
      IsAnchoredLangevin χ (poissonAnchoredValue χ hc φ) (poissonAnchoredGradient χ hc φ) a ∧
      Tendsto (fun k => anchoredTestHilbert χ hc (f k)) atTop (𝓝 φ) ∧
      Tendsto (fun k => poissonAnchoredGradient χ hc (anchoredTestHilbert χ hc (f k)))
        atTop (𝓝 (poissonAnchoredGradient χ hc φ)) := by
  obtain ⟨φ, hval, hg, hlim⟩ := Internal.anchoredScalar_graph_limit χ hc
    (fun k => anchoredTestHilbert χ hc (f k)) _ (fun k => anchoredTestHilbert_mem_graph χ hc (f k)) v a hv ha
  exact ⟨φ, hval, (mem_anchoredNeumannHilbertGraph_iff χ hc φ a).mp hg, hlim,
    ((poissonAnchoredGradient χ hc).continuous.tendsto φ).comp hlim⟩

end Riesz1
