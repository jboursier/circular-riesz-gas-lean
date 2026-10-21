/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GradientConvergenceAnchoredLinear
public import Riesz1.ToMathlib.GraphEnergyCauchy

/-! # Anchored gradient convergence in the vector energy norm

The remaining anchored assertion of
Proposition 3.1. Its scalar limit is in the
anchored Neumann domain and its gradient converges in the
anchored vector completion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Riesz1

variable {n : ℕ} {c : ℝ}

namespace Internal

theorem anchoredGradient_exists_limit (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f : ℕ → anchoredTestSubmodule n)
    (hg : CauchySeq (fun k => poissonAnchoredGradient χ hc (anchoredTestHilbert χ hc (f k))))
    (ha : CauchySeq (fun k => anchoredGradientSourceOperatorLin χ hc (f k))) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    ∃ G : AnchoredVectorSobolev χ (anchoredMeasureE χ),
      Tendsto (fun k => anchoredGradientFieldLin χ hc (f k)) atTop (𝓝 G) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  have hC := cauchySeq_of_linear_graph_energy
    (anchoredGradientFieldLin χ hc)
    ((poissonAnchoredGradient χ hc).toLinearMap.comp (anchoredTestHilbert χ hc))
    (anchoredGradientSourceOperatorLin χ hc) (anchoredGradientFieldLin_norm_sq χ hc) f hg ha
  exact cauchySeq_tendsto_of_complete hC

theorem anchoredGradient_limit_values (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f : ℕ → anchoredTestSubmodule n) (φ : PoissonAnchoredSpace χ hc) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    ∀ G : AnchoredVectorSobolev χ (anchoredMeasureE χ),
      Tendsto (fun k => poissonAnchoredGradient χ hc (anchoredTestHilbert χ hc (f k)))
        atTop (𝓝 (poissonAnchoredGradient χ hc φ)) →
      Tendsto (fun k => anchoredGradientFieldLin χ hc (f k)) atTop (𝓝 G) →
      anchoredInverseValues (anchoredMeasureE χ) G.val = poissonAnchoredGradient χ hc φ := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  intro G hgrad hGlim
  let P : AnchoredVectorSobolev χ (anchoredMeasureE χ) →L[ℝ]
      Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ) :=
    (anchoredInverseValues (anchoredMeasureE χ)).comp
      (anchoredVectorSobolevSubmodule χ (anchoredMeasureE χ)).subtypeL
  have h := (P.continuous.tendsto G).comp hGlim
  change Tendsto (fun k => anchoredInverseValues (anchoredMeasureE χ)
    (anchoredGradientFieldLin χ hc (f k)).val) atTop
      (𝓝 (anchoredInverseValues (anchoredMeasureE χ) G.val)) at h
  simp_rw [anchoredGradientFieldLin_values] at h
  exact tendsto_nhds_unique h hgrad

end Internal

/-- Proposition 3.1, anchored graph convergence.
The limiting vector is identified with the entire weak gradient in `L²`.
The scalar-domain witness is for the original anchored Neumann operator. -/
theorem anchoredGradient_graph_convergence (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f : ℕ → anchoredTestSubmodule n) (v a : Lp ℝ 2 (anchoredMeasureE χ))
    (hv : Tendsto (fun k => poissonAnchoredValue χ hc (anchoredTestHilbert χ hc (f k))) atTop (𝓝 v))
    (ha : Tendsto (fun k => (memLp_anchoredLangevinExpr χ hc (f k).property.1
      (f k).property.2.1 (f k).property.2.2).toLp (anchoredLangevinExpr χ (f k).val)) atTop (𝓝 a)) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    ∃ φ : PoissonAnchoredSpace χ hc, ∃ G : AnchoredVectorSobolev χ (anchoredMeasureE χ),
      poissonAnchoredValue χ hc φ = v ∧
      (∃ F : anchoredNeumannDomain χ,
        F.val = poissonAnchoredEquiv χ hc φ ∧ anchoredNeumannOperator χ F = a) ∧
      anchoredInverseValues (anchoredMeasureE χ) G.val = poissonAnchoredGradient χ hc φ ∧
      Tendsto (fun k => anchoredGradientFieldLin χ hc (f k)) atTop (𝓝 G) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  obtain ⟨φ, hval, hweak, _, hgrad⟩ := anchoredGradient_graph_convergence_scalar χ hc f v a hv ha
  have hA : CauchySeq (fun k => anchoredGradientSourceOperatorLin χ hc (f k)) := by
    have h : Tendsto (fun k => anchoredGradientSourceOperatorLin χ hc (f k)) atTop (𝓝 a) := by
      simpa only [anchoredGradientSourceOperatorLin_eq] using ha
    exact h.cauchySeq
  obtain ⟨G, hGlim⟩ := Internal.anchoredGradient_exists_limit χ hc f hgrad.cauchySeq hA
  refine ⟨φ, G, hval, ?_, Internal.anchoredGradient_limit_values χ hc f φ G hgrad hGlim, hGlim⟩
  let ψ := poissonAnchoredEquiv χ hc φ
  have hψ : IsAnchoredLangevin χ ψ.val.1 ψ.val.2 a := hweak
  let F : anchoredNeumannDomain χ := ⟨ψ, a, hψ⟩
  exact ⟨F, rfl, (anchoredNeumannOperator_eq_iff χ hc F a).mpr hψ⟩

end Riesz1
