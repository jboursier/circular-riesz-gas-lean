/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GradientConvergenceLinear
public import Riesz1.ToMathlib.GraphEnergyCauchy

/-! # Gradient convergence in the vector energy space

The full quotient graph-limit assertion of
Proposition 3.1. The scalar graph limit is
identified by the existing resolvent, and the integrated commutator makes
the gradients Cauchy in the existing complete vector space.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

namespace Internal

theorem hsGradient_cauchy (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (f : ℕ → hsTestSubmodule N)
    (hg : CauchySeq (fun k => hsSobolevGradient
      (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) (hsTestSobolev _ (f k))))
    (ha : CauchySeq (fun k => hsGradientSourceOperatorLin χ hN hc (f k))) :
    CauchySeq (fun k => hsGradientFieldLin χ hN hc
      (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) (f k)) := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  have : InnerProductSpace ℝ (HsVectorJet μ) := inferInstance
  exact cauchySeq_of_linear_graph_energy
    (T := hsTestSubmodule N) (V := HsVectorSobolev χ hN hc μ)
    (E := Lp (HsEuclidean N) 2 μ) (W := Lp ℝ 2 μ) (hsGradientFieldLin χ hN hc μ)
    ((hsSobolevGradient μ).toLinearMap.comp (hsTestSobolev μ))
    (hsGradientSourceOperatorLin χ hN hc) (hsGradientFieldLin_norm_sq χ hN hc) f hg ha

theorem hsGradient_exists_limit (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (f : ℕ → hsTestSubmodule N)
    (hg : CauchySeq (fun k => hsSobolevGradient
      (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) (hsTestSobolev _ (f k))))
    (ha : CauchySeq (fun k => hsGradientSourceOperatorLin χ hN hc (f k))) :
    ∃ G : HsVectorSobolev χ hN hc (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)),
      Tendsto (fun k => hsGradientFieldLin χ hN hc _ (f k)) atTop (𝓝 G) :=
  cauchySeq_tendsto_of_complete (hsGradient_cauchy χ hN hc f hg ha)

theorem hsGradient_limit_values (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (f : ℕ → hsTestSubmodule N)
    (φ : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (G : HsVectorSobolev χ hN hc (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (hgrad : Tendsto (fun k => hsSobolevGradient _ (hsTestSobolev _ (f k)))
      atTop (𝓝 (hsSobolevGradient _ φ)))
    (hGlim : Tendsto (fun k => hsGradientFieldLin χ hN hc _ (f k)) atTop (𝓝 G)) :
    ∀ i : Fin (N : ℕ), hsJetValue _ i G.val =
      (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 _ (hsSobolevGradient _ φ) := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  intro i
  let P : HsVectorSobolev χ hN hc μ →L[ℝ] Lp ℝ 2 μ :=
    (hsJetValue μ i).comp (hsVectorSobolevSubmodule χ hN hc μ).subtypeL
  have h1 : Tendsto (fun k => hsJetValue μ i (hsGradientFieldLin χ hN hc μ (f k)).val)
      atTop (𝓝 (hsJetValue μ i G.val)) := (P.continuous.tendsto G).comp hGlim
  have h2 := (((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ).continuous.tendsto
    (hsSobolevGradient μ φ)).comp hgrad
  simp_rw [hsGradientFieldLin_value] at h1
  exact tendsto_nhds_unique h1 h2

end Internal

/-- Full graph convergence on the quotient, including the vector energy norm.
The component values of the limiting vector are the coordinates of the scalar
weak gradient, which identifies it as `∇φ` in the completion. -/
theorem hsGradient_graph_convergence (hN : 2 ≤ (N : ℕ))
    (χ : HsPairPotentials N c) (hc : 0 < c) (f : ℕ → HsTestFunction N)
    (v a : Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (hv : Tendsto (fun k => hsSobolevValue _
      (hsSobolevOfSmooth _ ⟨(f k).toFun, (f k).smoothOnClosure⟩)) atTop (𝓝 v))
    (ha : Tendsto (fun k => (memLp_hsLangevin hN χ (f k)
      (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))).toLp (hsLangevin χ (f k)))
      atTop (𝓝 a)) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    ∃ φ : HsSobolev μ, ∃ G : HsVectorSobolev χ hN hc μ,
      hsSobolevValue μ φ = v ∧
      (∃ hφ : φ ∈ hsNeumannDomain μ, hsNeumannOperator χ hc ⟨φ, hφ⟩ = a) ∧
      (∀ i : Fin (N : ℕ), hsJetValue μ i G.val =
        (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ φ)) ∧
      Tendsto (fun k => hsVectorJetElt χ hN hc μ (hsGradientTestTuple hN (f k)))
        atTop (𝓝 G) := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  let t (k : ℕ) := hsGradientTestOfSource (f k)
  obtain ⟨φ, hval, hφ, hlim, hgrad⟩ := hsGradient_graph_convergence_scalar hN χ hc f v a hv ha
  have hG : CauchySeq (fun k => hsSobolevGradient μ (hsTestSobolev μ (t k))) := hgrad.cauchySeq
  have hA : CauchySeq (fun k => hsGradientSourceOperatorLin χ hN hc (t k)) := by
    have ha' : Tendsto (fun k => hsGradientSourceOperatorLin χ hN hc (t k)) atTop (𝓝 a) := by
      simpa only [t, hsGradientSourceOperatorLin_of_source] using ha
    exact ha'.cauchySeq
  have hex : ∃ G : HsVectorSobolev χ hN hc μ,
      Tendsto (fun k => hsGradientFieldLin χ hN hc μ (t k)) atTop (𝓝 G) :=
    Internal.hsGradient_exists_limit χ hN hc t hG hA
  obtain ⟨G, hGlim⟩ := hex
  have hvalues := Internal.hsGradient_limit_values χ hN hc t φ G hgrad hGlim
  refine ⟨φ, G, hval, hφ, hvalues, ?_⟩
  simpa only [t, hsGradientFieldLin_of_source] using hGlim

end Riesz1
