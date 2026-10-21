/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.CoercivityComplete
public import Riesz1.HelfferSjostrand.GradientConvergenceLinear
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The normalized vector energy space

The closed normalization subspaces, and coercivity
of the existing vector form on that subspace. Coordinates in finite products
are used only for continuous projections and pairings. The input fields are
the ordinary Euclidean-valued `L²` classes.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

/-- Coordinates of an ordinary vector-valued `L²` class. -/
def hsL2Coordinates (μ : Measure (HsConfiguration N)) :
    Lp (HsEuclidean N) 2 μ →L[ℝ] PiLp 2 (fun _ : Fin (N : ℕ) => Lp ℝ 2 μ) :=
  (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ)

/-- The expected coordinate sum of a vector-valued `L²` class. -/
def hsL2Mean (μ : Measure (HsConfiguration N)) [IsProbabilityMeasure μ] :
    Lp (HsEuclidean N) 2 μ →L[ℝ] ℝ :=
  ∑ i : Fin (N : ℕ), (poissonMean μ).comp ((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ)

/-- `L²₀(μ; ℝᴺ)`: only the mean rotation component vanishes. -/
abbrev hsMeanZeroL2 (μ : Measure (HsConfiguration N)) [IsProbabilityMeasure μ] :
    Submodule ℝ (Lp (HsEuclidean N) 2 μ) := (hsL2Mean μ).ker

/-- Component values of a vector jet. -/
def hsNonGradientValues (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    HsVectorJet μ →L[ℝ] PiLp 2 (fun _ : Fin (N : ℕ) => Lp ℝ 2 μ) :=
  (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => hsJetValue μ i)

variable (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
  (μ : Measure (HsConfiguration N)) [IsProbabilityMeasure μ]

local instance : NormedAddCommGroup (HsSobolev μ) := inferInstance
local instance : InnerProductSpace ℝ (HsSobolev μ) := inferInstance
local instance : NormedSpace ℝ (HsSobolev μ) := inferInstance
local instance : InnerProductSpace ℝ (PiLp 2 (fun _ : Fin (N : ℕ) => HsSobolev μ)) := inferInstance
local instance : NormedAddCommGroup (HsVectorJet μ) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorJet μ) := inferInstance
local instance : NormedSpace ℝ (HsVectorJet μ) := inferInstance
local instance : NormedAddCommGroup (HsVectorSobolev χ hN hc μ) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorSobolev χ hN hc μ) := inferInstance
local instance : NormedSpace ℝ (HsVectorSobolev χ hN hc μ) := inferInstance

/-- The expected coordinate sum on the vector completion. -/
def hsNonGradientMean : HsVectorSobolev χ hN hc μ →L[ℝ] ℝ :=
  (hsVectorMean μ).comp (hsVectorSobolevSubmodule χ hN hc μ).subtypeL

/-- `𝒱_{μ,0}` is the normalization kernel inside the completion. -/
abbrev hsMeanZeroVector : Submodule ℝ (HsVectorSobolev χ hN hc μ) :=
  (hsNonGradientMean χ hN hc μ).ker

namespace Internal

theorem nonGradient_sum_bilinear_apply {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (B : I → E →L[ℝ] E →L[ℝ] ℝ) (u w : E) :
    (∑ i, B i) u w = ∑ i, B i u w := by
  simp only [sum_apply]

end Internal

/-- The gradients and pair energy of the existing vector completion. -/
def hsNonGradientDifferential : HsVectorSobolev χ hN hc μ →L[ℝ]
    WithLp 2 (PiLp 2 (fun _ : Fin (N : ℕ) => Lp (HsEuclidean N) 2 μ) ×
      Lp (EuclideanSpace ℝ (HsPairIndex N)) 2 μ) := by
  let S := (hsVectorSobolevSubmodule χ hN hc μ).subtypeL
  let P := (WithLp.fstL 2 ℝ _ _).comp S
  let G (i : Fin (N : ℕ)) := (hsSobolevGradient μ).comp
    ((PiLp.proj 2 (fun _ : Fin (N : ℕ) => HsSobolev μ) i).comp P)
  let E := (WithLp.sndL 2 ℝ _ _).comp S
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    (((PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi G)).prod E)

/-- The existing form, bundled as a continuous bilinear map on `𝒱_μ`. -/
def hsNonGradientFullBilinear :
    HsVectorSobolev χ hN hc μ →L[ℝ] HsVectorSobolev χ hN hc μ →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (hsNonGradientDifferential χ hN hc μ)
    (hsNonGradientDifferential χ hN hc μ)

theorem hsNonGradientFullBilinear_eq (u w : HsVectorSobolev χ hN hc μ) :
    hsNonGradientFullBilinear χ hN hc μ u w = hsVectorSobolevForm χ hN hc μ u w := by
  change inner ℝ (hsNonGradientDifferential χ hN hc μ u)
    (hsNonGradientDifferential χ hN hc μ w) = _
  exact (WithLp.prod_inner_apply (hsNonGradientDifferential χ hN hc μ u)
    (hsNonGradientDifferential χ hN hc μ w)).trans
      (congrArg (· + inner ℝ u.val.ofLp.2 w.val.ofLp.2)
        (PiLp.inner_apply _ _))

theorem hsNonGradientFullBilinear_symm (u w : HsVectorSobolev χ hN hc μ) :
    hsNonGradientFullBilinear χ hN hc μ u w = hsNonGradientFullBilinear χ hN hc μ w u := by
  have h := hsNonGradientFullBilinear_eq χ hN hc μ u w
  have h' := hsNonGradientFullBilinear_eq χ hN hc μ w u
  apply h.trans
  apply Eq.trans _ h'.symm
  change (∑ i : Fin (N : ℕ), inner ℝ (hsSobolevGradient μ (u.val.ofLp.1 i))
      (hsSobolevGradient μ (w.val.ofLp.1 i))) + inner ℝ u.val.ofLp.2 w.val.ofLp.2 =
    (∑ i : Fin (N : ℕ), inner ℝ (hsSobolevGradient μ (w.val.ofLp.1 i))
      (hsSobolevGradient μ (u.val.ofLp.1 i))) + inner ℝ w.val.ofLp.2 u.val.ofLp.2
  exact congrArg₂ (· + ·) (Finset.sum_congr rfl (fun i _ => (real_inner_comm _ _).symm))
    (real_inner_comm _ _).symm

/-- Coercivity written as a norm estimate on normalized vectors. -/
theorem hsNonGradient_norm_bound (hPL : External.PrekopaLeindler)
    (u : HsVectorSobolev χ hN hc (hsQuotientGibbsProbability χ hc : Measure _))
    (hu : hsNonGradientMean χ hN hc _ u = 0) :
    ‖u‖ ^ 2 ≤ (1 + hsPoincareConstant N c) * hsVectorSobolevForm χ hN hc _ u u := by
  let ν : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  have hm : ∑ i, poissonMean ν (hsJetValue ν i u.val) = 0 := by
    rw [← hsVectorMean_eq_sum]
    exact hu
  have hb := hsVector_normalized_coercivity hPL χ hN hc u hm
  have hn := hsGradient_vector_norm_sq χ hN hc ν u
  linarith only [hb, hn]

end Riesz1
