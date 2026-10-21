/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.QuotientChartWeakGradient
public import Riesz1.HelfferSjostrand.SobolevCalculus

/-!
# The Gibbs Sobolev realization with quotient charts

The Gibbs Sobolev realization includes completion, integral norm,
injection into L², smooth density, chart weak gradients, scalar chain rules,
level sets, and truncations. All objects are the completion and
calculus operations. The additional general-density and Euclidean results
are not restated here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter
open scoped ContDiff ENNReal NNReal Topology

namespace Riesz1

/-- The defining properties of the Gibbs H¹ space, assembled
with the ordinary chart weak-gradient clause. -/
theorem hsSobolev_gibbs_definition {N : ℕ+} {c : ℝ}
    (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c) (hc : 0 < c) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    CompleteSpace (HsSobolev μ) ∧
    Injective (hsSobolevValue μ) ∧ DenseRange (hsSobolevOfSmooth μ) ∧
    ∀ f : HsSobolev μ,
      (‖f‖ ^ 2 = ∫ x, (hsSobolevValue μ f x) ^ 2 + ‖hsSobolevGradient μ f x‖ ^ 2 ∂μ) ∧
      (∀ (U : Set (HsEuclidean N)) (_hUo : IsOpen U) (hU : U ⊆ hsChamber N),
        let q : U → HsConfiguration N := fun x => hsChamberProjection ⟨x.val, hU x.property⟩
        let ν := Measure.comap (Subtype.val : U → HsEuclidean N) volume
        LocallyIntegrable (fun x => hsSobolevValue μ f (q x)) ν ∧
        LocallyIntegrable (fun x => hsSobolevGradient μ f (q x)) ν ∧
        ∀ ψ : HsEuclidean N → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
          ∀ v : HsEuclidean N,
            (∫ x : U, ψ x.val * inner ℝ (hsSobolevGradient μ f (q x)) v ∂ν) =
              -(∫ x : U, hsSobolevValue μ f (q x) * fderiv ℝ ψ x.val v ∂ν)) ∧
      (∀ (T : ℝ → ℝ) (hT : ContDiff ℝ 1 T) (h0 : T 0 = 0)
        (C : ℝ≥0) (hb : ∀ r, ‖deriv T r‖₊ ≤ C),
        (hsSobolevValue μ (hsSobolevCompC1 μ f T hT h0 C hb) : HsConfiguration N → ℝ) =ᵐ[μ]
          (fun x => T (hsSobolevValue μ f x)) ∧
        (hsSobolevGradient μ (hsSobolevCompC1 μ f T hT h0 C hb) :
          HsConfiguration N → HsEuclidean N) =ᵐ[μ]
          (fun x => deriv T (hsSobolevValue μ f x) • hsSobolevGradient μ f x)) ∧
      (∀ (T : ℝ → ℝ) (C : ℝ≥0) (hT : LipschitzWith C T) (h0 : T 0 = 0)
        (B : Set ℝ) (hB : B.Finite) (hTC : ContDiffOn ℝ 1 T Bᶜ),
        (hsSobolevValue μ (hsSobolevCompPiecewise χ hc f T C hT h0 B hB hTC) :
          HsConfiguration N → ℝ) =ᵐ[μ] (fun x => T (hsSobolevValue μ f x)) ∧
        (hsSobolevGradient μ (hsSobolevCompPiecewise χ hc f T C hT h0 B hB hTC) :
          HsConfiguration N → HsEuclidean N) =ᵐ[μ]
          (fun x => deriv T (hsSobolevValue μ f x) • hsSobolevGradient μ f x)) ∧
      (∀ a : ℝ, ∀ᵐ x ∂μ, hsSobolevValue μ f x = a → hsSobolevGradient μ f x = 0) ∧
      (∀ (R : ℝ) (hR : 0 ≤ R),
        (hsSobolevValue μ (hsSobolevClip χ hc f R hR) : HsConfiguration N → ℝ) =ᵐ[μ]
          (fun x => WeightedSobolev.clipReal R (hsSobolevValue μ f x)) ∧
        (hsSobolevGradient μ (hsSobolevClip χ hc f R hR) :
          HsConfiguration N → HsEuclidean N) =ᵐ[μ]
          {x | |hsSobolevValue μ f x| < R}.indicator (hsSobolevGradient μ f)) ∧
      Tendsto (fun n : ℕ => hsSobolevClip χ hc f n (Nat.cast_nonneg n)) atTop (𝓝 f) := by
  dsimp only
  refine ⟨inferInstance, hsSobolevValue_injective χ hc, denseRange_hsSobolevOfSmooth _, ?_⟩
  intro f
  refine ⟨hsSobolev_norm_sq_eq_integral _ f, ?_, ?_, ?_, ?_, ?_, tendsto_hsSobolevClip χ hc f⟩
  · intro U hUo hU
    exact hsSobolev_chart hN χ hc f hUo hU
  · intro T hT h0 C hb
    exact ⟨hsSobolevValue_compC1 _ f T hT h0 C hb,
      hsSobolevGradient_compC1 _ f T hT h0 C hb⟩
  · intro T C hT h0 B hB hTC
    exact ⟨hsSobolevValue_compPiecewise χ hc f T C hT h0 B hB hTC,
      hsSobolevGradient_compPiecewise χ hc f T C hT h0 B hB hTC⟩
  · exact hsSobolevGradient_eq_zero_on_level χ hc f
  · intro R hR
    exact ⟨hsSobolevValue_clip χ hc f R hR, hsSobolevGradient_clip χ hc f R hR⟩

end Riesz1
