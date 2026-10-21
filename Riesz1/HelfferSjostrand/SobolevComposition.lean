/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.Sobolev
public import Riesz1.ToMathlib.WeightedSobolev.SmoothComposition

/-!
# Smooth composition in the periodic Sobolev completion

The smooth case of the chain rule, for every
finite measure on the configuration quotient. This file does not assert
the extension from smooth scalar maps to arbitrary `C¹` or piecewise `C¹` maps.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal

namespace Riesz1

/-- Smooth scalar composition preserves the periodic smooth core. -/
theorem HsSmoothOnClosure.comp_smooth {N : ℕ+} {f : HsEuclidean N → ℝ}
    (hf : HsSmoothOnClosure N f) {T : ℝ → ℝ} (hT : ContDiff ℝ ∞ T) :
    HsSmoothOnClosure N (fun y => T (f y)) := by
  obtain ⟨hp, W, hW, hUW, hfW⟩ := hf
  exact ⟨fun k y => congrArg T (hp k y), W, hW, hUW, hT.comp_contDiffOn hfW⟩

/-- Classical gradient chain rule for smooth scalar composition. -/
theorem hsSmoothGradient_comp {N : ℕ+} (f : hsSmoothCore N)
    {T : ℝ → ℝ} (hT : ContDiff ℝ ∞ T) (x : HsConfiguration N) :
    hsSmoothGradient ⟨fun y => T (f.val y), f.property.comp_smooth hT⟩ x =
      deriv T (hsSmoothValue f.val x) • hsSmoothGradient f x := by
  let y := hsLiftPoint N x
  have hdf := f.property.differentiableAt (hsLiftPoint_mem_chamber N x)
  have hdT := (hT.differentiable (by norm_num) (f.val y)).hasDerivAt
  have he := (hdT.comp_hasFDerivAt y hdf.hasFDerivAt).fderiv
  change fderiv ℝ (fun z => T (f.val z)) y = _ at he
  change (InnerProductSpace.toDual ℝ (HsEuclidean N)).symm
      (fderiv ℝ (fun z => T (f.val z)) y) = _
  rw [he, map_smul]
  rfl

variable {N : ℕ+} (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]

/-- Smooth scalar composition satisfies the chain rule in the completed graph. -/
theorem hsSobolev_comp_smooth_graph (f : HsSobolev μ)
    {T : ℝ → ℝ} (hT : ContDiff ℝ ∞ T) (h0 : T 0 = 0) {C : ℝ≥0}
    (hb : ∀ r, ‖deriv T r‖₊ ≤ C) :
    WeightedSobolev.IsGraphH1 μ (fun _ : hsSmoothCore N => True)
      (fun φ => hsSmoothValue φ.val) hsSmoothGradient
      (fun x => T (hsSobolevValue μ f x))
      (fun x => deriv T (hsSobolevValue μ f x) • hsSobolevGradient μ f x) := by
  have hgraph := (hsSobolev_iff_graph μ (hsSobolevValue μ f) (hsSobolevGradient μ f)
    (Lp.memLp _) (Lp.memLp _)).mp (by
      simp only [Lp.toLp_coeFn]
      change WithLp.toLp 2 ((WithLp.ofLp f.val).1, (WithLp.ofLp f.val).2) ∈ hsSobolevSubmodule μ
      simpa only [Prod.mk.eta, WithLp.toLp_ofLp] using f.property)
  exact WeightedSobolev.Internal.graph_comp_smooth
    (fun φ _ => φ.property.memLp_value μ) (fun φ _ => φ.property.memLp_gradient μ)
    hT h0 hb (fun φ => ⟨fun y => T (φ.val y), φ.property.comp_smooth hT⟩)
    (fun _ _ => trivial) (fun _ _ _ => rfl) (fun φ _ x => hsSmoothGradient_comp φ hT x) hgraph

/-- Composition with a smooth map with bounded derivative, as an actual completed Sobolev jet. -/
def hsSobolevCompSmooth (f : HsSobolev μ)
    (T : ℝ → ℝ) (hT : ContDiff ℝ ∞ T) (h0 : T 0 = 0) (C : ℝ≥0)
    (hb : ∀ r, ‖deriv T r‖₊ ≤ C) : HsSobolev μ := by
  let h := hsSobolev_comp_smooth_graph μ f hT h0 hb
  exact ⟨WithLp.toLp 2 (h.1.toLp (fun x => T (hsSobolevValue μ f x)),
    h.2.1.toLp (fun x => deriv T (hsSobolevValue μ f x) • hsSobolevGradient μ f x)),
    (hsSobolev_iff_graph μ _ _ h.1 h.2.1).mpr h⟩

/-- The value of smooth composition is the pointwise scalar composition, almost everywhere. -/
theorem hsSobolevValue_compSmooth (f : HsSobolev μ)
    (T : ℝ → ℝ) (hT : ContDiff ℝ ∞ T) (h0 : T 0 = 0) (C : ℝ≥0)
    (hb : ∀ r, ‖deriv T r‖₊ ≤ C) :
    (hsSobolevValue μ (hsSobolevCompSmooth μ f T hT h0 C hb) : HsConfiguration N → ℝ) =ᵐ[μ]
      fun x => T (hsSobolevValue μ f x) :=
  (hsSobolev_comp_smooth_graph μ f hT h0 hb).1.coeFn_toLp

/-- The gradient formula for smooth composition in the completion. -/
theorem hsSobolevGradient_compSmooth (f : HsSobolev μ)
    (T : ℝ → ℝ) (hT : ContDiff ℝ ∞ T) (h0 : T 0 = 0) (C : ℝ≥0)
    (hb : ∀ r, ‖deriv T r‖₊ ≤ C) :
    (hsSobolevGradient μ (hsSobolevCompSmooth μ f T hT h0 C hb) :
      HsConfiguration N → HsEuclidean N) =ᵐ[μ]
      fun x => deriv T (hsSobolevValue μ f x) • hsSobolevGradient μ f x :=
  (hsSobolev_comp_smooth_graph μ f hT h0 hb).2.1.coeFn_toLp

end Riesz1

end
