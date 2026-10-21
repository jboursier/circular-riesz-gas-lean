/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SobolevComposition
public import Riesz1.HelfferSjostrand.SobolevClosability
public import Riesz1.ToMathlib.WeightedSobolev.LevelSetGraph

/-!
# Vanishing of the Gibbs weak gradient on level sets

Smooth flattening maps produce a vertical jet
whose gradient is the original gradient restricted to a level set.
The closability theorem forces that jet to vanish.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set

namespace Riesz1

/-- The weak gradient vanishes almost everywhere on each individual level set. -/
theorem hsSobolevGradient_eq_zero_on_level {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (a : ℝ) :
    ∀ᵐ x ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)),
      hsSobolevValue _ f x = a → hsSobolevGradient _ f x = 0 := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  let F := hsSobolevValue μ f
  let G := hsSobolevGradient μ f
  let D := {x | F x = a}.indicator (G : HsConfiguration N → HsEuclidean N)
  have hgraph := WeightedSobolev.Internal.graph_levelSet
    (fun φ _ => φ.property.memLp_value μ) (fun φ _ => φ.property.memLp_gradient μ)
    (Lp.memLp F) (Lp.memLp G)
    (fun _ hS hS0 _ hSb => hsSobolev_comp_smooth_graph μ f hS hS0 hSb) a
  let u : HsSobolev μ := ⟨WithLp.toLp 2 (hgraph.1.toLp (fun _ => 0), hgraph.2.1.toLp D),
    (hsSobolev_iff_graph μ _ _ hgraph.1 hgraph.2.1).mpr hgraph⟩
  have hu : hsSobolevValue μ u = 0 := MemLp.toLp_zero hgraph.1
  have hz : hgraph.2.1.toLp D = 0 :=
    Internal.hsSobolevGradient_eq_zero_of_value_eq_zero χ hc u hu
  have he : D =ᵐ[μ] 0 := by
    filter_upwards [hgraph.2.1.coeFn_toLp, Lp.coeFn_zero (HsEuclidean N) 2 μ] with x hx h0
    rw [hz, h0] at hx
    exact hx.symm
  filter_upwards [he] with x hx hxa
  change D x = 0 at hx
  change F x = a at hxa
  change G x = 0
  change (if F x = a then G x else 0) = 0 at hx
  rwa [ite_eq_left hxa] at hx

end Riesz1

end
