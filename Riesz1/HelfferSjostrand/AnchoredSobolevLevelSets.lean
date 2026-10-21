/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.AnchoredSobolevComposition
public import Riesz1.HelfferSjostrand.AnchoredIntegrationByParts
public import Riesz1.ToMathlib.WeightedSobolev.LevelSetGraph

/-!
# Closability and level sets for the anchored law

Compact directional tests detect
zero-value jets. Smooth flattening then gives vanishing on every level set.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- A zero anchored Sobolev value has zero weak gradient. -/
theorem IsAnchoredH1.gradient_eq_zero_of_value_eq_zero
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {F : AnchoredEuclidean n → ℝ} {G : AnchoredEuclidean n → AnchoredEuclidean n}
    (hFG : IsAnchoredH1 χ F G) (hF : F =ᵐ[anchoredMeasureE χ] 0) :
    G =ᵐ[anchoredMeasureE χ] 0 := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  let μ := anchoredMeasureE χ
  let g := hFG.2.1.toLp G
  have hcoord (i : Fin n) : ∀ᵐ x ∂μ, G x i = 0 := by
    let p := EuclideanSpace.proj (𝕜 := ℝ) i
    have he : p.compLpL 2 μ g = 0 := by
      apply Internal.eq_zero_of_chart_tests μ id MeasurableEmbedding.id
        (anchoredSimplex n) (isOpen_anchoredSimplex n) (ae_mem_anchoredSimplex χ)
      intro ψ hψ hψc hψU
      have hi := anchoredH1_directional_integrationByParts χ hc hFG hψ hψc hψU
        (EuclideanSpace.single i 1)
      have hz : (∫ y, F y * (ψ y * fderiv ℝ (hsAnchoredHamiltonianE χ) y
          (EuclideanSpace.single i 1) - fderiv ℝ ψ y (EuclideanSpace.single i 1)) ∂μ) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [hF] with y hy
        rw [hy]
        exact zero_mul _
      calc
        _ = ∫ y, ψ y * inner ℝ (G y) (EuclideanSpace.single i 1) ∂μ := by
          apply integral_congr_ae
          filter_upwards [p.coeFn_compLpL (p := 2) (μ := μ) g, hFG.2.1.coeFn_toLp]
            with y hy hgy
          rw [hy, hgy, EuclideanSpace.inner_single_right]
          simp only [p, RCLike.conj_to_real, one_mul, id_eq]
          rfl
        _ = _ := hi
        _ = 0 := hz
    filter_upwards [p.coeFn_compLpL (p := 2) (μ := μ) g,
      hFG.2.1.coeFn_toLp, Lp.coeFn_zero ℝ 2 μ] with y hy hgy h0
    rw [he, h0, hgy] at hy
    exact hy.symm
  filter_upwards [ae_all_iff.mpr hcoord] with y hy
  ext i
  exact hy i

/-- The anchored weak gradient vanishes almost everywhere on each level set. -/
theorem IsAnchoredH1.gradient_eq_zero_on_level
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {F : AnchoredEuclidean n → ℝ} {G : AnchoredEuclidean n → AnchoredEuclidean n}
    (hFG : IsAnchoredH1 χ F G) (a : ℝ) :
    ∀ᵐ x ∂anchoredMeasureE χ, F x = a → G x = 0 := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  have hgraph := WeightedSobolev.Internal.graph_levelSet
    (P := WeightedSobolev.SmoothNearClosure (anchoredSimplex n)) (value := id) (grad := gradient)
    (fun φ hφ => (WeightedSobolev.memLp_of_smoothNearClosure
      (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex χ) hφ).1)
    (fun φ hφ => (WeightedSobolev.memLp_of_smoothNearClosure
      (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex χ) hφ).2)
    hFG.1 hFG.2.1 (fun _ hS hS0 _ hSb => hFG.comp_smooth χ hc hS hS0 hSb) a
  have hz := IsAnchoredH1.gradient_eq_zero_of_value_eq_zero χ hc hgraph Filter.EventuallyEq.rfl
  filter_upwards [hz] with x hx hxa
  change (if F x = a then G x else 0) = 0 at hx
  rwa [ite_eq_left hxa] at hx

end Riesz1

end
