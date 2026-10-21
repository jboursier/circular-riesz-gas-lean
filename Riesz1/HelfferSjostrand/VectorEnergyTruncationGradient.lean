/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.AnchoredIntegrationByParts
public import Riesz1.HelfferSjostrand.AnchoredSobolevLevelSets
public import Riesz1.HelfferSjostrand.AnchoredSobolevPiecewiseComposition
public import Riesz1.ToMathlib.WeightedSobolev.TestDensity

/-!
# Weak gradients of positive parts in the anchored Sobolev space

Facts about the anchored weak gradient, used to identify the gradient of a truncation:

* two anchored Sobolev pairs with almost everywhere equal values have almost everywhere equal weak
  gradients (`IsAnchoredH1.grad_ae_eq_of_value_ae_eq`), by the directional integration by parts
  `anchoredH1_directional_integrationByParts` and the chart test lemma.
* the positive part `r ↦ max r 0` is `1`-Lipschitz, is smooth off zero, and has derivative `1` on
  `(0, ∞)` and `0` on `(-∞, 0)`, so `IsAnchoredH1.comp_piecewise` applies to it.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff InnerProductSpace

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- Two anchored Sobolev pairs with a.e. equal values have a.e. equal weak gradients. -/
theorem IsAnchoredH1.grad_ae_eq_of_value_ae_eq
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {F₁ F₂ : AnchoredEuclidean n → ℝ} {G₁ G₂ : AnchoredEuclidean n → AnchoredEuclidean n}
    (h₁ : IsAnchoredH1 χ F₁ G₁) (h₂ : IsAnchoredH1 χ F₂ G₂)
    (hF : F₁ =ᵐ[anchoredMeasureE χ] F₂) :
    G₁ =ᵐ[anchoredMeasureE χ] G₂ := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  let μ := anchoredMeasureE χ
  have hcoord (i : Fin n) : ∀ᵐ x ∂μ, G₁ x i = G₂ x i := by
    let p := EuclideanSpace.proj (𝕜 := ℝ) i
    let b₁ := p.compLpL 2 μ (h₁.2.1.toLp G₁)
    let b₂ := p.compLpL 2 μ (h₂.2.1.toLp G₂)
    -- The `i`-th coordinate of the weak gradient is the pairing with the basis vector `e_i`.
    have hb₁ : ∀ᵐ y ∂μ, b₁ y = inner ℝ (G₁ y) (EuclideanSpace.single i 1) := by
      filter_upwards [p.coeFn_compLpL (p := 2) (μ := μ) (h₁.2.1.toLp G₁),
        h₁.2.1.coeFn_toLp] with y hy hg
      rw [hy, hg]
      simp [p, EuclideanSpace.inner_single_right]
    have hb₂ : ∀ᵐ y ∂μ, b₂ y = inner ℝ (G₂ y) (EuclideanSpace.single i 1) := by
      filter_upwards [p.coeFn_compLpL (p := 2) (μ := μ) (h₂.2.1.toLp G₂),
        h₂.2.1.coeFn_toLp] with y hy hg
      rw [hy, hg]
      simp [p, EuclideanSpace.inner_single_right]
    have he : b₁ - b₂ = 0 := by
      apply Internal.eq_zero_of_chart_tests μ id MeasurableEmbedding.id
        (anchoredSimplex n) (isOpen_anchoredSimplex n) (ae_mem_anchoredSimplex χ)
      intro ψ hψ hψc hψU
      have hi₁ := anchoredH1_directional_integrationByParts χ hc h₁ hψ hψc hψU
        (EuclideanSpace.single i 1)
      have hi₂ := anchoredH1_directional_integrationByParts χ hc h₂ hψ hψc hψU
        (EuclideanSpace.single i 1)
      obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hψc
      have hint₁ : Integrable (fun x => ψ x * b₁ x) μ :=
        (Lp.memLp b₁).integrable one_le_two |>.bdd_mul hψ.continuous.aestronglyMeasurable
          (Eventually.of_forall fun x => hC x)
      have hint₂ : Integrable (fun x => ψ x * b₂ x) μ :=
        (Lp.memLp b₂).integrable one_le_two |>.bdd_mul hψ.continuous.aestronglyMeasurable
          (Eventually.of_forall fun x => hC x)
      calc ∫ x, ψ (id x) * (b₁ - b₂) x ∂μ
          = ∫ x, ψ x * b₁ x ∂μ - ∫ x, ψ x * b₂ x ∂μ := by
            rw [← integral_sub hint₁ hint₂]
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_sub b₁ b₂] with x hx
            rw [hx]
            simp only [id, Pi.sub_apply]
            ring
        _ = ∫ x, ψ x * inner ℝ (G₁ x) (EuclideanSpace.single i 1) ∂μ
            - ∫ x, ψ x * inner ℝ (G₂ x) (EuclideanSpace.single i 1) ∂μ := by
            congr 1
            · apply integral_congr_ae
              filter_upwards [hb₁] with x hx
              rw [hx]
            · apply integral_congr_ae
              filter_upwards [hb₂] with x hx
              rw [hx]
        _ = ∫ y, F₁ y * (ψ y * fderiv ℝ (hsAnchoredHamiltonianE χ) y (EuclideanSpace.single i 1)
              - fderiv ℝ ψ y (EuclideanSpace.single i 1)) ∂μ
            - ∫ y, F₂ y * (ψ y * fderiv ℝ (hsAnchoredHamiltonianE χ) y (EuclideanSpace.single i 1)
              - fderiv ℝ ψ y (EuclideanSpace.single i 1)) ∂μ := by
            rw [hi₁, hi₂]
        _ = 0 := by
            rw [sub_eq_zero]
            apply integral_congr_ae
            filter_upwards [hF] with y hy
            rw [hy]
    have hz : ∀ᵐ x ∂μ, (b₁ - b₂) x = 0 := by
      rw [he]
      exact Lp.coeFn_zero ℝ 2 μ
    filter_upwards [hz, Lp.coeFn_sub b₁ b₂, hb₁, hb₂] with x h0 hsub h1 h2
    have e : b₁ x - b₂ x = 0 := by
      calc b₁ x - b₂ x = (⇑b₁ - ⇑b₂) x := rfl
        _ = (b₁ - b₂) x := hsub.symm
        _ = 0 := h0
    have e' : inner ℝ (G₁ x) (EuclideanSpace.single i 1) =
        inner ℝ (G₂ x) (EuclideanSpace.single i 1) := by
      rw [← h1, ← h2]
      exact sub_eq_zero.mp e
    rw [EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_right] at e'
    simpa using e'
  filter_upwards [ae_all_iff.mpr hcoord] with x hx
  ext i
  exact hx i

/-- The positive part `r ↦ max r 0` has derivative `1` on the positive half line. -/
theorem hasDerivAt_max_zero_of_pos {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun x : ℝ => max x 0) 1 r := by
  refine (hasDerivAt_id r).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hr] with x hx
  exact max_eq_left (le_of_lt hx)

/-- The positive part `r ↦ max r 0` has derivative `0` on the negative half line. -/
theorem hasDerivAt_max_zero_of_neg {r : ℝ} (hr : r < 0) :
    HasDerivAt (fun x : ℝ => max x 0) 0 r := by
  refine (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hr] with x hx
  exact max_eq_right (le_of_lt hx)

/-- The positive part `r ↦ max r 0` is smooth off zero. -/
theorem contDiffOn_max_zero_compl :
    ContDiffOn ℝ 1 (fun x : ℝ => max x 0) {0}ᶜ := by
  intro r hr
  rcases lt_or_gt_of_ne hr with h | h
  · refine ContDiffAt.contDiffWithinAt ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_)
    filter_upwards [Iio_mem_nhds h] with x hx
    exact max_eq_right (le_of_lt hx)
  · refine ContDiffAt.contDiffWithinAt ((contDiffAt_id (𝕜 := ℝ) (E := ℝ)).congr_of_eventuallyEq ?_)
    filter_upwards [Ioi_mem_nhds h] with x hx
    exact max_eq_left (le_of_lt hx)

/-- The positive part `r ↦ max r 0` is `1`-Lipschitz. -/
theorem lipschitzWith_max_zero : LipschitzWith 1 (fun x : ℝ => max x 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [Real.dist_eq, Real.dist_eq]
  simpa using abs_max_sub_max_le_abs a b 0

end Riesz1
