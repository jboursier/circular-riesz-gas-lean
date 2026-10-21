/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Orthogonal splitting along a unit vector preserves Lebesgue measure

For a unit vector `v` of a finite-dimensional real inner product space `E`, the map
`x ↦ (x - ⟪x, v⟫ v, ⟪x, v⟫)` separates `x` into its component in `(ℝ ∙ v)ᗮ` and its coordinate
along `v`. This file proves that this map is measure preserving from `E` to the product of the
inner-product volumes of `(ℝ ∙ v)ᗮ` and `ℝ`. The isometry `Submodule.orthogonalDecomposition`
is used only as a proof device. The statement involves the volumes alone.
-/

@[expose] public section

noncomputable section

open MeasureTheory Submodule
open scoped RealInnerProductSpace

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The component of `x` orthogonal to the unit vector `v`, as an element of `(ℝ ∙ v)ᗮ`. -/
def orthComponent {v : E} (hv : ‖v‖ = 1) (x : E) : (ℝ ∙ v)ᗮ :=
  ⟨x - ⟪x, v⟫ • v, by
    rw [mem_orthogonal_singleton_iff_inner_left, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hv]
    ring⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem coe_orthComponent {v : E} (hv : ‖v‖ = 1) (x : E) :
    (orthComponent hv x : E) = x - ⟪x, v⟫ • v :=
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The orthogonal component is the orthogonal projection onto `(ℝ ∙ v)ᗮ`, as an element of `E`. -/
theorem orthComponent_eq_starProjection {v : E} (hv : ‖v‖ = 1) (x : E) :
    (orthComponent hv x : E) = (ℝ ∙ v)ᗮ.starProjection x := by
  symm
  refine eq_starProjection_of_mem_of_inner_eq_zero (orthComponent hv x).2 ?_
  intro w hw
  have hx : x - (orthComponent hv x : E) = ⟪x, v⟫ • v := by
    rw [coe_orthComponent]
    abel
  rw [hx, real_inner_smul_left]
  rw [mem_orthogonal_singleton_iff_inner_right] at hw
  rw [hw, mul_zero]

/-- A unit vector `v` gives an isometry `(ℝ ∙ v)ᗮᗮ ≃ ℝ` sending `q` to `⟪q, v⟫`. -/
def orthCoordinate {v : E} (hv : ‖v‖ = 1) : ((ℝ ∙ v)ᗮ)ᗮ ≃ₗᵢ[ℝ] ℝ :=
  (LinearIsometryEquiv.ofEq _ _ (orthogonal_orthogonal (ℝ ∙ v))).trans
    (LinearIsometryEquiv.toSpanUnitSingleton v hv).symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem orthCoordinate_apply {v : E} (hv : ‖v‖ = 1) (q : ((ℝ ∙ v)ᗮ)ᗮ) :
    orthCoordinate hv q = ⟪(q : E), v⟫ := by
  have h1 : LinearIsometryEquiv.toSpanUnitSingleton v hv (orthCoordinate hv q) =
      LinearIsometryEquiv.ofEq _ _ (orthogonal_orthogonal (ℝ ∙ v)) q := by
    simp [orthCoordinate]
  have h2 : (orthCoordinate hv q • v : E) = (q : E) := by
    have := congrArg Subtype.val h1
    simpa [LinearIsometryEquiv.toSpanUnitSingleton_apply] using this
  rw [← h2, real_inner_smul_left, real_inner_self_eq_norm_sq, hv]
  ring

/-- The map `x ↦ (x - ⟪x, v⟫ v, ⟪x, v⟫)` preserves Lebesgue measure: the splitting of `E` into
`(ℝ ∙ v)ᗮ` and the line `ℝ ∙ v` is an isometry for the `L²` product, hence volume preserving. -/
theorem measurePreserving_orthSplit {v : E} (hv : ‖v‖ = 1) :
    MeasurePreserving (fun x : E => (orthComponent hv x, ⟪x, v⟫)) volume
      (volume.prod volume) := by
  let Ψ' : E ≃ₗᵢ[ℝ] WithLp 2 (↥((ℝ ∙ v)ᗮ) × ℝ) :=
    ((ℝ ∙ v)ᗮ).orthogonalDecomposition.trans
      (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ _) (orthCoordinate hv))
  have hcomp : MeasurePreserving (fun x : E => (Ψ' x).ofLp) volume (volume.prod volume) :=
    (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod ((ℝ ∙ v)ᗮ) ℝ).comp
      Ψ'.measurePreserving
  convert hcomp using 1
  funext x
  have hsum := Submodule.starProjection_add_starProjection_orthogonal (K := (ℝ ∙ v)ᗮ) x
  have hp : ⟪((ℝ ∙ v)ᗮ).starProjection x, v⟫ = 0 := by
    rw [real_inner_comm]
    exact mem_orthogonal_singleton_iff_inner_right.mp
      (Submodule.starProjection_apply_mem ((ℝ ∙ v)ᗮ) x)
  have hx : ⟪x, v⟫ = ⟪(((ℝ ∙ v)ᗮ)ᗮ).starProjection x, v⟫ := by
    calc ⟪x, v⟫
        = ⟪((ℝ ∙ v)ᗮ).starProjection x + (((ℝ ∙ v)ᗮ)ᗮ).starProjection x, v⟫ := by rw [hsum]
      _ = _ := by rw [inner_add_left, hp, zero_add]
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    simp [Ψ', orthComponent_eq_starProjection hv x]
  · simp [Ψ', orthCoordinate_apply, hx]

end Riesz1

end
