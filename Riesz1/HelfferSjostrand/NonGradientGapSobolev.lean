/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.NonGradientGapFactorization

/-!
# Rotation on the scalar Sobolev completion

Common rotation preserves values and gradients of the smooth core and
therefore acts isometrically on the scalar Sobolev completion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set InnerProductSpace Topology
open scoped ContDiff

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

theorem hsGap_translate_eq_add (t : ℝ) (x : HsEuclidean N) :
    hsTranslate t x = x + WithLp.toLp 2 (fun _ : Fin (N : ℕ) => t) := by
  ext i
  rfl

theorem hsGap_periodic_pull {V : Type*} (F : HsEuclidean N → V)
    (hF : ∀ (k : ℤ) x, F (hsTranslate (k : ℝ) x) = F x)
    (t : ℝ) (x : HsConfiguration N) :
    F (hsLiftPoint N (hsGapRotate t x)) = F (hsTranslate t (hsLiftPoint N x)) := by
  rw [hsGapRotate_lift]
  have he : hsTranslate (t - ⌊hsLiftPoint N x ⟨0, N.pos⟩ + t⌋) (hsLiftPoint N x) =
      hsTranslate ((-⌊hsLiftPoint N x ⟨0, N.pos⟩ + t⌋ : ℤ) : ℝ)
        (hsTranslate t (hsLiftPoint N x)) := by
    rw [hsTranslate_add, Int.cast_neg]
    congr 1
    ring
  rw [he, hF]

theorem HsSmoothOnClosure.hsGap_pull {f : HsEuclidean N → ℝ}
    (hf : HsSmoothOnClosure N f) (t : ℝ) :
    HsSmoothOnClosure N (fun x => f (hsTranslate t x)) := by
  have ht : ContDiff ℝ ∞ (hsTranslate (N := N) t) := by
    have he : hsTranslate (N := N) t =
        (fun x => x + WithLp.toLp 2 (fun _ : Fin (N : ℕ) => t)) :=
      funext (hsGap_translate_eq_add t)
    rw [he]
    exact contDiff_id.add contDiff_const
  obtain ⟨hp, U, hU, hcU, hfU⟩ := hf
  refine ⟨?_, (hsTranslate t) ⁻¹' U, hU.preimage ht.continuous, ?_,
    hfU.comp ht.contDiffOn (fun _ hx => hx)⟩
  · intro k x
    dsimp only
    rw [hsTranslate_add, add_comm t (k : ℝ), ← hsTranslate_add, hp]
  · intro x hx
    exact hcU ((MapsTo.closure
      (fun y hy => (hsTranslate_mem_chamber_iff t y).mpr hy) ht.continuous) hx)

/-- Pullback on the existing smooth core. -/
def hsGapSmoothPull (t : ℝ) : hsSmoothCore N →ₗ[ℝ] hsSmoothCore N where
  toFun f := ⟨fun x => f.val (hsTranslate t x), f.property.hsGap_pull t⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem hsGap_gradient_pull (f : HsEuclidean N → ℝ) (t : ℝ) (x : HsEuclidean N) :
    gradient (fun y => f (hsTranslate t y)) x = gradient f (hsTranslate t x) := by
  simp_rw [hsGap_translate_eq_add]
  unfold gradient
  rw [fderiv_comp_add_right]

variable (χ : HsPairPotentials N c) (hc : 0 < c)

local notation "μ" => (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))

/-- Rotation pullback on ordinary `L²` classes, for any real normed target. -/
def hsGapLpPull (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (t : ℝ) :
    Lp V 2 μ →ₗᵢ[ℝ] Lp V 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℝ (hsGapRotate t) (measurePreserving_hsGapRotate χ hc t)

theorem hsGapLpPull_ae (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t : ℝ) (f : Lp V 2 μ) :
    (hsGapLpPull χ hc V t f : HsConfiguration N → V) =ᵐ[μ] fun x => f (hsGapRotate t x) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_hsGapRotate χ hc t)

local instance : NormedAddCommGroup (HsSobolev μ) := inferInstance
local instance : NormedSpace ℝ (HsSobolev μ) := inferInstance
local instance : InnerProductSpace ℝ (HsSobolev μ) := inferInstance

/-- Pull back both entries of the existing value/gradient jet. -/
def hsGapScalarJetPull (t : ℝ) :
    WeightedSobolev.L2Jet μ (HsEuclidean N) →ₗᵢ[ℝ] WeightedSobolev.L2Jet μ (HsEuclidean N) :=
  (hsGapLpPull χ hc ℝ t).withLpProdMap 2 (hsGapLpPull χ hc (HsEuclidean N) t)

theorem hsGapScalarJetPull_smooth (t : ℝ) (f : hsSmoothCore N) :
    hsGapScalarJetPull χ hc t (hsSmoothJet μ f) =
      hsSmoothJet μ (hsGapSmoothPull t f) := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · apply Lp.ext
    have hv := (f.property.memLp_value μ).coeFn_toLp
    have ht := (measurePreserving_hsGapRotate χ hc t).quasiMeasurePreserving.ae hv
    filter_upwards [hsGapLpPull_ae χ hc ℝ t
      ((f.property.memLp_value μ).toLp (hsSmoothValue f.val)), ht,
      ((hsGapSmoothPull t f).property.memLp_value μ).coeFn_toLp] with x hx hx' hx''
    exact hx.trans (hx'.trans ((hsGap_periodic_pull f.val f.property.1 t x).trans hx''.symm))
  · apply Lp.ext
    have hg := (f.property.memLp_gradient μ).coeFn_toLp
    have ht := (measurePreserving_hsGapRotate χ hc t).quasiMeasurePreserving.ae hg
    filter_upwards [hsGapLpPull_ae χ hc (HsEuclidean N) t
      ((f.property.memLp_gradient μ).toLp (hsSmoothGradient f)), ht,
      ((hsGapSmoothPull t f).property.memLp_gradient μ).coeFn_toLp] with x hx hx' hx''
    apply hx.trans
    apply hx'.trans
    change gradient f.val (hsLiftPoint N (hsGapRotate t x)) = _
    rw [hsGap_periodic_pull (gradient f.val) (fun k y =>
      scalarPoincare_gradient_translate f.property k y)]
    exact (hsGap_gradient_pull f.val t (hsLiftPoint N x)).symm.trans hx''.symm

theorem hsGapScalarJetPull_mem (t : ℝ) (f : HsSobolev μ) :
    hsGapScalarJetPull χ hc t f.val ∈ hsSobolevSubmodule μ := by
  have hm : MapsTo (hsGapScalarJetPull χ hc t)
      (LinearMap.range (hsSmoothJet μ) : Set _)
      (LinearMap.range (hsSmoothJet μ) : Set _) := by
    rintro _ ⟨g, rfl⟩
    exact ⟨hsGapSmoothPull t g, (hsGapScalarJetPull_smooth χ hc t g).symm⟩
  exact hm.closure (hsGapScalarJetPull χ hc t).continuous f.property

/-- Common rotation acts isometrically on the scalar completion. -/
def hsGapSobolevPull (t : ℝ) : HsSobolev μ →ₗᵢ[ℝ] HsSobolev μ where
  toLinearMap := ((hsGapScalarJetPull χ hc t).toLinearMap.comp
    (hsSobolevSubmodule μ).subtype).codRestrict (hsSobolevSubmodule μ)
      (hsGapScalarJetPull_mem χ hc t)
  norm_map' f := (hsGapScalarJetPull χ hc t).norm_map f.val

theorem hsGapSobolevPull_value (t : ℝ) (f : HsSobolev μ) :
    hsSobolevValue μ (hsGapSobolevPull χ hc t f) = hsGapLpPull χ hc ℝ t (hsSobolevValue μ f) := rfl

theorem hsGapSobolevPull_gradient (t : ℝ) (f : HsSobolev μ) :
    hsSobolevGradient μ (hsGapSobolevPull χ hc t f) =
      hsGapLpPull χ hc (HsEuclidean N) t (hsSobolevGradient μ f) := rfl

end Riesz1
