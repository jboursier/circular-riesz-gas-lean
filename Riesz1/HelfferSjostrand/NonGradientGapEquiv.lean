/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.NonGradientGapVector

/-!
# Rotation, normalization, and the vector pairing

The rotations of the vector completion are invertible and preserve the
mean rotation component. The ordinary forcing pairing transforms by
the same pullback on both slots.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set InnerProductSpace

namespace Riesz1

variable {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)

local notation "μ" => (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))

theorem hsGapLpPull_add (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t s : ℝ) (f : Lp V 2 μ) :
    hsGapLpPull χ hc V t (hsGapLpPull χ hc V s f) = hsGapLpPull χ hc V (s + t) f := by
  apply Lp.ext
  have ht := (measurePreserving_hsGapRotate χ hc t).quasiMeasurePreserving.ae
    (hsGapLpPull_ae χ hc V s f)
  filter_upwards [hsGapLpPull_ae χ hc V t (hsGapLpPull χ hc V s f), ht,
    hsGapLpPull_ae χ hc V (s + t) f] with x hx hx' hx''
  exact hx.trans (hx'.trans ((congrArg f (hsGapRotate_add s t x)).trans hx''.symm))

theorem hsGapLpPull_zero (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Lp V 2 μ) : hsGapLpPull χ hc V 0 f = f := by
  apply Lp.ext
  filter_upwards [hsGapLpPull_ae χ hc V 0 f] with x hx
  simpa only [hsGapRotate_zero] using hx

theorem hsGapLpPull_neg (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t : ℝ) (f : Lp V 2 μ) : hsGapLpPull χ hc V t (hsGapLpPull χ hc V (-t) f) = f := by
  rw [hsGapLpPull_add, neg_add_cancel, hsGapLpPull_zero]

theorem hsGapLpPull_mean (t : ℝ) (f : Lp ℝ 2 μ) :
    poissonMean μ (hsGapLpPull χ hc ℝ t f) = poissonMean μ f := by
  rw [poissonMean_eq_integral, poissonMean_eq_integral,
    integral_congr_ae (hsGapLpPull_ae χ hc ℝ t f)]
  have hm := measurePreserving_hsGapRotate χ hc t
  have hf : AEStronglyMeasurable (f : HsConfiguration N → ℝ) (Measure.map (hsGapRotate t) μ) := by
    rw [hm.map_eq]
    exact Lp.aestronglyMeasurable f
  exact (integral_map hm.measurable.aemeasurable hf).symm.trans
    (congrArg (fun ν : Measure (HsConfiguration N) => ∫ x, f x ∂ν) hm.map_eq)

theorem hsGapLpPull_coord (t : ℝ) (v : Lp (HsEuclidean N) 2 μ) (i : Fin (N : ℕ)) :
    (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsGapLpPull χ hc (HsEuclidean N) t v) =
      hsGapLpPull χ hc ℝ t ((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ v) := by
  apply Lp.ext
  have ht := (measurePreserving_hsGapRotate χ hc t).quasiMeasurePreserving.ae
    (ContinuousLinearMap.coeFn_compLpL (EuclideanSpace.proj (𝕜 := ℝ) i) v)
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (EuclideanSpace.proj (𝕜 := ℝ) i)
      (hsGapLpPull χ hc (HsEuclidean N) t v), hsGapLpPull_ae χ hc (HsEuclidean N) t v,
    hsGapLpPull_ae χ hc ℝ t ((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ v), ht]
    with x hx hx' hx'' htx
  rw [hx, hx', hx'', htx]

variable (hN : 2 ≤ (N : ℕ))

local instance : NormedAddCommGroup (HsSobolev μ) := inferInstance
local instance : NormedSpace ℝ (HsSobolev μ) := inferInstance
local instance : InnerProductSpace ℝ (HsSobolev μ) := inferInstance
local instance : NormedAddCommGroup (HsVectorJet μ) := inferInstance
local instance : NormedSpace ℝ (HsVectorJet μ) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorJet μ) := inferInstance
local instance : NormedAddCommGroup (HsVectorSobolev χ hN hc μ) := inferInstance
local instance : NormedSpace ℝ (HsVectorSobolev χ hN hc μ) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorSobolev χ hN hc μ) := inferInstance

theorem hsGapVectorPull_neg (t : ℝ) (u : HsVectorSobolev χ hN hc μ) :
    hsGapVectorPull χ hc hN t (hsGapVectorPull χ hc hN (-t) u) = u := by
  apply sub_eq_zero.mp
  apply hsVectorSobolev_eq_zero_of_values χ hN hc
  intro i
  change hsJetValue μ i ((hsGapVectorPull χ hc hN t
    (hsGapVectorPull χ hc hN (-t) u)).val - u.val) = 0
  rw [map_sub, hsGapVectorPull_value, hsGapVectorPull_value, hsGapLpPull_neg, sub_self]

theorem hsGapVectorPull_mean (t : ℝ) (u : HsVectorSobolev χ hN hc μ) :
    hsNonGradientMean χ hN hc μ (hsGapVectorPull χ hc hN t u) =
      hsNonGradientMean χ hN hc μ u := by
  change hsVectorMean μ (hsGapVectorPull χ hc hN t u).val = hsVectorMean μ u.val
  calc
    _ = ∑ i : Fin (N : ℕ), poissonMean μ
        (hsJetValue μ i (hsGapVectorPull χ hc hN t u).val) :=
      hsVectorMean_eq_sum μ (hsGapVectorPull χ hc hN t u).val
    _ = ∑ i : Fin (N : ℕ), poissonMean μ (hsJetValue μ i u.val) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (congrArg (poissonMean μ) (hsGapVectorPull_value χ hc hN t u i)).trans
        (hsGapLpPull_mean χ hc t (hsJetValue μ i u.val))
    _ = _ := (hsVectorMean_eq_sum μ u.val).symm

/-- Common rotation on the normalized subspace. -/
def hsGapNormalizedPull (t : ℝ) : hsMeanZeroVector χ hN hc μ →ₗᵢ[ℝ] hsMeanZeroVector χ hN hc μ where
  toLinearMap := ((hsGapVectorPull χ hc hN t).toLinearMap.comp
    (hsMeanZeroVector χ hN hc μ).subtype).codRestrict (hsMeanZeroVector χ hN hc μ) (by
      intro u
      change hsNonGradientMean χ hN hc μ (hsGapVectorPull χ hc hN t u.val) = 0
      exact (hsGapVectorPull_mean χ hc hN t u.val).trans u.property)
  norm_map' u := (hsGapVectorPull χ hc hN t).norm_map u.val

theorem hsGapNormalizedPull_value (t : ℝ) (u : hsMeanZeroVector χ hN hc μ) (i : Fin (N : ℕ)) :
    hsJetValue μ i (hsGapNormalizedPull χ hc hN t u).val.val =
      hsGapLpPull χ hc ℝ t (hsJetValue μ i u.val.val) := rfl

theorem hsGap_pairing_coords (v : Lp (HsEuclidean N) 2 μ) (u : HsVectorJet μ) :
    hsNonGradientPairing μ v u = ∑ i : Fin (N : ℕ),
      inner ℝ ((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ v) (hsJetValue μ i u) :=
  PiLp.inner_apply (hsL2Coordinates μ v) (hsNonGradientValues μ u)

namespace Internal

theorem hsGap_pairing_pull_of_values (t : ℝ) (v : Lp (HsEuclidean N) 2 μ)
    (u w : HsVectorJet μ)
    (hw : ∀ i : Fin (N : ℕ), hsJetValue μ i w = hsGapLpPull χ hc ℝ t (hsJetValue μ i u)) :
    hsNonGradientPairing μ (hsGapLpPull χ hc (HsEuclidean N) t v) w =
      hsNonGradientPairing μ v u := by
  rw [hsGap_pairing_coords χ hc, hsGap_pairing_coords χ hc]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsGapLpPull_coord χ hc t v i, hw i]
  exact (hsGapLpPull χ hc ℝ t).inner_map_map _ _

end Internal

theorem hsGapVectorPull_pairing (t : ℝ) (v : Lp (HsEuclidean N) 2 μ)
    (u : HsVectorSobolev χ hN hc μ) :
    hsNonGradientPairing μ (hsGapLpPull χ hc (HsEuclidean N) t v)
      (hsGapVectorPull χ hc hN t u).val = hsNonGradientPairing μ v u.val :=
  Internal.hsGap_pairing_pull_of_values χ hc t v u.val
    (hsGapVectorPull χ hc hN t u).val (hsGapVectorPull_value χ hc hN t u)

theorem hsGapVectorPull_pairing_fixed (t : ℝ) (v : Lp (HsEuclidean N) 2 μ)
    (hv : hsGapLpPull χ hc (HsEuclidean N) t v = v)
    (u : HsVectorSobolev χ hN hc μ) :
    hsNonGradientPairing μ v (hsGapVectorPull χ hc hN t u).val = hsNonGradientPairing μ v u.val :=
  (congrArg (fun f => hsNonGradientPairing μ f (hsGapVectorPull χ hc hN t u).val) hv).symm.trans
    (hsGapVectorPull_pairing χ hc hN t v u)

namespace Internal

theorem hsGapLpPull_fixed_ae (t : ℝ) (f : Lp ℝ 2 μ)
    (hf : hsGapLpPull χ hc ℝ t f = f) :
    (fun x => f (hsGapRotate t x)) =ᵐ[μ] f := by
  have ha := hsGapLpPull_ae χ hc ℝ t f
  rw [hf] at ha
  exact ha.symm

theorem hsGapNormalizedPull_value_fixed (t : ℝ) (u : hsMeanZeroVector χ hN hc μ)
    (hu : hsGapNormalizedPull χ hc hN t u = u) (i : Fin (N : ℕ)) :
    (fun x => hsJetValue μ i u.val.val (hsGapRotate t x)) =ᵐ[μ] hsJetValue μ i u.val.val := by
  have he : hsGapLpPull χ hc ℝ t (hsJetValue μ i u.val.val) = hsJetValue μ i u.val.val :=
    (hsGapNormalizedPull_value χ hc hN t u i).symm.trans
      (congrArg (fun w : hsMeanZeroVector χ hN hc μ => hsJetValue μ i w.val.val) hu)
  exact hsGapLpPull_fixed_ae χ hc t (hsJetValue μ i u.val.val) he

end Internal

end Riesz1
