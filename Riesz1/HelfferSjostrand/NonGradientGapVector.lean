/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.NonGradientGapSobolev

/-!
# Rotation on the vector energy completion

Rotation acts on the scalar components and on their pair Hessian energy.
The pair weights depend only on coordinate differences, so this action
preserves the test jets and the existing completion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set InnerProductSpace Topology
open scoped ContDiff

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

theorem hsGap_infEDist_translate (t : ℝ) (x : HsEuclidean N) :
    Metric.infEDist (hsTranslate t x) (hsChamber N)ᶜ = Metric.infEDist x (hsChamber N)ᶜ := by
  have he : hsTranslate t '' (hsChamber N)ᶜ = (hsChamber N)ᶜ := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact fun h => hz ((hsTranslate_mem_chamber_iff t z).mp h)
    · intro hy
      refine ⟨hsTranslate (-t) y, fun h => hy ((hsTranslate_mem_chamber_iff (-t) y).mp h), ?_⟩
      rw [hsTranslate_add, add_neg_cancel, hsTranslate_zero]
  conv_lhs => rw [← he]
  exact Metric.infEDist_image (isometry_hsTranslate N t)

/-- Common translation on the collision-free scalar tests. -/
def hsGapTestPull (t : ℝ) : hsTestSubmodule N →ₗ[ℝ] hsTestSubmodule N where
  toFun f := ⟨fun x => f.val (hsTranslate t x), by
    obtain ⟨hs, hp, δ, hδ, hsupport⟩ := f.property
    refine ⟨?_, ?_, δ, hδ, ?_⟩
    · simp_rw [hsGap_translate_eq_add]
      exact hs.comp (contDiff_id.add contDiff_const)
    · intro k x
      dsimp only
      rw [hsTranslate_add, add_comm t (k : ℝ), ← hsTranslate_add, hp]
    · intro x hx
      exact (hsupport _ hx).trans_eq (hsGap_infEDist_translate t x)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem hsGap_energyWeight_translate (χ : HsPairPotentials N c) (p : HsPairIndex N)
    (t : ℝ) (x : HsEuclidean N) :
    hsEnergyWeight χ p (hsTranslate t x) = hsEnergyWeight χ p x := by
  unfold hsEnergyWeight
  simp only [hsTranslate_apply, add_sub_add_right_eq_sub]

theorem hsGap_energy_translate (χ : HsPairPotentials N c)
    (t : ℝ) (x v : HsEuclidean N) :
    hsHessianEnergy χ (hsTranslate t x) v = hsHessianEnergy χ x v := by
  ext p
  simp only [hsHessianEnergy, PiLp.toLp_apply, hsGap_energyWeight_translate]

variable (χ : HsPairPotentials N c) (hc : 0 < c)

local notation "μ" => (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))

local instance : NormedAddCommGroup (HsSobolev μ) := inferInstance
local instance : NormedSpace ℝ (HsSobolev μ) := inferInstance
local instance : InnerProductSpace ℝ (HsSobolev μ) := inferInstance
local instance : NormedAddCommGroup (HsVectorJet μ) := inferInstance
local instance : NormedSpace ℝ (HsVectorJet μ) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorJet μ) := inferInstance

/-- Apply the scalar Sobolev isometry to each component. -/
def hsGapSobolevTuplePull (t : ℝ) :
    PiLp 2 (fun _ : Fin (N : ℕ) => HsSobolev μ) →ₗᵢ[ℝ]
      PiLp 2 (fun _ : Fin (N : ℕ) => HsSobolev μ) where
  toLinearMap := (PiLp.continuousLinearEquiv 2 ℝ _).symm.toLinearMap.comp
    (LinearMap.pi fun i => (hsGapSobolevPull χ hc t).toLinearMap.comp
      (PiLp.proj 2 (fun _ : Fin (N : ℕ) => HsSobolev μ) i).toLinearMap)
  norm_map' f := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (· ^ 2) ((hsGapSobolevPull χ hc t).norm_map (f i))

/-- Rotation of all entries of the vector jet. -/
def hsGapVectorJetPull (t : ℝ) : HsVectorJet μ →ₗᵢ[ℝ] HsVectorJet μ :=
  (hsGapSobolevTuplePull χ hc t).withLpProdMap 2
    (hsGapLpPull χ hc (EuclideanSpace ℝ (HsPairIndex N)) t)

variable (hN : 2 ≤ (N : ℕ))

theorem hsGapVectorJetPull_test (t : ℝ) (u : HsVectorTest N) :
    hsGapVectorJetPull χ hc t (hsVectorJet χ hN hc μ u) =
      hsVectorJet χ hN hc μ (fun i => hsGapTestPull t (u i)) := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · ext i
    exact hsGapScalarJetPull_smooth χ hc t
      ⟨(u i).val, HsTestSubmodule.smoothOnClosure (u i).property⟩
  · apply Lp.ext
    let F : HsEuclidean N → EuclideanSpace ℝ (HsPairIndex N) := fun y =>
      hsHessianEnergy χ y (hsTestVector u y)
    have hp : ∀ (k : ℤ) y, F (hsTranslate (k : ℝ) y) = F y := by
      intro k y
      change hsHessianEnergy χ (hsTranslate (k : ℝ) y)
        (hsTestVector u (hsTranslate (k : ℝ) y)) = _
      rw [hsGap_energy_translate]
      congr 1
      ext i
      exact (u i).property.2.1 k y
    have ht := (measurePreserving_hsGapRotate χ hc t).quasiMeasurePreserving.ae
      (memLp_hsTestEnergyFun χ hN hc μ u).coeFn_toLp
    filter_upwards [hsGapLpPull_ae χ hc (EuclideanSpace ℝ (HsPairIndex N)) t
      ((memLp_hsTestEnergyFun χ hN hc μ u).toLp (hsTestEnergyFun χ u)), ht,
      (memLp_hsTestEnergyFun χ hN hc μ (fun i => hsGapTestPull t (u i))).coeFn_toLp]
      with x hx hx' hx''
    apply hx.trans (hx'.trans _)
    change F (hsLiftPoint N (hsGapRotate t x)) = _
    rw [hsGap_periodic_pull F hp]
    apply Eq.trans _ hx''.symm
    exact hsGap_energy_translate χ t (hsLiftPoint N x) _

theorem hsGapVectorJetPull_mem (t : ℝ) (u : HsVectorSobolev χ hN hc μ) :
    hsGapVectorJetPull χ hc t u.val ∈ hsVectorSobolevSubmodule χ hN hc μ := by
  have hm : MapsTo (hsGapVectorJetPull χ hc t)
      (LinearMap.range (hsVectorJetLin χ hN hc μ) : Set _)
      (LinearMap.range (hsVectorJetLin χ hN hc μ) : Set _) := by
    rintro _ ⟨w, rfl⟩
    exact ⟨(fun i => hsGapTestPull t (w i)), (hsGapVectorJetPull_test χ hc hN t w).symm⟩
  exact hm.closure (hsGapVectorJetPull χ hc t).continuous u.property

/-- Rotation on the actual vector energy completion. -/
def hsGapVectorPull (t : ℝ) :
    HsVectorSobolev χ hN hc μ →ₗᵢ[ℝ] HsVectorSobolev χ hN hc μ where
  toLinearMap := ((hsGapVectorJetPull χ hc t).toLinearMap.comp
    (hsVectorSobolevSubmodule χ hN hc μ).subtype).codRestrict
      (hsVectorSobolevSubmodule χ hN hc μ) (hsGapVectorJetPull_mem χ hc hN t)
  norm_map' u := (hsGapVectorJetPull χ hc t).norm_map u.val

theorem hsGapVectorPull_value (t : ℝ) (u : HsVectorSobolev χ hN hc μ) (i : Fin (N : ℕ)) :
    hsJetValue μ i (hsGapVectorPull χ hc hN t u).val =
      hsGapLpPull χ hc ℝ t (hsJetValue μ i u.val) := rfl

theorem hsGapVectorPull_form (t : ℝ) (u w : HsVectorSobolev χ hN hc μ) :
    hsVectorSobolevForm χ hN hc μ (hsGapVectorPull χ hc hN t u) (hsGapVectorPull χ hc hN t w) =
      hsVectorSobolevForm χ hN hc μ u w := by
  change (∑ i : Fin (N : ℕ), inner ℝ
      (hsGapLpPull χ hc (HsEuclidean N) t (hsSobolevGradient μ (u.val.ofLp.1 i)))
      (hsGapLpPull χ hc (HsEuclidean N) t (hsSobolevGradient μ (w.val.ofLp.1 i)))) +
      inner ℝ (hsGapLpPull χ hc (EuclideanSpace ℝ (HsPairIndex N)) t u.val.ofLp.2)
        (hsGapLpPull χ hc (EuclideanSpace ℝ (HsPairIndex N)) t w.val.ofLp.2) = _
  simp only [LinearIsometry.inner_map_map]
  rfl

end Riesz1
