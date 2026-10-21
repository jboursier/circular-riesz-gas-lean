/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.ScalarPoincareProduct
public import Riesz1.ToMathlib.CircleSobolevProduct
public import Riesz1.ToMathlib.WeightedSobolev.GraphTransport

/-!
# Sobolev descent in radial and rotation coordinates

The product analytic step of Lemma 3.9. The actual periodic smooth core
supplies the circle derivatives and radial smooth slices. The limiting graph is sliced
almost everywhere, rather than evaluated at a fixed rotation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff InnerProductSpace

namespace Riesz1

variable {M : ℕ+}
variable (basis : OrthonormalBasis (Fin (Module.finrank ℝ (hsOrthSubspace M))) ℝ
  (hsOrthSubspace M))

/-- A smooth periodic test restricted to a circle slice of the existing supported product
extension. Its value is zero off the radial domain, as is that extension. -/
def blockProductCircleTest (f : hsSmoothCore M)
    (q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace M)))) :
    CircleC1Function (Real.sqrt (M : ℕ)) :=
  ⟨fun w => scalarPoincareProductExtension basis f.val (q, w), by
    by_cases hq : q ∈ scalarPoincareRadialDomain basis
    · have he : (fun t : ℝ => scalarPoincareProductExtension basis f.val
          (q, (t : AddCircle (Real.sqrt (M : ℕ))))) =
          (fun t : ℝ => f.val (scalarPoincareRadialEmbedding basis q + t • hsUnitVector M)) := by
        funext t
        rw [scalarPoincareProductExtension_of_mem basis f.val hq,
          scalarPoincareProductLift_coe basis f.val f.property.1]
      rw [he]
      exact (scalarPoincare_circleSlice_smooth basis f.property hq).of_le (by norm_num)
    · have he : (fun t : ℝ => scalarPoincareProductExtension basis f.val
          (q, (t : AddCircle (Real.sqrt (M : ℕ))))) = (fun _ : ℝ => (0 : ℝ)) := by
        funext t
        exact indicator_of_notMem (by simpa using hq) _
      rw [he]
      exact contDiff_const⟩

/-- The circle derivative of the slice is the unit common-rotation derivative. -/
theorem blockProductCircleTest_derivative (f : hsSmoothCore M)
    (q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace M))))
    (w : AddCircle (Real.sqrt (M : ℕ))) :
    circleLiftDerivative _ (blockProductCircleTest basis f q) w =
      inner ℝ (scalarPoincareProductExtension basis (gradient f.val) (q, w)) (hsUnitVector M) := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective w
  rw [circleLiftDerivative_coe]
  by_cases hq : q ∈ scalarPoincareRadialDomain basis
  · have he : (fun s : ℝ => (blockProductCircleTest basis f q).val
        (s : AddCircle (Real.sqrt (M : ℕ)))) =
        (fun s : ℝ => f.val (scalarPoincareRadialEmbedding basis q + s • hsUnitVector M)) := by
      funext s
      exact (scalarPoincareProductExtension_of_mem basis f.val hq _).trans
        (scalarPoincareProductLift_coe basis f.val f.property.1 q s)
    rw [he, scalarPoincare_circleSlice_deriv basis f.property hq,
      scalarPoincareProductExtension_of_mem basis (gradient f.val) hq,
      scalarPoincareProductLift_coe basis (gradient f.val)
        (scalarPoincare_gradient_translate f.property)]
  · have he : (fun s : ℝ => (blockProductCircleTest basis f q).val
        (s : AddCircle (Real.sqrt (M : ℕ)))) = (fun _ : ℝ => (0 : ℝ)) := by
      funext s
      change scalarPoincareProductExtension basis f.val (q, _) = 0
      exact indicator_of_notMem (by simpa using hq) _
    rw [he, deriv_const]
    rw [scalarPoincareProductExtension, indicator_of_notMem (by simpa using hq), inner_zero_left]

/-- Radial gradient coordinates, the orthogonal projection followed by the chosen
orthonormal chart. -/
def blockRadialGradientMap : HsEuclidean M →L[ℝ]
    EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace M))) :=
  (scalarPoincareRadialChart basis).symm.toContinuousLinearMap.comp
    (hsOrthSubspace M).orthogonalProjectionOnto

theorem blockRadialGradientMap_apply (v : HsEuclidean M) :
    blockRadialGradientMap basis v =
      (scalarPoincareRadialChart basis).symm (hsOrthComp M v) := by
  change (scalarPoincareRadialChart basis).symm
    ((hsOrthSubspace M).orthogonalProjectionOnto v) = _
  congr 1
  apply Subtype.ext
  exact (Submodule.coe_orthogonalProjectionOnto_apply _ v).trans
    (orthComponent_eq_starProjection (hsUnitVector_norm M) v).symm

theorem blockRadialGradientMap_norm_le (v : HsEuclidean M) :
    ‖blockRadialGradientMap basis v‖ ≤ ‖v‖ := by
  change ‖(scalarPoincareRadialChart basis).symm
    ((hsOrthSubspace M).orthogonalProjectionOnto v)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (hsOrthSubspace M).norm_orthogonalProjectionOnto_apply_le v

namespace Internal

variable (ν : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace M)))))
  [IsProbabilityMeasure ν]

private theorem product_test_value_memLp (f : hsSmoothCore M) :
    MemLp (scalarPoincareProductExtension basis f.val) 2 (ν.prod AddCircle.haarAddCircle) := by
  obtain ⟨hm, C, hC⟩ := scalarPoincareProductExtension_properties basis f.val
    (f.property.2.choose_spec.2.2.continuousOn.mono f.property.2.choose_spec.2.1)
  exact MemLp.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hC)

private theorem product_test_gradient_memLp (f : hsSmoothCore M) :
    MemLp (scalarPoincareProductExtension basis (gradient f.val)) 2
      (ν.prod AddCircle.haarAddCircle) := by
  obtain ⟨hm, C, hC⟩ := scalarPoincareProductExtension_properties basis (gradient f.val)
    (scalarPoincare_gradient_continuousOn f.property)
  exact MemLp.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hC)

/-- For the actual periodic smooth core, zero weak common-rotation derivative makes
the product representative equal to its rotation average. This is an internal product
statement. It does not assume slice Sobolev membership. -/
theorem block_product_eq_rotation_mean
    {F : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace M))) ×
      AddCircle (Real.sqrt (M : ℕ)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace M))) ×
      AddCircle (Real.sqrt (M : ℕ)) → HsEuclidean M}
    (hFG : WeightedSobolev.IsGraphH1 (ν.prod AddCircle.haarAddCircle)
      (fun _ : hsSmoothCore M => True)
      (fun f => scalarPoincareProductExtension basis f.val)
      (fun f => scalarPoincareProductExtension basis (gradient f.val)) F G)
    (hzero : ∀ᵐ p ∂ν.prod AddCircle.haarAddCircle, inner ℝ (G p) (hsUnitVector M) = 0) :
    F =ᵐ[ν.prod AddCircle.haarAddCircle]
      (fun p => ∫ w, F (p.1, w) ∂AddCircle.haarAddCircle) := by
  let A := innerSL ℝ (hsUnitVector M)
  have hg := hFG.map_derivative (fun f _ => product_test_gradient_memLp basis ν f) A
  have hz : (fun p => A (G p)) =ᵐ[ν.prod AddCircle.haarAddCircle] (fun _ => 0) := by
    filter_upwards [hzero] with p hp
    change inner ℝ (hsUnitVector M) (G p) = 0
    rwa [real_inner_comm]
  have hg' := hg.congr (Eventually.of_forall fun _ => rfl) hz
  have he : (fun f p => circleLiftDerivative _ (blockProductCircleTest basis f p.1) p.2) =
      (fun (f : hsSmoothCore M) p => A
        (scalarPoincareProductExtension basis (gradient f.val) p)) := by
    funext f p
    rw [blockProductCircleTest_derivative]
    exact real_inner_comm _ _
  apply circleProductGraphH1_eq_rotation_mean
    (test := blockProductCircleTest basis)
  · change WeightedSobolev.IsGraphH1 _ _ _ _ F (fun _ => 0)
    rw [he]
    exact hg'
  · exact fun f _ => product_test_value_memLp basis ν f
  · intro f _
    rw [show (fun p => circleLiftDerivative _ (blockProductCircleTest basis f p.1) p.2) =
      (fun p => A (scalarPoincareProductExtension basis (gradient f.val) p)) from congrFun he f]
    exact (product_test_gradient_memLp basis ν f).continuousLinearMap_comp A

/-- Almost every rotation slice of a completed periodic product jet is in the actual
radial weighted Sobolev space, with the projected radial gradient. -/
theorem block_product_ae_radial_slice
    (hν : ∀ᵐ q ∂ν, q ∈ scalarPoincareRadialDomain basis)
    {F : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace M))) ×
      AddCircle (Real.sqrt (M : ℕ)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace M))) ×
      AddCircle (Real.sqrt (M : ℕ)) → HsEuclidean M}
    (hFG : WeightedSobolev.IsGraphH1 (ν.prod AddCircle.haarAddCircle)
      (fun _ : hsSmoothCore M => True)
      (fun f => scalarPoincareProductExtension basis f.val)
      (fun f => scalarPoincareProductExtension basis (gradient f.val)) F G) :
    ∀ᵐ w ∂AddCircle.haarAddCircle,
      WeightedSobolev.IsWeightedH1 ν (scalarPoincareRadialDomain basis)
        (fun q => F (q, w)) (fun q => blockRadialGradientMap basis (G (q, w))) := by
  let R := blockRadialGradientMap basis
  have hv (f : hsSmoothCore M) (_ : True) := product_test_value_memLp basis ν f
  have hg (f : hsSmoothCore M) (_ : True) := product_test_gradient_memLp basis ν f
  have hr (f : hsSmoothCore M) (_ : True) := (hg f trivial).continuousLinearMap_comp R
  have hR := hFG.map_derivative hg R
  have hswap := hR.comp_measurePreserving hv hr Measure.measurePreserving_swap
  have hsl := hswap.ae_slice
    (fun f _ => (hv f trivial).comp_measurePreserving Measure.measurePreserving_swap)
    (fun f _ => (hr f trivial).comp_measurePreserving Measure.measurePreserving_swap)
  filter_upwards [hsl] with w hw
  obtain ⟨hFw, hGw, φ, hφ, hφv, hφg⟩ := hw
  let t : ℝ := AddCircle.equivIoc (Real.sqrt (M : ℕ)) 0 w
  let ψ := fun k q => (φ k).val
    (scalarPoincareRadialEmbedding basis q + t • hsUnitVector M)
  have he (k : ℕ) : (fun q => scalarPoincareProductExtension basis (φ k).val (q, w)) =ᵐ[ν]
      ψ k := hν.mono fun q hq => scalarPoincareProductExtension_of_mem basis (φ k).val hq w
  have hge (k : ℕ) : (fun q => R
      (scalarPoincareProductExtension basis (gradient (φ k).val) (q, w))) =ᵐ[ν]
      gradient (ψ k) := by
    filter_upwards [hν] with q hq
    rw [scalarPoincareProductExtension_of_mem basis (gradient (φ k).val) hq]
    change blockRadialGradientMap basis (gradient (φ k).val
      (scalarPoincareRadialEmbedding basis q + t • hsUnitVector M)) = gradient (ψ k) q
    rw [blockRadialGradientMap_apply, scalarPoincare_radialSlice_gradient basis (φ k).property hq]
  refine ⟨hFw, hGw, ψ, fun k => scalarPoincare_radialSlice_smooth basis (φ k).property t, ?_, ?_⟩
  · convert hφv using 1
    funext k
    apply lintegral_congr_ae
    filter_upwards [he k] with q hq
    change ‖ψ k q - F (q, w)‖ₑ ^ 2 =
      ‖scalarPoincareProductExtension basis (φ k).val (q, w) - F (q, w)‖ₑ ^ 2
    rw [hq]
  · convert hφg using 1
    funext k
    apply lintegral_congr_ae
    filter_upwards [hge k] with q hq
    change ‖gradient (ψ k) q - R (G (q, w))‖ₑ ^ 2 =
      ‖R (scalarPoincareProductExtension basis (gradient (φ k).val) (q, w)) - R (G (q, w))‖ₑ ^ 2
    rw [hq]

/-- A zero-rotation product Sobolev observable has a radial Sobolev representative with
the same essential gradient bound. Both slice membership and the representative are
conclusions. The argument chooses a slice only from a proved full-measure set. -/
theorem block_product_sobolev_descent
    (hν : ∀ᵐ q ∂ν, q ∈ scalarPoincareRadialDomain basis)
    {F : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace M))) ×
      AddCircle (Real.sqrt (M : ℕ)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace M))) ×
      AddCircle (Real.sqrt (M : ℕ)) → HsEuclidean M}
    (hFG : WeightedSobolev.IsGraphH1 (ν.prod AddCircle.haarAddCircle)
      (fun _ : hsSmoothCore M => True)
      (fun f => scalarPoincareProductExtension basis f.val)
      (fun f => scalarPoincareProductExtension basis (gradient f.val)) F G)
    (hzero : ∀ᵐ p ∂ν.prod AddCircle.haarAddCircle, inner ℝ (G p) (hsUnitVector M) = 0)
    {L : ℝ} (hbound : ∀ᵐ p ∂ν.prod AddCircle.haarAddCircle, ‖G p‖ ≤ L) :
    ∃ f g, WeightedSobolev.IsWeightedH1 ν (scalarPoincareRadialDomain basis) f g ∧
      (∀ᵐ q ∂ν, ‖g q‖ ≤ L) ∧ F =ᵐ[ν.prod AddCircle.haarAddCircle] (fun p => f p.1) := by
  have hm := block_product_eq_rotation_mean basis ν hFG hzero
  have hs := block_product_ae_radial_slice basis ν hν hFG
  have hwmean := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hm)
  have hwbound := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hbound)
  obtain ⟨w, hws, hwm, hwb⟩ := (hs.and (hwmean.and hwbound)).exists
  refine ⟨fun q => F (q, w), fun q => blockRadialGradientMap basis (G (q, w)), hws, ?_, ?_⟩
  · filter_upwards [hwb] with q hq
    exact (blockRadialGradientMap_norm_le basis _).trans hq
  · apply hm.trans
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hwm] with p hp
    exact hp.symm

end Internal

end Riesz1

end
