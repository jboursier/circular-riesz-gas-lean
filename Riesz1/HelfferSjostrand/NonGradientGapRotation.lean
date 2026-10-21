/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.NonGradient
public import Riesz1.HelfferSjostrand.RadialDomainGaps
public import Riesz1.HelfferSjostrand.GeometryLawBijection
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Common rotations for the non-gradient equation

The rotations in the proof of Proposition 3.2 act on
the existing configuration carrier. The product law proves preservation
of the general pair-potential Gibbs probability.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set InnerProductSpace

namespace Riesz1

variable {N : ℕ+}

/-- The unique fundamental representative of a commonly translated configuration. -/
def hsGapRotateConfiguration (t : ℝ) (X : Configuration N) : Configuration N :=
  hsRepresentative ⟨hsTranslate t (WithLp.toLp 2 X.val),
    (hsTranslate_mem_chamber_iff t _).mpr ⟨X.property.1, X.property.2.2.2⟩⟩

theorem hsGapRotateConfiguration_lift (t : ℝ) (X : Configuration N) :
    WithLp.toLp 2 (hsGapRotateConfiguration t X).val =
      hsTranslate (t - ⌊X.val ⟨0, N.pos⟩ + t⌋) (WithLp.toLp 2 X.val) := by
  ext i
  simp only [hsGapRotateConfiguration, hsRepresentative_apply, hsTranslate_apply]
  ring

theorem measurable_hsGapRotateConfiguration :
    Measurable (fun p : ℝ × Configuration N => hsGapRotateConfiguration p.1 p.2) := by
  apply Measurable.subtype_mk
  apply measurable_pi_iff.mpr
  intro i
  change Measurable (fun p : ℝ × Configuration N =>
    (p.2.val i + p.1) - (⌊p.2.val ⟨0, N.pos⟩ + p.1⌋ : ℝ))
  have h0 : Measurable (fun p : ℝ × Configuration N => p.2.val ⟨0, N.pos⟩ + p.1) :=
    ((measurable_pi_apply (⟨0, N.pos⟩ : Fin (N : ℕ))).comp
      (measurable_subtype_coe.comp measurable_snd)).add measurable_fst
  have hfloor : Measurable (fun p : ℝ × Configuration N =>
      (⌊p.2.val ⟨0, N.pos⟩ + p.1⌋ : ℝ)) :=
    (measurable_of_countable (fun k : ℤ => (k : ℝ))).comp h0.floor
  have hi : Measurable (fun p : ℝ × Configuration N => p.2.val i + p.1) :=
    ((measurable_pi_apply i).comp (measurable_subtype_coe.comp measurable_snd)).add measurable_fst
  exact hi.sub hfloor

theorem hsGap_coord_translate (t : ℝ) (x : HsEuclidean N) :
    hsCoord N (hsTranslate t x) =
      ((hsCoord N x).1, (hsCoord N x).2 + (t * Real.sqrt (N : ℕ) : ℝ)) := by
  have hT : Real.sqrt (N : ℕ) ≠ 0 := (sqrt_N_pos N).ne'
  have ht : hsTranslate t x = x + (t * Real.sqrt (N : ℕ)) • hsUnitVector N := by
    ext i
    simp only [hsTranslate_apply, PiLp.add_apply, PiLp.smul_apply, hsUnitVector,
      hsRotationVector, smul_eq_mul]
    field_simp
  have hi : inner ℝ (hsTranslate t x) (hsUnitVector N) =
      inner ℝ x (hsUnitVector N) + t * Real.sqrt (N : ℕ) := by
    rw [ht, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      hsUnitVector_norm, one_pow, mul_one]
  apply Prod.ext
  · apply Subtype.ext
    change (hsOrthComp N (hsTranslate t x) : HsEuclidean N) = (hsOrthComp N x : HsEuclidean N)
    rw [hsOrthComp_coe, hi, ht, hsOrthComp_coe, add_smul]
    abel
  · change ((inner ℝ (hsTranslate t x) (hsUnitVector N) : ℝ) : AddCircle (Real.sqrt (N : ℕ))) = _
    rw [hi, QuotientAddGroup.mk_add]
    rfl

theorem hsGap_coord_representative (x : hsChamber N) :
    hsConfigCoord N (hsRepresentative x) = hsCoord N x.val := by
  have he : WithLp.toLp 2 (hsRepresentative x).val =
      hsTranslate (-(⌊x.val ⟨0, N.pos⟩⌋ : ℝ)) x.val := by
    ext i
    simp only [hsRepresentative_apply, hsTranslate_apply]
    ring
  change hsCoord N (WithLp.toLp 2 (hsRepresentative x).val) = _
  rw [he, hsGap_coord_translate]
  have hz : (((-(⌊x.val ⟨0, N.pos⟩⌋ : ℝ)) * Real.sqrt (N : ℕ) : ℝ) :
      AddCircle (Real.sqrt (N : ℕ))) = 0 := by
    apply (AddCircle.coe_eq_zero_iff _).mpr
    exact ⟨-⌊x.val ⟨0, N.pos⟩⌋, by simp only [zsmul_eq_mul, Int.cast_neg]⟩
  rw [hz, add_zero]

theorem hsGapRotateConfiguration_coord (t : ℝ) (X : Configuration N) :
    hsConfigCoord N (hsGapRotateConfiguration t X) =
      ((hsConfigCoord N X).1, (hsConfigCoord N X).2 + (t * Real.sqrt (N : ℕ) : ℝ)) := by
  rw [hsGapRotateConfiguration, hsGap_coord_representative, hsGap_coord_translate]
  rfl

theorem measurableEmbedding_hsGapConfigCoord (N : ℕ+) :
    MeasurableEmbedding (hsConfigCoord N) := by
  let : StandardBorelSpace (Configuration N) := (measurableSet_orderedDomain N).standardBorel
  exact (measurable_hsConfigCoord N).measurableEmbedding
    (fun X Y h => (hsConfigCoord_bijOn N).injOn (mem_univ X) (mem_univ Y) h)

/-- Common rotations preserve the Gibbs law for every pair family. -/
theorem measurePreserving_hsGapRotateConfiguration {c : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c) (t : ℝ) :
    MeasurePreserving (hsGapRotateConfiguration (N := N) t)
      (hsGibbsProbability χ hc : Measure (Configuration N)) (hsGibbsProbability χ hc : Measure (Configuration N)) := by
  have hm : Measurable (hsGapRotateConfiguration (N := N) t) :=
    (measurable_hsGapRotateConfiguration (N := N)).comp
      (show Measurable (fun x : Configuration N => (t, x)) from measurable_const.prodMk measurable_id)
  refine ⟨hm, (measurableEmbedding_hsGapConfigCoord N).map_injective ?_⟩
  rw [Measure.map_map (measurable_hsConfigCoord N) hm]
  have he : hsConfigCoord N ∘ hsGapRotateConfiguration t =
      (fun p : hsOrthSubspace N × AddCircle (Real.sqrt (N : ℕ)) =>
        (p.1, p.2 + ((t * Real.sqrt (N : ℕ) : ℝ) : AddCircle (Real.sqrt (N : ℕ))))) ∘ hsConfigCoord N :=
    funext (hsGapRotateConfiguration_coord t)
  have hshift : Measurable (fun p : hsOrthSubspace N × AddCircle (Real.sqrt (N : ℕ)) =>
      (p.1, p.2 + ((t * Real.sqrt (N : ℕ) : ℝ) : AddCircle (Real.sqrt (N : ℕ))))) :=
    measurable_fst.prodMk (measurable_snd.add measurable_const)
  rw [he, ← Measure.map_map hshift (measurable_hsConfigCoord N), hsGibbs_map_hsConfigCoord]
  have hp : MeasurePreserving
      (fun p : hsOrthSubspace N × AddCircle (Real.sqrt (N : ℕ)) =>
        (p.1, p.2 + ((t * Real.sqrt (N : ℕ) : ℝ) : AddCircle (Real.sqrt (N : ℕ)))))
      ((hsRadialProbability χ hc : Measure _).prod (hsUniformCircle N : Measure _))
      ((hsRadialProbability χ hc : Measure _).prod (hsUniformCircle N : Measure _)) := by
    have hr : MeasurePreserving
        (fun w : AddCircle (Real.sqrt (N : ℕ)) =>
          w + (((t * Real.sqrt (N : ℕ)) : ℝ) : AddCircle (Real.sqrt (N : ℕ))))
        (hsUniformCircle N : Measure _) (hsUniformCircle N : Measure _) := by
      change MeasurePreserving _ AddCircle.haarAddCircle AddCircle.haarAddCircle
      exact measurePreserving_add_right _ _
    exact (MeasurePreserving.id (hsRadialProbability χ hc : Measure (hsOrthSubspace N))).prod hr
  exact hp.map_eq

/-- Common rotation on the existing cyclic quotient. -/
def hsGapRotate (t : ℝ) (x : HsConfiguration N) : HsConfiguration N :=
  hsConfigurationMap N (hsGapRotateConfiguration t ((hsConfigurationEquiv N).symm x))

theorem measurable_hsGapRotate :
    Measurable (fun p : ℝ × HsConfiguration N => hsGapRotate p.1 p.2) :=
  (measurable_hsConfigurationMap N).comp
    (measurable_hsGapRotateConfiguration.comp
      (measurable_fst.prodMk ((measurable_hsConfigurationEquiv_symm N).comp measurable_snd)))

theorem hsGapRotate_lift (t : ℝ) (x : HsConfiguration N) :
    hsLiftPoint N (hsGapRotate t x) =
      hsTranslate (t - ⌊hsLiftPoint N x ⟨0, N.pos⟩ + t⌋) (hsLiftPoint N x) := by
  change WithLp.toLp 2 ((hsConfigurationEquiv N).symm
    ((hsConfigurationEquiv N) (hsGapRotateConfiguration t ((hsConfigurationEquiv N).symm x)))).val = _
  rw [Equiv.symm_apply_apply, hsGapRotateConfiguration_lift]
  rfl

theorem hsGapRotate_gap (t : ℝ) (x : HsConfiguration N) :
    hsGap (hsLiftPoint N (hsGapRotate t x)) = hsGap (hsLiftPoint N x) := by
  rw [hsGapRotate_lift, hsGap_translate]

theorem measurePreserving_hsGapRotate {c : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c) (t : ℝ) :
    MeasurePreserving (hsGapRotate (N := N) t)
      (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
  have hm : Measurable (hsGapRotate (N := N) t) := by
    exact (measurable_hsConfigurationMap N).comp
      (((measurable_hsGapRotateConfiguration (N := N)).comp
        (measurable_const.prodMk measurable_id)).comp (measurable_hsConfigurationEquiv_symm N))
  refine ⟨hm, ?_⟩
  rw [hsQuotientGibbsProbability_eq_map,
    Measure.map_map hm (measurable_hsConfigurationMap N)]
  have he : hsGapRotate t ∘ hsConfigurationMap N =
      hsConfigurationMap N ∘ hsGapRotateConfiguration t := by
    funext X
    change hsConfigurationMap N (hsGapRotateConfiguration t
      ((hsConfigurationEquiv N).symm ((hsConfigurationEquiv N) X))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [he, ← Measure.map_map (measurable_hsConfigurationMap N)
    (measurePreserving_hsGapRotateConfiguration χ hc t).measurable,
    (measurePreserving_hsGapRotateConfiguration χ hc t).map_eq]

theorem hsGapRotateConfiguration_add (t s : ℝ) (X : Configuration N) :
    hsGapRotateConfiguration t (hsGapRotateConfiguration s X) =
      hsGapRotateConfiguration (t + s) X := by
  apply (measurableEmbedding_hsGapConfigCoord N).injective
  simp only [hsGapRotateConfiguration_coord]
  refine Prod.ext rfl ?_
  change (hsConfigCoord N X).2 + ((s * Real.sqrt (N : ℕ) : ℝ) : AddCircle _) +
    ((t * Real.sqrt (N : ℕ) : ℝ) : AddCircle _) = _
  rw [add_mul, QuotientAddGroup.mk_add]
  ac_rfl

theorem hsGapRotateConfiguration_zero (X : Configuration N) :
    hsGapRotateConfiguration 0 X = X := by
  apply (measurableEmbedding_hsGapConfigCoord N).injective
  simp only [hsGapRotateConfiguration_coord, zero_mul, QuotientAddGroup.mk_zero, add_zero]

theorem hsGapRotate_add (t s : ℝ) (x : HsConfiguration N) :
    hsGapRotate t (hsGapRotate s x) = hsGapRotate (t + s) x := by
  change hsConfigurationMap N (hsGapRotateConfiguration t
    ((hsConfigurationEquiv N).symm ((hsConfigurationEquiv N)
      (hsGapRotateConfiguration s ((hsConfigurationEquiv N).symm x))))) = _
  rw [Equiv.symm_apply_apply, hsGapRotateConfiguration_add]
  rfl

theorem hsGapRotate_zero (x : HsConfiguration N) : hsGapRotate 0 x = x := by
  change (hsConfigurationEquiv N) (hsGapRotateConfiguration 0 ((hsConfigurationEquiv N).symm x)) = x
  rw [hsGapRotateConfiguration_zero, Equiv.apply_symm_apply]

end Riesz1
