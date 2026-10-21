/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.NonGradientGapRotation
public import Riesz1.HelfferSjostrand.SettingRelabelVolume
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Gap factorization of almost everywhere invariant fields

The pointwise rotation/gap equivalence applies to an invariant
representative. Periodic averaging supplies that representative from
almost everywhere invariance under each rotation. No common null set
over the uncountable family of rotations is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

variable {N : ℕ+}

theorem continuous_hsGapTranslate :
    Continuous (fun p : HsEuclidean N × ℝ => hsTranslate p.2 p.1) :=
  (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
      continuous_fst).add continuous_snd)

namespace Internal

/-- The measurable, almost everywhere version of the pointwise
rotation/gap equivalence. -/
theorem hsGap_factorization_of_bounded_ae_rotation
    (μ : Measure (HsConfiguration N)) [SFinite μ]
    (f : HsConfiguration N → ℝ) (hf : Measurable f)
    (hinv : ∀ t : ℝ, (fun x => f (hsGapRotate t x)) =ᵐ[μ] f)
    (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    ∃ g : (Fin (N : ℕ) → ℝ) → ℝ, Measurable g ∧
      f =ᵐ[μ] fun x => g (hsGap (hsLiftPoint N x)) := by
  let q : HsEuclidean N → ℝ := Function.extend Subtype.val
    (fun x : hsChamber N => f (hsConfigurationMap N (hsRepresentative x))) (fun _ => 0)
  have hq : Measurable q := (MeasurableEmbedding.subtype_coe
    (isOpen_hsChamber N).measurableSet).measurable_extend
      (hf.comp ((measurable_hsConfigurationMap N).comp (measurable_hsRepresentative N)))
      measurable_const
  have hmem (x : hsChamber N) :
      q x.val = f (hsConfigurationMap N (hsRepresentative x)) :=
    Subtype.val_injective.extend_apply _ _ x
  have hnot (x : HsEuclidean N) (hx : x ∉ hsChamber N) : q x = 0 :=
    Function.extend_apply' _ _ _ (by rintro ⟨y, rfl⟩; exact hx y.property)
  have hqb (y : HsEuclidean N) : ‖q y‖ ≤ max C 0 := by
    by_cases hy : y ∈ hsChamber N
    · rw [hmem ⟨y, hy⟩]
      exact (hb _).trans (le_max_left C 0)
    · rw [hnot y hy, norm_zero]
      exact le_max_right C 0
  have hOrbit (y : HsEuclidean N) :
      Integrable (fun t => q (hsTranslate t y)) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have hm : Measurable (fun t : ℝ => q (hsTranslate t y)) :=
      hq.comp (continuous_hsGapTranslate.measurable.comp (measurable_const.prodMk measurable_id))
    exact ⟨hm.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun t => hqb (hsTranslate t y))⟩
  have hper (j : ℤ) (x : HsEuclidean N) : q (hsTranslate (j : ℝ) x) = q x := by
    by_cases hx : x ∈ hsChamber N
    · rw [hmem ⟨hsTranslate (j : ℝ) x, (hsTranslate_mem_chamber_iff _ _).mpr hx⟩,
        hmem ⟨x, hx⟩]
      exact congrArg (fun X => f (hsConfigurationMap N X))
        (hsRepresentative_translate_int (⟨x, hx⟩ : hsChamber N) j)
    · rw [hnot x hx, hnot _ (by simpa only [hsTranslate_mem_chamber_iff] using hx)]
  have hval (t : ℝ) (x : HsConfiguration N) :
      q (hsTranslate t (hsLiftPoint N x)) = f (hsGapRotate t x) := by
    rw [hmem ⟨_, (hsTranslate_mem_chamber_iff _ _).mpr (hsLiftPoint_mem_chamber N x)⟩]
    rfl
  let A : HsEuclidean N → ℝ := fun y => ∫ t in (0 : ℝ)..1, q (hsTranslate t y)
  have hAm : Measurable A := by
    have hqm : StronglyMeasurable (fun p : HsEuclidean N × ℝ => q (hsTranslate p.2 p.1)) :=
      (hq.comp continuous_hsGapTranslate.measurable).stronglyMeasurable
    have hm := hqm.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))
    simpa only [A, intervalIntegral.integral_of_le zero_le_one] using hm.measurable
  have hAi (y : HsEuclidean N) (s : ℝ) : A (hsTranslate s y) = A y := by
    have hp : Function.Periodic (fun t : ℝ => q (hsTranslate t y)) 1 := by
      intro t
      change q (hsTranslate (t + 1) y) = q (hsTranslate t y)
      rw [add_comm t 1, ← hsTranslate_add]
      simpa only [Int.cast_one] using hper 1 (hsTranslate t y)
    change (∫ t in (0 : ℝ)..1, q (hsTranslate t (hsTranslate s y))) = _
    simp_rw [hsTranslate_add]
    rw [intervalIntegral.integral_comp_add_right (fun t => q (hsTranslate t y)) s]
    simpa only [zero_add, add_comm s 1] using hp.intervalIntegral_add_eq s 0
  have hAeq : (fun x => A (hsLiftPoint N x)) =ᵐ[μ] f := by
    have hm : Measurable (fun p : HsConfiguration N × ℝ =>
        q (hsTranslate p.2 (hsLiftPoint N p.1))) :=
      hq.comp (continuous_hsGapTranslate.measurable.comp
        (((measurable_hsLiftPoint N).comp measurable_fst).prodMk measurable_snd))
    have hmeq : MeasurableSet {p : HsConfiguration N × ℝ |
        q (hsTranslate p.2 (hsLiftPoint N p.1)) = f p.1} :=
      measurableSet_eq_fun hm (hf.comp measurable_fst)
    have hte : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ᵐ x ∂μ,
        q (hsTranslate t (hsLiftPoint N x)) = f x :=
      Filter.Eventually.of_forall fun t => (hinv t).mono fun x hx => (hval t x).trans hx
    have he : ∀ᵐ x ∂μ, ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
        q (hsTranslate t (hsLiftPoint N x)) = f x :=
      (Measure.ae_ae_comm (μ := μ) (ν := volume.restrict (Ioc (0 : ℝ) 1))
        (p := fun x t => q (hsTranslate t (hsLiftPoint N x)) = f x) hmeq).mpr hte
    filter_upwards [he] with x hx
    change (∫ t in (0 : ℝ)..1, q (hsTranslate t (hsLiftPoint N x))) = f x
    rw [intervalIntegral.integral_of_le zero_le_one, integral_congr_ae hx]
    simp
  obtain ⟨g, hgm, hg⟩ := (exists_gapFunction_iff_rotation_invariant A
    (hAm.indicator (isOpen_hsChamber N).measurableSet)).mpr
      (fun x _ t => hAi x t)
  exact ⟨g, hgm, hAeq.symm.trans (Filter.Eventually.of_forall fun x =>
    hg (hsLiftPoint N x) (hsLiftPoint_mem_chamber N x))⟩

/-- Bounded injective transformation makes every orbit integral finite,
including orbits in exceptional null fibers. -/
theorem hsGap_factorization_of_ae_rotation
    (μ : Measure (HsConfiguration N)) [SFinite μ]
    (f : HsConfiguration N → ℝ) (hf : Measurable f)
    (hinv : ∀ t : ℝ, (fun x => f (hsGapRotate t x)) =ᵐ[μ] f) :
    ∃ g : (Fin (N : ℕ) → ℝ) → ℝ, Measurable g ∧
      f =ᵐ[μ] fun x => g (hsGap (hsLiftPoint N x)) := by
  have hb (x : HsConfiguration N) : ‖Real.arctan (f x)‖ ≤ Real.pi / 2 := by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  have hi (t : ℝ) : (fun x => Real.arctan (f (hsGapRotate t x))) =ᵐ[μ]
      fun x => Real.arctan (f x) := (hinv t).mono fun _ hx => congrArg Real.arctan hx
  obtain ⟨g, hgm, hg⟩ := hsGap_factorization_of_bounded_ae_rotation μ
    (fun x => Real.arctan (f x)) (Real.continuous_arctan.measurable.comp hf)
    hi (Real.pi / 2) hb
  have htan : Measurable Real.tan := by
    have he : Real.tan = (fun x => Real.sin x / Real.cos x) :=
      funext Real.tan_eq_sin_div_cos
    rw [he]
    exact Real.continuous_sin.measurable.div Real.continuous_cos.measurable
  refine ⟨fun a => Real.tan (g a), htan.comp hgm, ?_⟩
  filter_upwards [hg] with x hx
  rw [← hx, Real.tan_arctan]

end Internal

/-- An `L²` class is a measurable function of the gap map exactly
when each common rotation fixes it almost everywhere. -/
theorem hsLp_gap_factorization_iff_rotation {c : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    (∃ g : (Fin (N : ℕ) → ℝ) → ℝ, Measurable g ∧
      (f : HsConfiguration N → ℝ) =ᵐ[(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))]
        fun x => g (hsGap (hsLiftPoint N x))) ↔
      ∀ t : ℝ, (fun x => f (hsGapRotate t x)) =ᵐ[(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))] f := by
  constructor
  · rintro ⟨g, -, hg⟩ t
    have ht := (measurePreserving_hsGapRotate χ hc t).quasiMeasurePreserving.ae hg
    filter_upwards [hg, ht] with x hx htx
    exact htx.trans ((congrArg g (hsGapRotate_gap t x)).trans hx.symm)
  · exact Internal.hsGap_factorization_of_ae_rotation _ f (Lp.stronglyMeasurable f).measurable

end Riesz1
