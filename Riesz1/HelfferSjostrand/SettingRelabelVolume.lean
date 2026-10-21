/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GeometryRelabelAdmissible
public import Riesz1.ToMathlib.Chamber.PeriodizationIntegral

/-!
# Cyclic relabeling and quotient volume

The affine cyclic permutation changes the fundamental strip. Integer-periodic
integrals agree on the two strips, including their seams. This implements the
volume change of variables in the proofs of Lemma 3.6
and Lemma 3.9 for general labelled pair potentials.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace Riesz1

variable {N : ℕ+}

/-- The lift relabeling preserves Euclidean volume. -/
theorem measurePreserving_hsRelabel (N : ℕ+) (k : ℕ) :
    MeasurePreserving (hsRelabel N k) volume volume := by
  have he : hsRelabel N k = fun x => hsCycLinear N k x + hsCycShiftVec N k := by
    funext x
    exact hsRelabel_eq_affine N k x
  rw [he]
  exact (measurePreserving_add_right volume _).comp (hsCycLinear N k).measurePreserving

/-- Relabel a configuration and take its unique fundamental representative. -/
def hsRelabelConfiguration (N : ℕ+) (k : ℕ) (X : Configuration N) : Configuration N :=
  hsRepresentative ⟨hsRelabel N k (WithLp.toLp 2 X.val),
    hsRelabel_mem_chamber N k ⟨X.property.1, X.property.2.2.2⟩⟩

theorem measurable_hsRepresentative (N : ℕ+) :
    Measurable (hsRepresentative (N := N)) := by
  have he : hsRepresentative (N := N) = fun x : hsChamber N =>
      (hsConfigurationEquiv N).symm
        ⟨QuotientAddGroup.mk x.val, ⟨x.val, x.property, rfl⟩⟩ := by
    funext x
    apply (hsConfigurationEquiv N).injective
    apply Subtype.ext
    rw [Equiv.apply_symm_apply]
    exact hsConfigurationMap_representative x
  rw [he]
  apply (measurable_hsConfigurationEquiv_symm N).comp
  exact (QuotientAddGroup.measurable_coe.comp measurable_subtype_coe).subtype_mk

theorem measurable_hsRelabelConfiguration (N : ℕ+) (k : ℕ) :
    Measurable (hsRelabelConfiguration N k) := by
  apply (measurable_hsRepresentative N).comp
  exact ((measurePreserving_hsRelabel N k).measurable.comp
    ((PiLp.volume_preserving_toLp (Fin (N : ℕ))).measurable.comp
      measurable_subtype_coe)).subtype_mk

/-- Integer translation does not change the fundamental representative. -/
theorem hsRepresentative_translate_int (x : hsChamber N) (j : ℤ) :
    hsRepresentative ⟨hsTranslate (j : ℝ) x.val,
      (hsTranslate_mem_chamber_iff _ _).mpr x.property⟩ = hsRepresentative x := by
  apply (hsConfigurationEquiv N).injective
  apply Subtype.ext
  change (hsConfigurationMap N (hsRepresentative _)).val =
    (hsConfigurationMap N (hsRepresentative _)).val
  rw [hsConfigurationMap_representative, hsConfigurationMap_representative]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  apply (hsPeriodLattice_mem_iff _).mpr
  exact ⟨j, fun i => by simp [hsTranslate_apply]⟩

/-- Reducing a point already in the fundamental region does nothing. -/
theorem hsRepresentative_configuration (X : Configuration N) :
    hsRepresentative ⟨WithLp.toLp 2 X.val, ⟨X.property.1, X.property.2.2.2⟩⟩ = X := by
  apply (hsConfigurationEquiv N).injective
  apply Subtype.ext
  exact hsConfigurationMap_representative _

/-- A periodic nonnegative function has the same integral after cyclic relabeling.
The function is supported on the chamber. No integrability premise is needed. -/
theorem lintegral_hsRelabel_periodic (N : ℕ+) (k : ℕ)
    {f : HsEuclidean N → ℝ≥0∞} (hf : Measurable f)
    (hper : ∀ (j : ℤ) x, f (hsTranslate (j : ℝ) x) = f x)
    (hsupp : ∀ x ∉ hsChamber N, f x = 0) :
    ∫⁻ x in hsFundamentalRegion N, f (hsRelabel N k x) =
      ∫⁻ x in hsFundamentalRegion N, f x := by
  let S := (EuclideanSpace.proj (⟨0, N.pos⟩ : Fin (N : ℕ))) ⁻¹' Ico (0 : ℝ) 1
  have hv : hsRotationVector N ≠ 0 := by
    intro h
    have := congrArg (fun x : HsEuclidean N => x ⟨0, N.pos⟩) h
    simp [hsRotationVector] at this
  have hS := isAddFundamentalDomain_vectorStrip hv
    (EuclideanSpace.proj (⟨0, N.pos⟩ : Fin (N : ℕ))) (by simp [hsRotationVector])
    (volume : Measure (HsEuclidean N))
  have hT := hS.preimage_of_equiv (measurePreserving_hsRelabel N k).quasiMeasurePreserving
    (Function.bijective_id : Function.Bijective (id : hsPeriodLattice N → hsPeriodLattice N))
    (fun g x => by
      obtain ⟨j, hj⟩ := (hsPeriodLattice_mem_iff g.val).mp g.property
      change hsRelabel N k (g.val + x) = g.val + hsRelabel N k x
      have ha (y : HsEuclidean N) : g.val + y = hsTranslate (j : ℝ) y := by
        ext i
        change g.val i + y i = y i + (j : ℝ)
        rw [hj i, add_comm]
      rw [ha, ha, hsRelabel_translate])
  have hperiod : ∀ (g : hsPeriodLattice N) x,
      f (hsRelabel N k (g +ᵥ x)) = f (hsRelabel N k x) := by
    intro g x
    obtain ⟨j, hj⟩ := (hsPeriodLattice_mem_iff g.val).mp g.property
    have he : g +ᵥ x = hsTranslate (j : ℝ) x := by
      ext i
      change g.val i + x i = x i + (j : ℝ)
      rw [hj i, add_comm]
    rw [he, hsRelabel_translate, hper]
  have hint := hS.setLIntegral_eq hT (fun x => f (hsRelabel N k x)) hperiod
  have hSm : MeasurableSet S := by
    exact measurableSet_Ico.preimage (PiLp.continuous_apply 2 (fun _ : Fin (N : ℕ) => ℝ)
      (⟨0, N.pos⟩ : Fin (N : ℕ))).measurable
  have hchange := ((measurePreserving_hsRelabel N k).restrict_preimage hSm).lintegral_comp hf
  have hF : hsFundamentalRegion N = hsChamber N ∩ S := by
    ext x
    simp only [hsFundamentalRegion, mem_ofPred_eq, mem_inter_iff, S, mem_preimage, mem_Ico]
    tauto
  have hleft : ∫⁻ x in S, f (hsRelabel N k x) =
      ∫⁻ x in hsFundamentalRegion N, f (hsRelabel N k x) := by
    rw [hF, ← Measure.restrict_restrict (isOpen_hsChamber N).measurableSet,
      ← lintegral_indicator (isOpen_hsChamber N).measurableSet]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ hsChamber N
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hsupp]
      intro h
      obtain ⟨y, hy, he⟩ := hsRelabel_exists_preimage N k h
      exact hx ((isometry_hsRelabel N k).injective he ▸ hy)
  have hright : ∫⁻ x in S, f x = ∫⁻ x in hsFundamentalRegion N, f x := by
    rw [hF, ← Measure.restrict_restrict (isOpen_hsChamber N).measurableSet,
      ← lintegral_indicator (isOpen_hsChamber N).measurableSet]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ hsChamber N
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hsupp x hx]
  rw [← hleft, hint, hchange, hright]

/-- Euclidean fundamental-region integration, with an ambient Euclidean test. -/
theorem lintegral_hsFundamentalRegion_euclidean {f : HsEuclidean N → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x in hsFundamentalRegion N, f x =
      ∫⁻ X : Configuration N, f (WithLp.toLp 2 X.val) ∂configurationVolume N := by
  simpa only [WithLp.toLp_ofLp] using hsFundamentalRegion_lintegral N
    (fun x => f (WithLp.toLp 2 x))
    (hf.comp (PiLp.volume_preserving_toLp (Fin (N : ℕ))).measurable)

/-- Cyclic relabeling preserves the quotient volume written in fundamental representatives. -/
theorem lintegral_hsRelabelConfiguration (N : ℕ+) (k : ℕ)
    {f : Configuration N → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ X, f (hsRelabelConfiguration N k X) ∂configurationVolume N =
      ∫⁻ X, f X ∂configurationVolume N := by
  let g : HsEuclidean N → ℝ≥0∞ :=
    Function.extend Subtype.val (fun x : hsChamber N => f (hsRepresentative x)) (fun _ => 0)
  have hg : Measurable g := (MeasurableEmbedding.subtype_coe
    (isOpen_hsChamber N).measurableSet).measurable_extend
      (hf.comp (measurable_hsRepresentative N)) measurable_const
  have hmem (x : hsChamber N) : g x.val = f (hsRepresentative x) :=
    Subtype.val_injective.extend_apply _ _ x
  have hnot (x : HsEuclidean N) (hx : x ∉ hsChamber N) : g x = 0 :=
    Function.extend_apply' _ _ _ (by rintro ⟨y, rfl⟩; exact hx y.property)
  have hper (j : ℤ) (x : HsEuclidean N) : g (hsTranslate (j : ℝ) x) = g x := by
    by_cases hx : x ∈ hsChamber N
    · rw [hmem ⟨hsTranslate (j : ℝ) x, (hsTranslate_mem_chamber_iff _ _).mpr hx⟩,
        hmem ⟨x, hx⟩]
      exact congrArg f (hsRepresentative_translate_int ⟨x, hx⟩ j)
    · rw [hnot x hx, hnot _ (by simpa only [hsTranslate_mem_chamber_iff] using hx)]
  have he := lintegral_hsRelabel_periodic N k hg hper hnot
  change (∫⁻ x in hsFundamentalRegion N, (g ∘ hsRelabel N k) x) = _ at he
  rw [lintegral_hsFundamentalRegion_euclidean
      (hg.comp (measurePreserving_hsRelabel N k).measurable),
    lintegral_hsFundamentalRegion_euclidean hg] at he
  have ha (X : Configuration N) : g (hsRelabel N k (WithLp.toLp 2 X.val)) =
      f (hsRelabelConfiguration N k X) :=
    hmem ⟨_, hsRelabel_mem_chamber N k ⟨X.property.1, X.property.2.2.2⟩⟩
  have hb (X : Configuration N) : g (WithLp.toLp 2 X.val) = f X := by
    rw [hmem ⟨_, ⟨X.property.1, X.property.2.2.2⟩⟩, hsRepresentative_configuration]
  simpa only [Function.comp_def, ha, hb] using he

/-- The seam-aware cyclic relabeling is measure preserving on configurations. -/
theorem measurePreserving_hsRelabelConfiguration (N : ℕ+) (k : ℕ) :
    MeasurePreserving (hsRelabelConfiguration N k) (configurationVolume N)
      (configurationVolume N) := by
  refine ⟨measurable_hsRelabelConfiguration N k, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_hsRelabelConfiguration N k)]
  exact lintegral_hsRelabelConfiguration N k hf

end Riesz1

end
