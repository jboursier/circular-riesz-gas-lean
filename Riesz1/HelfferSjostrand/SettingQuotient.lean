/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SettingGeometry
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The fundamental region and the cyclic quotient

The quotient forgets only simultaneous integer translations. In particular,
this equivalence introduces neither a factorial nor a quotient by permutations.
The volume is the push-forward of Lebesgue volume on the fundamental
region.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology ENNReal

namespace Riesz1

theorem hsPeriodLattice_mem_iff {N : ℕ+} (v : HsEuclidean N) :
    v ∈ hsPeriodLattice N ↔ ∃ k : ℤ, ∀ i, v i = (k : ℝ) := by
  constructor
  · intro hv
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hv
    exact ⟨k, fun i => by simp [hsRotationVector]⟩
  · rintro ⟨k, hk⟩
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨k, ?_⟩
    ext i
    simp [hsRotationVector, hk i]

/-- Projection of the unique representative into the quotient chamber. -/
def hsConfigurationMap (N : ℕ+) (X : Configuration N) : HsConfiguration N :=
  ⟨QuotientAddGroup.mk (WithLp.toLp 2 X.val),
    ⟨WithLp.toLp 2 X.val, ⟨X.property.1, X.property.2.2.2⟩, rfl⟩⟩

theorem hsConfigurationMap_injective (N : ℕ+) :
    Function.Injective (hsConfigurationMap N) := by
  intro X Y h
  have hq := congrArg Subtype.val h
  change (QuotientAddGroup.mk (WithLp.toLp 2 X.val) : HsCylinder N) =
    QuotientAddGroup.mk (WithLp.toLp 2 Y.val) at hq
  obtain ⟨k, hk⟩ := (hsPeriodLattice_mem_iff _).mp
    (QuotientAddGroup.eq_iff_sub_mem.mp hq)
  have h0 := hk ⟨0, N.pos⟩
  change X.val ⟨0, N.pos⟩ - Y.val ⟨0, N.pos⟩ = (k : ℝ) at h0
  have hkl : (-1 : ℝ) < (k : ℝ) := by linarith [X.property.2.1, Y.property.2.2.1]
  have hku : (k : ℝ) < 1 := by linarith [Y.property.2.1, X.property.2.2.1]
  have hkl' : (-1 : ℤ) < k := by exact_mod_cast hkl
  have hku' : k < (1 : ℤ) := by exact_mod_cast hku
  have hk0 : k = 0 := by omega
  apply Subtype.ext
  funext i
  have hi := hk i
  change X.val i - Y.val i = (k : ℝ) at hi
  simpa only [hk0, Int.cast_zero, sub_eq_zero] using hi

theorem hsConfigurationMap_representative {N : ℕ+} (x : hsChamber N) :
    (hsConfigurationMap N (hsRepresentative x)).val =
      (QuotientAddGroup.mk x.val : HsCylinder N) := by
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  apply (hsPeriodLattice_mem_iff _).mpr
  refine ⟨-⌊x.val ⟨0, N.pos⟩⌋, fun i => ?_⟩
  change (hsRepresentative x).val i - x.val i = _
  rw [hsRepresentative_apply, Int.cast_neg]
  ring

theorem hsConfigurationMap_surjective (N : ℕ+) :
    Function.Surjective (hsConfigurationMap N) := by
  rintro ⟨q, x, hx, rfl⟩
  exact ⟨hsRepresentative ⟨x, hx⟩,
    Subtype.ext (hsConfigurationMap_representative ⟨x, hx⟩)⟩

/-- Equivalence with the fundamental region. Its inverse is uniquely specified. -/
def hsConfigurationEquiv (N : ℕ+) : Configuration N ≃ HsConfiguration N :=
  Equiv.ofBijective (hsConfigurationMap N)
    ⟨hsConfigurationMap_injective N, hsConfigurationMap_surjective N⟩

theorem continuous_hsConfigurationMap (N : ℕ+) : Continuous (hsConfigurationMap N) := by
  apply Continuous.subtype_mk
  exact QuotientAddGroup.continuous_mk.comp
    ((PiLp.continuous_toLp 2 _).comp continuous_subtype_val)

theorem measurable_hsConfigurationMap (N : ℕ+) : Measurable (hsConfigurationMap N) := by
  apply Measurable.subtype_mk
  exact QuotientAddGroup.measurable_coe.comp
    ((PiLp.volume_preserving_toLp (Fin (N : ℕ))).measurable.comp measurable_subtype_coe)

theorem measurableEmbedding_hsConfigurationMap (N : ℕ+) :
    MeasurableEmbedding (hsConfigurationMap N) := by
  let : StandardBorelSpace (Configuration N) := (measurableSet_orderedDomain N).standardBorel
  exact (measurable_hsConfigurationMap N).measurableEmbedding
    (hsConfigurationMap_injective N)

theorem measurable_hsConfigurationEquiv_symm (N : ℕ+) :
    Measurable (hsConfigurationEquiv N).symm := by
  intro s hs
  convert (measurableEmbedding_hsConfigurationMap N).measurableSet_image' hs using 1
  ext x
  simp only [mem_preimage, mem_image]
  constructor
  · intro hx
    exact ⟨(hsConfigurationEquiv N).symm x, hx, (hsConfigurationEquiv N).apply_symm_apply x⟩
  · rintro ⟨y, hy, hyx⟩
    change (hsConfigurationEquiv N) y = x at hyx
    rw [← hyx, Equiv.symm_apply_apply]
    exact hy

/-- The fundamental-region equivalence also preserves the measurable structures. -/
def hsConfigurationMeasurableEquiv (N : ℕ+) : Configuration N ≃ᵐ HsConfiguration N where
  toEquiv := hsConfigurationEquiv N
  measurable_toFun := measurable_hsConfigurationMap N
  measurable_invFun := measurable_hsConfigurationEquiv_symm N

/-- The collision distance as a function on the cyclic quotient. -/
def hsQuotientBoundaryDistance (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (x : HsConfiguration N) : ℝ :=
  hsBoundaryDistance N hN (WithLp.toLp 2 ((hsConfigurationEquiv N).symm x).val)

/-- The quotient distance function agrees with the lift distance at every chamber point. -/
theorem hsQuotientBoundaryDistance_projection {N : ℕ+} (hN : 2 ≤ (N : ℕ)) (x : hsChamber N) :
    hsQuotientBoundaryDistance N hN
      ⟨QuotientAddGroup.mk x.val, ⟨x.val, x.property, rfl⟩⟩ = hsBoundaryDistance N hN x.val := by
  have hq : (hsConfigurationMap N (hsRepresentative x)) =
      (⟨QuotientAddGroup.mk x.val, ⟨x.val, x.property, rfl⟩⟩ : HsConfiguration N) :=
    Subtype.ext (hsConfigurationMap_representative x)
  rw [← hq]
  change hsBoundaryDistance N hN (WithLp.toLp 2
    ((hsConfigurationEquiv N).symm ((hsConfigurationEquiv N) (hsRepresentative x))).val) = _
  rw [Equiv.symm_apply_apply]
  have heq : WithLp.toLp 2 (hsRepresentative x).val =
      hsTranslate (-(⌊x.val ⟨0, N.pos⟩⌋ : ℤ) : ℝ) x.val := by
    ext i
    simp only [hsRepresentative_apply, hsTranslate_apply, sub_eq_add_neg]
  rw [heq, hsBoundaryDistance_translate]

/-- Lebesgue volume on the cyclic quotient, expressed in its fundamental region. -/
def hsConfigurationVolume (N : ℕ+) : Measure (HsConfiguration N) :=
  (configurationVolume N).map (hsConfigurationMap N)

theorem hsConfigurationVolume_univ (N : ℕ+) :
    hsConfigurationVolume N univ = ENNReal.ofReal (1 / (((N : ℕ) - 1).factorial : ℝ)) := by
  rw [hsConfigurationVolume, Measure.map_apply (measurable_hsConfigurationMap N)
    MeasurableSet.univ, preimage_univ]
  exact configurationVolume_univ N

/-- Nonnegative integrals on the cyclic quotient equal fundamental-region integrals. -/
theorem hsConfiguration_lintegral (N : ℕ+) (f : HsConfiguration N → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ x, f x ∂hsConfigurationVolume N =
      ∫⁻ X, f (hsConfigurationMap N X) ∂configurationVolume N := by
  exact lintegral_map hf (measurable_hsConfigurationMap N)

/-- Real integrals on the cyclic quotient equal fundamental-region integrals. -/
theorem hsConfiguration_integral (N : ℕ+) (f : HsConfiguration N → ℝ)
    (hf : AEStronglyMeasurable f (hsConfigurationVolume N)) :
    ∫ x, f x ∂hsConfigurationVolume N =
      ∫ X, f (hsConfigurationMap N X) ∂configurationVolume N := by
  exact integral_map (measurable_hsConfigurationMap N).aemeasurable hf

/-- Euclidean Lebesgue integration on the fundamental region agrees with the volume. -/
theorem hsFundamentalRegion_lintegral (N : ℕ+) (f : (Fin (N : ℕ) → ℝ) → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ x in hsFundamentalRegion N, f (WithLp.ofLp x) =
      ∫⁻ X : Configuration N, f X.val ∂configurationVolume N := by
  rw [hsFundamentalRegion_eq_preimage]
  change _ = ∫⁻ X : orderedDomain N, f X.val ∂Measure.comap Subtype.val volume
  rw [lintegral_subtype_comap (measurableSet_orderedDomain N)]
  exact ((PiLp.volume_preserving_ofLp (Fin (N : ℕ))).restrict_preimage
    (measurableSet_orderedDomain N)).lintegral_comp hf

end Riesz1

end
