/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SobolevDensity
public import Riesz1.ToMathlib.Chamber.PeriodizationIntegral

/-!
# Projection from the chamber and fundamental-region measure transport

The chamber projection is the actual quotient projection. Its restrictions
to open rotation strips of length one are injective, including strips across
an integer seam. The chosen fundamental representative transports quotient
volume to restricted Euclidean volume, for arbitrary measurable integrands.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology ENNReal

namespace Riesz1

/-- The quotient projection on the entire open chamber. -/
def hsChamberProjection {N : ℕ+} (x : hsChamber N) : HsConfiguration N :=
  ⟨QuotientAddGroup.mk x.val, ⟨x.val, x.property, rfl⟩⟩

theorem continuous_hsChamberProjection (N : ℕ+) :
    Continuous (hsChamberProjection (N := N)) :=
  (QuotientAddGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _

theorem measurable_hsChamberProjection (N : ℕ+) :
    Measurable (hsChamberProjection (N := N)) :=
  (continuous_hsChamberProjection N).measurable

theorem hsChamberProjection_translate {N : ℕ+} (k : ℤ) (x : hsChamber N) :
    hsChamberProjection
      ⟨hsTranslate (k : ℝ) x.val, (hsTranslate_mem_chamber_iff _ _).mpr x.property⟩ =
      hsChamberProjection x := by
  apply Subtype.ext
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  apply (hsPeriodLattice_mem_iff _).mpr
  refine ⟨k, fun i => ?_⟩
  change (x.val i + (k : ℝ)) - x.val i = (k : ℝ)
  ring

theorem hsChamberProjection_representative {N : ℕ+} (x : hsChamber N) :
    hsConfigurationMap N (hsRepresentative x) = hsChamberProjection x :=
  Subtype.ext (hsConfigurationMap_representative x)

theorem hsChamberProjection_liftPoint {N : ℕ+} (x : HsConfiguration N) :
    hsChamberProjection ⟨hsLiftPoint N x, hsLiftPoint_mem_chamber N x⟩ = x := by
  change hsConfigurationMap N ((hsConfigurationEquiv N).symm x) = x
  exact (hsConfigurationEquiv N).apply_symm_apply x

/-- Every open rotation strip of length one is an injective chart domain. -/
theorem hsChamberProjection_injOn_strip (N : ℕ+) (a : ℝ) :
    InjOn (hsChamberProjection (N := N))
      {x | a < x.val ⟨0, N.pos⟩ ∧ x.val ⟨0, N.pos⟩ < a + 1} := by
  intro x hx y hy hxy
  have hq := congrArg Subtype.val hxy
  obtain ⟨k, hk⟩ := (hsPeriodLattice_mem_iff _).mp
    (QuotientAddGroup.eq_iff_sub_mem.mp hq)
  have h0 := hk ⟨0, N.pos⟩
  change x.val ⟨0, N.pos⟩ - y.val ⟨0, N.pos⟩ = (k : ℝ) at h0
  have hlo : (-1 : ℝ) < (k : ℝ) := by linarith [hx.1, hy.2]
  have hhi : (k : ℝ) < 1 := by linarith [hy.1, hx.2]
  have hlo' : (-1 : ℤ) < k := by exact_mod_cast hlo
  have hhi' : k < (1 : ℤ) := by exact_mod_cast hhi
  have hk0 : k = 0 := by omega
  apply Subtype.ext
  ext i
  have hi := hk i
  change x.val i - y.val i = (k : ℝ) at hi
  simpa only [hk0, Int.cast_zero, sub_eq_zero] using hi

/-- The representative map preserves volume, with target the Euclidean
half-open fundamental region rather than the whole infinite cover. -/
theorem measurePreserving_hsLiftPoint_volume (N : ℕ+) :
    MeasurePreserving (hsLiftPoint N) (hsConfigurationVolume N)
      (volume.restrict (hsFundamentalRegion N)) := by
  refine ⟨measurable_hsLiftPoint N, ?_⟩
  rw [hsConfigurationVolume, Measure.map_map (measurable_hsLiftPoint N)
    (measurable_hsConfigurationMap N)]
  have he : hsLiftPoint N ∘ hsConfigurationMap N =
      fun X : Configuration N => WithLp.toLp 2 X.val := by
    funext X
    change WithLp.toLp 2 ((hsConfigurationEquiv N).symm
      ((hsConfigurationEquiv N) X)).val = _
    rw [Equiv.symm_apply_apply]
  rw [he]
  change (Measure.comap (Subtype.val : Configuration N → (Fin (N : ℕ) → ℝ)) volume).map
    ((WithLp.toLp 2) ∘ Subtype.val) = _
  rw [← Measure.map_map (PiLp.volume_preserving_toLp (Fin (N : ℕ))).measurable
    measurable_subtype_coe, map_comap_subtype_coe (measurableSet_orderedDomain N)]
  rw [hsFundamentalRegion_eq_preimage]
  exact ((PiLp.volume_preserving_toLp (Fin (N : ℕ))).restrict_image_emb
    (PiLp.homeomorph 2 (fun _ : Fin (N : ℕ) => ℝ)).symm.measurableEmbedding
    (orderedDomain N)).map_eq.trans (by
      congr 1
      ext x
      simp only [mem_image, mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨WithLp.ofLp x, hx, rfl⟩)

/-- Arbitrary quotient Lp representatives pull back to Lp representatives
in the fundamental region. No continuity hypothesis is involved. -/
theorem memLp_hsLiftPoint_volume_iff {N : ℕ+} {F : Type*}
    [NormedAddCommGroup F] {p : ℝ≥0∞} {f : HsEuclidean N → F} :
    MemLp (f ∘ hsLiftPoint N) p (hsConfigurationVolume N) ↔
      MemLp f p (volume.restrict (hsFundamentalRegion N)) := by
  rw [← (measurePreserving_hsLiftPoint_volume N).map_eq]
  exact (measurableEmbedding_hsLiftPoint N).memLp_map_measure_iff.symm

end Riesz1
