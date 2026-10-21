/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.QuotientChartGeometry
public import Riesz1.ToMathlib.PeriodicLocalLp

/-!
# Local Lebesgue L² transport of quotient representatives

The results apply to arbitrary L² representatives, with no continuity
assumption, and to compact sets crossing the rotation seam.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Topology ENNReal

namespace Riesz1

/-- Pulling a cylinder function back to the cover preserves local L²
inside the chamber. Off the chamber an indicator is used only for the
intermediate measure argument. -/
theorem locallySquareIntegrableOn_quotient_mk {N : ℕ+} {F : Type*}
    [NormedAddCommGroup F] {f : HsCylinder N → F}
    (hf : MemLp (fun x : HsConfiguration N => f x.val) 2 (hsConfigurationVolume N)) :
    LocallySquareIntegrableOn (hsChamber N)
      (fun x : HsEuclidean N => f (QuotientAddGroup.mk x)) := by
  classical
  let u : HsEuclidean N → F := fun x => f (QuotientAddGroup.mk x)
  let w := (hsChamber N).indicator u
  have hfund : MemLp w 2 (volume.restrict (hsFundamentalRegion N)) := by
    apply memLp_hsLiftPoint_volume_iff.mp
    have he : w ∘ hsLiftPoint N = fun x : HsConfiguration N => f x.val := by
      funext x
      dsimp [w, u]
      rw [indicator_of_mem (hsLiftPoint_mem_chamber N x)]
      exact congrArg f (congrArg Subtype.val (hsChamberProjection_liftPoint x))
    rwa [he]
  let ℓ := EuclideanSpace.proj (𝕜 := ℝ) (⟨0, N.pos⟩ : Fin (N : ℕ))
  have hℓ : ℓ (hsRotationVector N) = 1 := by simp [ℓ, hsRotationVector]
  have hstrip : MemLp w 2 (volume.restrict (ℓ ⁻¹' Ico (0 : ℝ) 1)) := by
    apply (memLp_indicator_iff_restrict
      ((isOpen_hsChamber N).measurableSet.nullMeasurableSet)).mpr
    rw [Measure.restrict_restrict (isOpen_hsChamber N).measurableSet]
    change MemLp u 2 (volume.restrict (hsFundamentalRegion N))
    apply hfund.ae_eq
    filter_upwards [ae_restrict_mem (measurableSet_hsFundamentalRegion N)] with x hx
    exact indicator_of_mem hx.1 u
  have hp (k : ℤ) (x : HsEuclidean N) :
      w (x + (k : ℝ) • hsRotationVector N) = w x := by
    have hq : (QuotientAddGroup.mk (x + (k : ℝ) • hsRotationVector N) : HsCylinder N) =
        QuotientAddGroup.mk x := by
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      apply (hsPeriodLattice_mem_iff _).mpr
      refine ⟨k, fun i => ?_⟩
      change x i + (k : ℝ) * 1 - x i = (k : ℝ)
      ring
    dsimp only [w]
    by_cases hx : x ∈ hsChamber N
    · have ht : x + (k : ℝ) • hsRotationVector N ∈ hsChamber N := by
        rw [← hsTranslate_eq_add_rotation]
        exact (hsTranslate_mem_chamber_iff _ _).mpr hx
      rw [indicator_of_mem hx, indicator_of_mem ht]
      exact congrArg f hq
    · have ht : x + (k : ℝ) • hsRotationVector N ∉ hsChamber N := by
        rw [← hsTranslate_eq_add_rotation]
        exact fun hh => hx ((hsTranslate_mem_chamber_iff _ _).mp hh)
      rw [indicator_of_notMem hx, indicator_of_notMem ht]
  have hw := locallySquareIntegrableOn_vectorPeriodic (hsRotationVector_ne_zero N) ℓ hℓ hp hstrip
  intro K hK hKU
  apply (hw K hK (subset_univ _)).ae_eq
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact indicator_of_mem (hKU hx) u

/-- Every quotient L² representative pulls back to Lebesgue L² on each
compact interior set. The map in the conclusion is the actual chart
projection, and there is no restriction on the first coordinate. -/
theorem memLp_hsChamberProjection_compact {N : ℕ+} {F : Type*}
    [NormedAddCommGroup F] {f : HsConfiguration N → F}
    (hf : MemLp f 2 (hsConfigurationVolume N))
    {K : Set (HsEuclidean N)} (hK : IsCompact K) (hKU : K ⊆ hsChamber N) :
    MemLp (fun x : K => f (hsChamberProjection ⟨x.val, hKU x.property⟩)) 2
      (Measure.comap (Subtype.val : K → HsEuclidean N) volume) := by
  let g : HsCylinder N → F := Function.extend Subtype.val f (fun _ => 0)
  have hg : ∀ x : HsConfiguration N, g x.val = f x :=
    Subtype.val_injective.extend_apply f (fun _ => 0)
  have hgL : MemLp (fun x : HsConfiguration N => g x.val) 2 (hsConfigurationVolume N) := by
    simpa only [hg] using hf
  have hL := locallySquareIntegrableOn_quotient_mk hgL K hK hKU
  rw [← map_comap_subtype_coe hK.measurableSet volume,
    (MeasurableEmbedding.subtype_coe hK.measurableSet).memLp_map_measure_iff] at hL
  convert hL using 1
  funext x
  exact (hg (hsChamberProjection ⟨x.val, hKU x.property⟩)).symm

end Riesz1
