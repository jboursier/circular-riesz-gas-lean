/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Chamber.PeriodizationIntegral
public import Riesz1.ToMathlib.EllipticRegularity.WeakDerivatives

/-!
# Local square integrability of periodic representatives

Square integrability in one fundamental strip suffices for local square
integrability on the cover. No continuity of the representative is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Riesz1

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F]

local instance : HasUniqueDiv E := HasUniqueDiv.of_isTorsionFree ℝ E

omit [FiniteDimensional ℝ E] in
/-- Translation of the origin of a half-open strip preserves its
fundamental-domain property. -/
theorem isAddFundamentalDomain_vectorStrip_shift {v : E} (hv : v ≠ 0)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1) (a : ℝ) (μ : Measure E) :
    IsAddFundamentalDomain (AddSubgroup.zmultiples v) (ℓ ⁻¹' Ico a (a + 1)) μ := by
  let e := (AddSubgroup.zmultiplesEquivInt hv).symm
  apply IsAddFundamentalDomain.mk'
    ((measurableSet_Ico.preimage ℓ.continuous.measurable).nullMeasurableSet)
  intro x
  apply e.bijective.existsUnique_iff.mpr
  have he (k : ℤ) : ℓ ((e k : E) + x) = (k : ℝ) + ℓ x := by
    rw [AddSubgroup.coe_zmultiplesEquivInt_symm_apply, map_add, map_zsmul, hℓ]
    simp
  refine ⟨-⌊ℓ x - a⌋, ?_, ?_⟩
  · change ℓ ((e (-⌊ℓ x - a⌋) : E) + x) ∈ Ico a (a + 1)
    rw [he, Int.cast_neg]
    exact ⟨by linarith [Int.floor_le (ℓ x - a)],
      by linarith [Int.lt_floor_add_one (ℓ x - a)]⟩
  · intro k hk
    change ℓ ((e k : E) + x) ∈ Ico a (a + 1) at hk
    rw [he] at hk
    have hlo : (-1 : ℝ) < (k : ℝ) + (⌊ℓ x - a⌋ : ℝ) := by
      linarith [hk.1, Int.lt_floor_add_one (ℓ x - a)]
    have hhi : (k : ℝ) + (⌊ℓ x - a⌋ : ℝ) < 1 := by
      linarith [hk.2, Int.floor_le (ℓ x - a)]
    have hlo' : (-1 : ℤ) < k + ⌊ℓ x - a⌋ := by exact_mod_cast hlo
    have hhi' : k + ⌊ℓ x - a⌋ < (1 : ℤ) := by exact_mod_cast hhi
    omega

/-- L² membership of a periodic representative is independent of the
origin of its fundamental strip, including its measurability certificate. -/
theorem memLp_two_vectorStrip_shift_iff {v : E} (hv : v ≠ 0)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1) {f : E → F}
    (hf : ∀ (k : ℤ) x, f (x + (k : ℝ) • v) = f x) (a : ℝ) :
    MemLp f 2 (volume.restrict (ℓ ⁻¹' Ico a (a + 1))) ↔
      MemLp f 2 (volume.restrict (ℓ ⁻¹' Ico (0 : ℝ) 1)) := by
  have hDa := isAddFundamentalDomain_vectorStrip_shift hv ℓ hℓ a (volume : Measure E)
  have hD := isAddFundamentalDomain_vectorStrip hv ℓ hℓ (volume : Measure E)
  have hp (g : AddSubgroup.zmultiples v) (x : E) : f (g +ᵥ x) = f x := by
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp g.property
    change f ((g : E) + x) = f x
    rw [← hk, add_comm]
    simpa only [Int.cast_smul_eq_zsmul] using hf k x
  have hm := hDa.aestronglyMeasurable_on_iff hD hp
  constructor
  · intro h
    have hm' := hm.mp h.aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq_norm hm').mpr
    exact (hDa.integrableOn_iff hD (fun g x => by rw [hp g x])).mp
      ((memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h)
  · intro h
    have hm' := hm.mpr h.aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq_norm hm').mpr
    exact (hDa.integrableOn_iff hD (fun g x => by rw [hp g x])).mpr
      ((memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h)

/-- A periodic L² representative on one strip is locally L² on the whole
Euclidean cover. This does not assert global L² on the infinite cover. -/
theorem locallySquareIntegrableOn_vectorPeriodic {v : E} (hv : v ≠ 0)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1) {f : E → F}
    (hf : ∀ (k : ℤ) x, f (x + (k : ℝ) • v) = f x)
    (hL : MemLp f 2 (volume.restrict (ℓ ⁻¹' Ico (0 : ℝ) 1))) :
    LocallySquareIntegrableOn univ f := by
  have hshift (a : ℝ) := (memLp_two_vectorStrip_shift_iff hv ℓ hℓ hf a).mpr hL
  have hlocal : LocallyIntegrableOn f univ := by
    intro x _
    let a := ℓ x - 1 / 2
    have hn : ℓ ⁻¹' Ico a (a + 1) ∈ 𝓝 x := by
      apply mem_of_superset ((isOpen_Ioo.preimage ℓ.continuous).mem_nhds ?_)
        (preimage_mono Ioo_subset_Ico_self)
      change a < ℓ x ∧ ℓ x < a + 1
      dsimp [a]
      constructor <;> linarith
    have hL' : MemLp f 2
        (volume.restrict ((ℓ ⁻¹' Ico a (a + 1)) ∩ Metric.closedBall x 1)) :=
      (hshift a).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
    have : IsFiniteMeasure (volume.restrict (Metric.closedBall x 1)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using
        (isCompact_closedBall x 1).measure_lt_top (μ := volume)⟩
    have : IsFiniteMeasure
        (volume.restrict ((ℓ ⁻¹' Ico a (a + 1)) ∩ Metric.closedBall x 1)) :=
      isFiniteMeasure_of_le (volume.restrict (Metric.closedBall x 1))
        (Measure.restrict_mono inter_subset_right le_rfl)
    refine ⟨_, ?_, hL'.integrable (by norm_num)⟩
    simpa only [nhdsWithin_univ] using
      inter_mem hn (Metric.closedBall_mem_nhds x (by norm_num : (0 : ℝ) < 1))
  have hsq : LocallyIntegrableOn (fun x => ‖f x‖ ^ 2) univ := by
    intro x _
    let a := ℓ x - 1 / 2
    have hn : ℓ ⁻¹' Ico a (a + 1) ∈ 𝓝 x := by
      apply mem_of_superset ((isOpen_Ioo.preimage ℓ.continuous).mem_nhds ?_)
        (preimage_mono Ioo_subset_Ico_self)
      change a < ℓ x ∧ ℓ x < a + 1
      dsimp [a]
      constructor <;> linarith
    exact ⟨_, by simpa only [nhdsWithin_univ] using hn,
      (memLp_two_iff_integrable_sq_norm (hshift a).aestronglyMeasurable).mp (hshift a)⟩
  intro K hK _
  have hm : AEStronglyMeasurable f volume := by
    simpa only [Measure.restrict_univ] using hlocal.aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq_norm hm.restrict).mpr
    (hsq.integrableOn_compact_subset (subset_univ _) hK)

end Riesz1
