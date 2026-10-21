/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Chamber.Periodization
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Unfolding compact vector periodizations

A half-open strip for a linear functional taking the period vector to one
is a fundamental domain. Integration of a compact periodization over that
strip equals integration of the original function over the cover. In
particular the support may cross either edge of the strip.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Function Filter Topology

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local instance : HasUniqueDiv E := HasUniqueDiv.of_isTorsionFree ℝ E

/-- A strip is a fundamental domain for integer translations along its period vector. -/
theorem isAddFundamentalDomain_vectorStrip {v : E} (hv : v ≠ 0)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1) (μ : Measure E) :
    IsAddFundamentalDomain (AddSubgroup.zmultiples v) (ℓ ⁻¹' Ico (0 : ℝ) 1) μ := by
  let e := (AddSubgroup.zmultiplesEquivInt hv).symm
  apply IsAddFundamentalDomain.mk'
    ((measurableSet_Ico.preimage ℓ.continuous.measurable).nullMeasurableSet)
  intro x
  apply e.bijective.existsUnique_iff.mpr
  have he (k : ℤ) : ℓ ((e k : E) + x) = (k : ℝ) + ℓ x := by
    rw [AddSubgroup.coe_zmultiplesEquivInt_symm_apply, map_add, map_zsmul, hℓ]
    simp
  refine ⟨-⌊ℓ x⌋, ?_, ?_⟩
  · change ℓ ((e (-⌊ℓ x⌋) : E) + x) ∈ Ico (0 : ℝ) 1
    rw [he, Int.cast_neg]
    exact ⟨by linarith [Int.floor_le (ℓ x)], by linarith [Int.lt_floor_add_one (ℓ x)]⟩
  · intro k hk
    change ℓ ((e k : E) + x) ∈ Ico (0 : ℝ) 1 at hk
    rw [he] at hk
    have hlo : (-1 : ℝ) < (k : ℝ) + (⌊ℓ x⌋ : ℝ) := by
      linarith [hk.1, Int.lt_floor_add_one (ℓ x)]
    have hhi : (k : ℝ) + (⌊ℓ x⌋ : ℝ) < 1 := by
      linarith [hk.2, Int.floor_le (ℓ x)]
    have hlo' : (-1 : ℤ) < k + ⌊ℓ x⌋ := by exact_mod_cast hlo
    have hhi' : k + ⌊ℓ x⌋ < 1 := by exact_mod_cast hhi
    omega

variable {μ : Measure E} [IsAddHaarMeasure μ]

/-- Unfolding holds without a support restriction to the open strip. -/
theorem integral_vectorPeriodize {v : E} (hv : v ≠ 0)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1) {f : E → ℝ}
    (hs : HasCompactSupport f) (hf : Integrable f μ) :
    ∫ x in ℓ ⁻¹' Ico (0 : ℝ) 1, vectorPeriodize v hv f hs x ∂μ = ∫ x, f x ∂μ := by
  let e := (AddSubgroup.zmultiplesEquivInt hv).symm
  have hD := isAddFundamentalDomain_vectorStrip hv ℓ hℓ μ
  have hsum (x : E) : vectorPeriodize v hv f hs x =
      ∑' g : AddSubgroup.zmultiples v, f ((g : E) + x) := by
    rw [← e.toEquiv.tsum_eq]
    simp only [e, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv,
      AddSubgroup.coe_zmultiplesEquivInt_symm_apply]
    rw [tsum_eq_finsum (by simpa only [add_comm, Int.cast_smul_eq_zsmul] using
      vectorPeriodize_finite_support hv hs x)]
    unfold vectorPeriodize
    congr 1
    funext k
    rw [add_comm, Int.cast_smul_eq_zsmul]
  simp_rw [hsum]
  rw [integral_tsum]
  · exact (hD.integral_eq_tsum'' f hf).symm
  · intro g
    exact (hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_add_left μ (g : E)).quasiMeasurePreserving).restrict
  · have hn := hD.lintegral_eq_tsum'' (fun x => ‖f x‖ₑ)
    exact hn.symm ▸ hf.hasFiniteIntegral.ne

omit [MeasurableSpace E] [BorelSpace E] in
/-- A periodic multiplier can be moved inside the periodization. -/
theorem vectorPeriodize_mul_periodic {v : E} (hv : v ≠ 0) {f b : E → ℝ}
    (hs : HasCompactSupport f)
    (hb : ∀ (k : ℤ) x, b (x + (k : ℝ) • v) = b x) (x : E) :
    vectorPeriodize v hv (fun y => f y * b y) hs.mul_right x =
      vectorPeriodize v hv f hs x * b x := by
  simp only [vectorPeriodize, hb, finsum_mul]

/-- Unfolding with a periodic multiplier, including tests crossing the seam. -/
theorem integral_vectorPeriodize_mul_periodic {v : E} (hv : v ≠ 0)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1) {f b : E → ℝ}
    (hs : HasCompactSupport f)
    (hb : ∀ (k : ℤ) x, b (x + (k : ℝ) • v) = b x)
    (hf : Integrable (fun x => f x * b x) μ) :
    ∫ x in ℓ ⁻¹' Ico (0 : ℝ) 1, vectorPeriodize v hv f hs x * b x ∂μ =
      ∫ x, f x * b x ∂μ := by
  simp_rw [← vectorPeriodize_mul_periodic hv hs hb]
  exact integral_vectorPeriodize hv ℓ hℓ hs.mul_right hf

omit [MeasurableSpace E] [BorelSpace E] in
/-- Periodizing inside an invariant open set preserves the zero extension. -/
theorem vectorPeriodize_eq_zero_of_not_mem {v : E} (hv : v ≠ 0) {f : E → ℝ}
    (hs : HasCompactSupport f) {U : Set E}
    (hU : ∀ (k : ℤ) x, x + (k : ℝ) • v ∈ U ↔ x ∈ U)
    (hf : support f ⊆ U) {x : E} (hx : x ∉ U) :
    vectorPeriodize v hv f hs x = 0 := by
  unfold vectorPeriodize
  apply finsum_eq_zero_of_forall_eq_zero
  intro k
  by_contra hk
  exact hx ((hU k x).mp (hf hk))

end Riesz1

end
