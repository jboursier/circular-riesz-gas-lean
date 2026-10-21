/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Chamber.PeriodicSquareCutoff

/-!
# Integrability of compact periodizations

Only finitely many translates of a compactly supported function meet a
fixed fundamental strip. Consequently periodization preserves L¹, with no
continuity assumption on the integrand. Square partition weights recover
both integrability and the integral of an arbitrary periodic integrand.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Function

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A single finite set of integer translates suffices throughout the
whole fundamental strip, even when that strip is unbounded transversely. -/
theorem finite_vector_translates_on_strip {v : E} (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1)
    {f : E → ℝ} (hf : HasCompactSupport f) :
    ∃ s : Finset ℤ, ∀ x ∈ ℓ ⁻¹' Ico (0 : ℝ) 1,
      support (fun k : ℤ => f (x + (k : ℝ) • v)) ⊆ s := by
  classical
  obtain ⟨C, hC⟩ := (hf.image ℓ.continuous).isBounded.exists_norm_le
  have hfin : {k : ℤ | ‖k‖ ≤ C + 1}.Finite := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (isCompact_closedBall (0 : ℤ) (C + 1)).finite_of_discrete
  refine ⟨hfin.toFinset, fun x hx k hk => hfin.mem_toFinset.mpr ?_⟩
  have hb := hC (ℓ (x + (k : ℝ) • v))
    ⟨x + (k : ℝ) • v, subset_tsupport f hk, rfl⟩
  simp only [map_add, map_smul, hℓ, smul_eq_mul, mul_one, Real.norm_eq_abs] at hb
  have hlo := neg_le_abs (ℓ x + (k : ℝ))
  have hhi := le_abs_self (ℓ x + (k : ℝ))
  have hk' : |(k : ℝ)| ≤ C + 1 := abs_le.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
  simpa only [mem_ofPred_eq, Int.norm_eq_abs, Int.cast_abs] using hk'

variable {μ : Measure E} [IsAddHaarMeasure μ]

/-- Compact periodization is integrable on a fundamental strip whenever
the original representative is integrable on the cover. -/
theorem integrableOn_vectorPeriodize {v : E} (hv : v ≠ 0)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1) {f : E → ℝ}
    (hs : HasCompactSupport f) (hf : Integrable f μ) :
    IntegrableOn (vectorPeriodize v hv f hs) (ℓ ⁻¹' Ico (0 : ℝ) 1) μ := by
  classical
  obtain ⟨s, hsupport⟩ := finite_vector_translates_on_strip ℓ hℓ hs
  have hI : IntegrableOn (fun x => ∑ k ∈ s, f (x + (k : ℝ) • v))
      (ℓ ⁻¹' Ico (0 : ℝ) 1) μ :=
    integrable_finsetSum s (fun k _ =>
      (((measurePreserving_add_right μ ((k : ℝ) • v)).integrable_comp
        hf.aestronglyMeasurable).mpr hf).restrict)
  apply hI.congr
  filter_upwards [ae_restrict_mem (measurableSet_Ico.preimage ℓ.continuous.measurable)] with x hx
  exact (finsum_eq_sum_of_support_subset _ (hsupport x hx)).symm

/-- A square partition weight unfolds arbitrary periodic integrands.
Integrability is concluded on the strip, as well as the integral equality. -/
theorem integral_periodicSquareCutoff_sq_mul {v : E} (hv : v ≠ 0)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1) {f : E → ℝ}
    (hp : ∀ (k : ℤ) x, f (x + (k : ℝ) • v) = f x)
    (hs : HasCompactSupport (fun x => periodicSquareCutoff (ℓ x) ^ 2 * f x))
    (hf : Integrable (fun x => periodicSquareCutoff (ℓ x) ^ 2 * f x) μ) :
    IntegrableOn f (ℓ ⁻¹' Ico (0 : ℝ) 1) μ ∧
      (∫ x in ℓ ⁻¹' Ico (0 : ℝ) 1, f x ∂μ) =
        ∫ x, periodicSquareCutoff (ℓ x) ^ 2 * f x ∂μ := by
  have he : vectorPeriodize v hv (fun x => periodicSquareCutoff (ℓ x) ^ 2 * f x) hs = f := by
    funext x
    simp only [vectorPeriodize, map_add, map_smul, hℓ, smul_eq_mul, mul_one, hp]
    rw [← finsum_mul, finsum_periodicSquareCutoff_sq, one_mul]
  exact ⟨by simpa only [he] using integrableOn_vectorPeriodize hv ℓ hℓ hs hf,
    by simpa only [he] using integral_vectorPeriodize hv ℓ hℓ hs hf⟩

end Riesz1
