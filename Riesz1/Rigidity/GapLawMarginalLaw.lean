/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.GapLawMarginalConcavity
public import Riesz1.ToMathlib.LogConcave.MarginalConcaveDensity

/-!
# The law of one gap as a fiber density

First split the anchored law into its first offset and the remaining offsets.
Tonelli's theorem gives the offset marginal. A dilation by `N` then gives the
density of the physical gap, with its exact Jacobian factor `1/N`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

lemma anchoredLaw_eq_extendedDensity (P : Parameters) (n : ℕ) :
    anchoredLaw P n = volume.withDensity
      (fun y => ENNReal.ofReal (extendedAnchoredProbabilityDensity P n y)) := by
  rw [anchoredLaw_eq_withDensity]
  have he : (fun y => ENNReal.ofReal (extendedAnchoredProbabilityDensity P n y)) =
      (anchoredDomain n).indicator (fun y => ENNReal.ofReal (anchoredProbabilityDensity P n y)) := by
    ext y
    by_cases hy : y ∈ anchoredDomain n
    · rw [Set.indicator_of_mem hy]
      exact congrArg ENNReal.ofReal (Set.indicator_of_mem hy _)
    · rw [Set.indicator_of_notMem hy]
      rw [extendedAnchoredProbabilityDensity, Set.indicator_of_notMem hy, ENNReal.ofReal_zero]
  rw [he, withDensity_indicator (measurableSet_anchoredDomain n)]

lemma map_anchoredLaw_split (P : Parameters) (n : ℕ) :
    (anchoredLaw P (n + 1)).map (fun y => (y 0, Fin.tail y)) =
      (volume.prod volume).withDensity
        (fun p => ENNReal.ofReal (gapOffsetJointDensity P n p)) := by
  let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have he (y : Fin (n + 1) → ℝ) : e y = (y 0, Fin.tail y) := by
    apply Prod.ext
    · rfl
    · ext i
      simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
  have hevol : (volume : Measure (Fin (n + 1) → ℝ)).map e = volume.prod volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).map_eq
  have hcomp : (fun y => ENNReal.ofReal (extendedAnchoredProbabilityDensity P (n + 1) y)) =
      fun y => ENNReal.ofReal (gapOffsetJointDensity P n (e y)) := by
    ext y
    rw [he]
    change ENNReal.ofReal (extendedAnchoredProbabilityDensity P (n + 1) y) =
      ENNReal.ofReal (extendedAnchoredProbabilityDensity P (n + 1) (Fin.cons (y 0) (Fin.tail y)))
    rw [Fin.cons_self_tail]
  have hefun : (fun y => (y 0, Fin.tail y)) = e := funext fun y => (he y).symm
  rw [hefun, anchoredLaw_eq_extendedDensity, hcomp]
  have ht := map_withDensity_comp volume e.measurable
    (g := fun p => ENNReal.ofReal (gapOffsetJointDensity P n p))
    (ENNReal.measurable_ofReal.comp (measurable_gapOffsetJointDensity P n))
  exact ht.trans (congrArg (fun μ => μ.withDensity
    (fun p => ENNReal.ofReal (gapOffsetJointDensity P n p))) hevol)

/-- The first anchored offset has exactly the real fiber integral as density. -/
theorem map_anchoredLaw_first_density (P : Parameters) (n : ℕ) :
    (anchoredLaw P (n + 1)).map (fun y => y 0) =
      volume.withDensity (fun r => ENNReal.ofReal (gapOffsetMarginalDensity P n r)) := by
  have hcomp : (fun y : Fin (n + 1) → ℝ => y 0) =
      Prod.fst ∘ (fun y => (y 0, Fin.tail y)) := rfl
  rw [hcomp, ← Measure.map_map measurable_fst (by fun_prop), map_anchoredLaw_split]
  trans volume.withDensity (fun r => ∫⁻ z, ENNReal.ofReal (gapOffsetJointDensity P n (r, z)))
  · exact map_fst_withDensity_fiber volume volume
      (fun p => ENNReal.ofReal (gapOffsetJointDensity P n p))
      (ENNReal.measurable_ofReal.comp (measurable_gapOffsetJointDensity P n))
  congr 1
  ext r
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_gapOffsetJointDensity_fiber P n r)
    (Filter.Eventually.of_forall fun z => gapOffsetJointDensity_nonneg P n (r, z))).symm

lemma gapOffsetMarginalDensity_eq_zero (P : Parameters) (n : ℕ) {r : ℝ}
    (hr : r ∉ Ioo (0 : ℝ) 1) : gapOffsetMarginalDensity P n r = 0 := by
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro z
  apply Set.indicator_of_notMem
  intro h
  exact hr ((mem_anchoredDomain_cons_iff n r z).mp h).1

lemma measurable_gapOffsetMarginalDensity (P : Parameters) (n : ℕ) :
    Measurable (gapOffsetMarginalDensity P n) := by
  have hm : Measurable (fun r => ∫⁻ z, ENNReal.ofReal (gapOffsetJointDensity P n (r, z))) :=
    (ENNReal.measurable_ofReal.comp (measurable_gapOffsetJointDensity P n)).lintegral_prod_right'
  have he : gapOffsetMarginalDensity P n = fun r =>
      (∫⁻ z, ENNReal.ofReal (gapOffsetJointDensity P n (r, z))).toReal := by
    ext r
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gapOffsetJointDensity_fiber P n r)
      (Filter.Eventually.of_forall fun z => gapOffsetJointDensity_nonneg P n (r, z))]
    exact (ENNReal.toReal_ofReal (gapOffsetMarginalDensity_nonneg P n r)).symm
  rw [he]
  exact hm.ennreal_toReal

theorem map_anchoredLaw_first_restrict_density (P : Parameters) (n : ℕ) :
    (anchoredLaw P (n + 1)).map (fun y => y 0) =
      (volume.restrict (Ioo (0 : ℝ) 1)).withDensity
        (fun r => ENNReal.ofReal (gapOffsetMarginalDensity P n r)) := by
  rw [map_anchoredLaw_first_density, ← withDensity_indicator measurableSet_Ioo]
  congr 1
  ext r
  by_cases hr : r ∈ Ioo (0 : ℝ) 1
  · rw [Set.indicator_of_mem hr]
  · rw [Set.indicator_of_notMem hr, gapOffsetMarginalDensity_eq_zero P n hr, ENNReal.ofReal_zero]

lemma map_interval_withDensity_mul_pos (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ) (hf : Measurable f) :
    ((volume.restrict (Ioo (0 : ℝ) 1)).withDensity (fun t => ENNReal.ofReal (f t))).map
      (fun t => a * t) =
      (volume.restrict (Ioo (0 : ℝ) a)).withDensity
        (fun t => ENNReal.ofReal (f (t / a) / a)) := by
  have hpre : (fun t : ℝ => a * t) ⁻¹' Ioo (0 : ℝ) a = Ioo (0 : ℝ) 1 := by
    ext t
    simp only [mem_preimage, mem_Ioo]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨(mul_pos_iff_of_pos_left ha).mp h₁,
        (mul_lt_mul_iff_right₀ ha).mp (by simpa only [mul_one] using h₂)⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨mul_pos ha h₁, by simpa only [mul_one] using mul_lt_mul_of_pos_left h₂ ha⟩
  have hmap : (volume.restrict (Ioo (0 : ℝ) 1)).map (fun t => a * t) =
      ENNReal.ofReal a⁻¹ • volume.restrict (Ioo (0 : ℝ) a) := by
    rw [← hpre, ← Measure.restrict_map (by fun_prop) measurableSet_Ioo,
      Real.map_volume_mul_left ha.ne', Measure.restrict_smul, abs_of_pos (inv_pos.mpr ha)]
  have hcomp : (fun t : ℝ => ENNReal.ofReal (f t)) =
      fun t => ENNReal.ofReal (f ((a * t) / a)) := by
    ext t
    rw [mul_div_cancel_left₀ t ha.ne']
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal (f (t / a))) :=
    ENNReal.measurable_ofReal.comp (hf.comp (by fun_prop))
  rw [hcomp, map_withDensity_comp _ (by fun_prop) hm, hmap, withDensity_smul_measure]
  have hd : (fun t => ENNReal.ofReal (f (t / a) / a)) =
      ENNReal.ofReal a⁻¹ • (fun t => ENNReal.ofReal (f (t / a))) := by
    ext t
    change ENNReal.ofReal (f (t / a) / a) = ENNReal.ofReal a⁻¹ * ENNReal.ofReal (f (t / a))
    rw [show f (t / a) / a = a⁻¹ * f (t / a) by ring,
      ENNReal.ofReal_mul (inv_pos.mpr ha).le]
  rw [hd, withDensity_smul _ hm]

/-- The normalized physical one-gap density for a system of `n + 2` particles. -/
def gapMarginalProbabilityDensity (P : Parameters) (n : ℕ) (t : ℝ) : ℝ :=
  gapOffsetMarginalDensity P n (t / (n + 2 : ℝ)) / (n + 2 : ℝ)

lemma anchoredGapAt_zero_succ (n : ℕ) (y : Fin (n + 1) → ℝ) :
    anchoredGapAt (n + 1) y 0 = (n + 2 : ℝ) * y 0 := by
  unfold anchoredGapAt
  have h₀ : anchoredCyclicOffset (n + 1) y 0 = 0 := anchoredCyclicOffset_natCast (n + 1) y 0
  have h₁ : anchoredCyclicOffset (n + 1) y 1 = y 0 :=
    anchoredCyclicOffset_natCast (n + 1) y (0 : Fin (n + 1)).succ
  rw [zero_add, h₀, h₁, sub_zero]
  push_cast
  ring

/-- The law of every integer-labeled gap, including for `N = 2`, has this fiber density. -/
theorem map_gap_gibbsMeasure_marginal_density (P : Parameters) (n : ℕ) (j : ℤ) :
    (gibbsMeasure P (n + 1).succPNat).map (fun X => gap X j) =
      (volume.restrict (Ioo (0 : ℝ) (n + 2 : ℝ))).withDensity
        (fun t => ENNReal.ofReal (gapMarginalProbabilityDensity P n t)) := by
  rw [map_gap_gibbsMeasure_eq P _ (by simp only [Nat.succPNat_coe]; omega) j,
    map_gap_eq_map_anchoredGapAt]
  have hg : (fun y => anchoredGapAt (n + 1) y 0) =
      (fun t : ℝ => (n + 2 : ℝ) * t) ∘ (fun y : Fin (n + 1) → ℝ => y 0) :=
    funext (anchoredGapAt_zero_succ n)
  rw [hg, ← Measure.map_map (by fun_prop) (by fun_prop), map_anchoredLaw_first_restrict_density]
  exact map_interval_withDensity_mul_pos (n + 2 : ℝ) (by positivity) _
    (measurable_gapOffsetMarginalDensity P n)

end Riesz1

end
end
