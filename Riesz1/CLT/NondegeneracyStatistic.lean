/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.NondegeneracyZero
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The statistic and Gaussian in the zero-variance cases

The almost sure assertions of the nondegeneracy argument for Theorem 3.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Riesz1

namespace Internal

lemma nondegeneracy_scaled_zero (p : Profile)
    (hz : zeroExtension p =ᵐ[volume] fun _ => 0) (a : Scale) :
    (fun t : ℝ => zeroExtension p (t / a.val)) =ᵐ[volume] fun _ => 0 := by
  have h := (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ)
    (inv_ne_zero a.property.1.ne')).ae_eq_comp hz
  simpa only [smul_eq_mul, Function.comp_def, div_eq_inv_mul] using h

lemma nondegeneracy_lift_zero {g : ℝ → ℝ} (hg : g =ᵐ[volume] fun _ => 0) :
    AddCircle.liftIoc 1 (-(1 / 2 : ℝ)) g =ᵐ[volume] fun _ => 0 := by
  have hmp : MeasurePreserving
      (fun x : UnitAddCircle => ((AddCircle.equivIoc 1 (-(1 / 2 : ℝ)) x).val))
      volume (volume.restrict (Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1))) :=
    (measurePreserving_subtype_coe measurableSet_Ioc).comp
      (AddCircle.measurePreserving_equivIoc (T := 1) (a := -(1 / 2 : ℝ)))
  change (fun x : UnitAddCircle => g ((AddCircle.equivIoc 1 (-(1 / 2 : ℝ)) x).val))
    =ᵐ[volume] fun _ => 0
  have hh : ∀ᵐ t : ℝ ∂volume.restrict (Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)),
      g t = 0 := ae_restrict_of_ae hg
  exact hmp.quasiMeasurePreserving.ae (p := fun y : ℝ => g y = 0) hh

end Internal

/-- Null changes of a profile on the line remain null after scaling and
restriction to the central circle representative. -/
theorem testAtScale_ae_zero_of_zeroExtension (p : Profile)
    (hz : zeroExtension p =ᵐ[volume] fun _ => 0) (a : Scale) :
    testAtScale p a =ᵐ[volume] fun _ => 0 := by
  have : Fact (0 < unitLength.val) := ⟨unitLength.property⟩
  have hlift : AddCircle.liftIoc 1 (-(1 / 2 : ℝ))
      (fun t => zeroExtension p (t / a.val)) =ᵐ[volume] fun _ => 0 :=
    Internal.nondegeneracy_lift_zero (Internal.nondegeneracy_scaled_zero p hz a)
  have hnull : ∀ᵐ x : UnitAddCircle, x ≠ (((1 / 2 : ℝ) : UnitAddCircle)) := by
    refine ae_iff.mpr ?_
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using volume_singleton_half
  filter_upwards [hlift, hnull] with x hx hne
  have hxrep : ((centralRep unitLength x : ℝ) : UnitAddCircle) = x := by
    unfold centralRep
    exact AddCircle.coe_equivIco
  have hmem := (AddCircle.equivIco unitLength.val (-unitLength.val / 2) x).property
  change -(1 : ℝ) / 2 ≤ centralRep unitLength x ∧
    centralRep unitLength x < -(1 : ℝ) / 2 + 1 at hmem
  have hrepne : centralRep unitLength x ≠ -(1 / 2 : ℝ) := by
    intro he
    apply hne
    rw [← hxrep, he, ← AddCircle.coe_add_period (1 : ℝ) (-(1 / 2 : ℝ))]
    norm_num
  have habs : |centralRep unitLength x| < 1 / 2 :=
    abs_lt.mpr ⟨by
      have := lt_of_le_of_ne hmem.1 (show -(1 : ℝ) / 2 ≠ centralRep unitLength x by
        intro he; apply hrepne; linarith)
      linarith, by linarith [hmem.2]⟩
  rw [← hxrep, testAtScale_coe_of_abs_lt p habs]
  rw [← hxrep, AddCircle.liftIoc_coe_apply] at hx
  · exact hx
  · exact ⟨by linarith [(abs_lt.mp habs).1], by linarith [(abs_lt.mp habs).2]⟩

/-- A constant almost everywhere test has zero fluctuation almost surely. -/
theorem fluctuation_ae_zero_of_ae_const (P : Parameters) (N : ℕ+)
    (f : {f : UnitAddCircle → ℝ // Integrable f volume}) {c : ℝ}
    (hf : f.val =ᵐ[volume] fun _ => c) :
    (fun X => fluctuation f X) =ᵐ[gibbsMeasure P N] fun _ => 0 := by
  have hmean : ∫ x, f.val x = c := by
    rw [integral_congr_ae hf]
    simp [Measure.real]
  filter_upwards [linearStatistic_ae_eq P N hf] with X hX
  change linearStatistic f.val X - (N : ℝ) * ∫ x, f.val x = 0
  rw [hX, hmean]
  simp [linearStatistic, nsmul_eq_mul]

/-- In the macroscopic zero-variance case the normalized statistic
is zero almost surely, for every particle number. -/
theorem clt_nondegeneracy_macroscopic_statistic (P : Parameters) (p : Profile)
    (hz : circleVariance P p ⟨1, by norm_num⟩ = 0)
    (ell : Scales) (hell : ∀ N, (ell N).val = 1) (N : ℕ+) :
    normalizedStatistic P p ell N =ᵐ[gibbsMeasure P N] fun _ => 0 := by
  obtain ⟨c, hc⟩ := (clt_nondegeneracy_macroscopic_zero P p).mp hz
  have ht : testAtScale p (ell N) =ᵐ[volume] fun _ => c := by
    simpa only [testAtScale, hell N, ite_true] using hc
  filter_upwards [fluctuation_ae_zero_of_ae_const P N
    ⟨testAtScale p (ell N), testAtScaleL1 p (ell N)⟩ ht] with X hX
  simp only [normalizedStatistic, hX, mul_zero]

/-- In the compact zero-variance case the normalized statistic
is zero almost surely at every scale, including scale one. -/
theorem clt_nondegeneracy_compact_statistic (P : Parameters) (p : Profile)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : RepresentsZeroExtension p f)
    (hz : lineVariance P f = 0) (ell : Scales) (N : ℕ+) :
    normalizedStatistic P p ell N =ᵐ[gibbsMeasure P N] fun _ => 0 := by
  have ht := testAtScale_ae_zero_of_zeroExtension p
    ((clt_nondegeneracy_compact_zero P p f hf).mp hz) (ell N)
  filter_upwards [fluctuation_ae_zero_of_ae_const P N
    ⟨testAtScale p (ell N), testAtScaleL1 p (ell N)⟩ ht] with X hX
  simp only [normalizedStatistic, hX, mul_zero]

/-- The Gaussian comparison at variance zero is concentrated at zero,
as required in the two zero-variance cases. -/
theorem clt_nondegeneracy_gaussian_zero :
    (fun x : ℝ => x) =ᵐ[normalLaw 0] fun _ => 0 := by
  rw [normalLaw, ProbabilityTheory.gaussianReal_zero_var]
  exact (ae_dirac_iff (measurableSet_eq_fun measurable_id measurable_const)).mpr rfl

end Riesz1
