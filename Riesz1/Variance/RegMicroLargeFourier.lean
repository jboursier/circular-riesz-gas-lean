/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleFourierSumComparison
public import Riesz1.Variance.RegMicroFinalStatistics
public import Riesz1.ToMathlib.VarianceFrozenIntegral

/-!
# Fourier comparison for Gibbs second moments

The uniform common rotation transfers a
modewise Fourier comparison to Gibbs second moments. This supplies
the variance contraction needed for the families in Lemma 5.3.
The argument includes one particle and requires no marked points.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1.Internal

/-- Conditional square mass given the anchored particle offsets. The
inner circle integral is integrable in the offsets before it is used. -/
theorem regMicro_rotation_secondMoment (P : Parameters) (n : ℕ)
    (f : UnitAddCircle → ℝ) (hf : MemLp f 2 volume) :
    (∫ X : Configuration n.succPNat, (linearStatistic f X)^2 ∂gibbsMeasure P n.succPNat) =
      ∫ y, (∫ z : UnitAddCircle,
        (∑ i : Fin (n.succPNat : ℕ), f (z+(anchorVector y i : UnitAddCircle)))^2)
          ∂anchoredLaw P n ∧
    Integrable (fun y => ∫ z : UnitAddCircle,
      (∑ i : Fin (n.succPNat : ℕ), f (z+(anchorVector y i : UnitAddCircle)))^2)
        (anchoredLaw P n) := by
  have : IsProbabilityMeasure (anchoredLaw P n) := isProbabilityMeasure_anchoredLaw P n
  let μ := volume.restrict (Ico (0 : ℝ) 1)
  let Φ : ℝ × (Fin n → ℝ) → ℝ := fun p =>
    ∑ i : Fin (n.succPNat : ℕ), f ((p.1+anchorVector p.2 i : ℝ) : UnitAddCircle)
  have hΦ : MemLp Φ 2 (μ.prod (anchoredLaw P n)) := by
    apply memLp_finsetSum Finset.univ
    intro i _
    have hm := map_circle_uniform_shift (fun y : Fin n → ℝ => anchorVector y i)
      ((measurable_pi_apply i).comp (measurable_anchorVector n)) (anchoredLaw P n)
    have hfm : MemLp f 2 ((μ.prod (anchoredLaw P n)).map
        (fun p => ((p.1+anchorVector p.2 i : ℝ) : UnitAddCircle))) := by
      rw [hm]
      exact hf
    exact hfm.comp_of_map (measurable_coe_circle.comp
      (measurable_fst.add (((measurable_pi_apply i).comp
        (measurable_anchorVector n)).comp measurable_snd))).aemeasurable
  have hinner (y : Fin n → ℝ) :
      (∫ t, Φ (t,y)^2 ∂μ) = ∫ z : UnitAddCircle,
        (∑ i : Fin (n.succPNat : ℕ), f (z+(anchorVector y i : UnitAddCircle)))^2 := by
    let F := fun z : UnitAddCircle =>
      ∑ i : Fin (n.succPNat : ℕ), f (z+(anchorVector y i : UnitAddCircle))
    have hF : MemLp F 2 volume := memLp_finsetSum Finset.univ fun i _ =>
      hf.comp_measurePreserving (measurePreserving_add_right volume _)
    have hm : μ.map (fun t : ℝ => (t : UnitAddCircle)) = volume := by
      simpa only [add_zero] using map_circle_translate_uniform 0
    have hh := integral_map measurable_coe_circle.aemeasurable
      (show AEStronglyMeasurable (fun z => F z^2)
        (μ.map (fun t : ℝ => (t : UnitAddCircle))) by
        rw [hm]; exact hF.integrable_sq.aestronglyMeasurable)
    rw [hm] at hh
    simpa only [Φ, F, AddCircle.coe_add] using hh.symm
  have hchange := integral_map (measurable_anchorCoords_config n).aemeasurable
    (show AEStronglyMeasurable (fun p => Φ p^2)
      ((gibbsMeasure P n.succPNat).map (fun X => anchorCoords n X.val)) by
      rw [map_gibbsMeasure_anchorCoords]
      exact hΦ.integrable_sq.aestronglyMeasurable)
  rw [map_gibbsMeasure_anchorCoords] at hchange
  have hfun (X : Configuration n.succPNat) : Φ (anchorCoords n X.val) = linearStatistic f X := by
    unfold Φ linearStatistic
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact congrArg (fun t : ℝ => (t : UnitAddCircle)) (apply_eq_anchor_add n X.val i).symm
  constructor
  · calc
      _ = ∫ p, Φ p^2 ∂μ.prod (anchoredLaw P n) := by simpa only [hfun] using hchange.symm
      _ = ∫ y, ∫ t, Φ (t,y)^2 ∂μ ∂anchoredLaw P n :=
        integral_prod_symm _ hΦ.integrable_sq
      _ = _ := integral_congr_ae (Eventually.of_forall hinner)
  · exact hΦ.integrable_sq.integral_prod_right.congr (Eventually.of_forall hinner)

/-- Every modewise comparison of squared Fourier coefficients gives
the same comparison of uncentered Gibbs second moments. -/
theorem regMicro_secondMoment_le_of_circleCoeff (P : Parameters) (N : ℕ+)
    (f g : UnitAddCircle → ℝ)
    (hf : MemLp (fun z => (f z : ℂ)) 2 volume)
    (hg : MemLp (fun z => (g z : ℂ)) 2 volume)
    (D : ℝ) (hD : 0 ≤ D)
    (hc : ∀ k : ℤ, ‖circleCoeff f k‖^2 ≤ D*‖circleCoeff g k‖^2) :
    (∫ X : Configuration N, (linearStatistic f X)^2 ∂gibbsMeasure P N) ≤
      D*∫ X : Configuration N, (linearStatistic g X)^2 ∂gibbsMeasure P N := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n.succPNat :=
    ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
  obtain ⟨he, hi⟩ := regMicro_rotation_secondMoment P n f (memLp_real_of_complex hf)
  obtain ⟨he', hi'⟩ := regMicro_rotation_secondMoment P n g (memLp_real_of_complex hg)
  rw [he, he', ← integral_const_mul]
  apply integral_mono hi (hi'.const_mul D)
  intro y
  exact integral_sq_sum_translate_le_of_circleCoeff
    (fun i => (anchorVector y i : UnitAddCircle)) f g hf hg D hD hc

/-- For zero-mean tests the comparison is a comparison of the actual
extended variances, with finiteness supplied by their carriers. -/
theorem regMicro_variance_le_of_circleCoeff (P : Parameters) (N : ℕ+)
    (f g : UnitAddCircle → ℝ)
    (hf : MemLp (fun z => (f z : ℂ)) 2 volume)
    (hg : MemLp (fun z => (g z : ℂ)) 2 volume)
    (hmf : (∫ z, f z) = 0) (hmg : (∫ z, g z) = 0)
    (D : ℝ) (hD : 0 ≤ D)
    (hc : ∀ k : ℤ, ‖circleCoeff f k‖^2 ≤ D*‖circleCoeff g k‖^2) :
    variance (gibbsMeasure P N) (linearStatistic f)
        ((memLp_linearStatistic P N (memLp_real_of_complex hf)).integrable one_le_two) ≤
      ENNReal.ofReal D * variance (gibbsMeasure P N) (linearStatistic g)
        ((memLp_linearStatistic P N (memLp_real_of_complex hg)).integrable one_le_two) := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  rw [variance_eq_ofReal_integral_sq _ _ (memLp_linearStatistic P N (memLp_real_of_complex hf)),
    variance_eq_ofReal_integral_sq _ _ (memLp_linearStatistic P N (memLp_real_of_complex hg)),
    integral_linearStatistic P N (memLp_real_of_complex hf),
    integral_linearStatistic P N (memLp_real_of_complex hg), hmf, hmg]
  simp only [mul_zero, sub_zero]
  rw [← ENNReal.ofReal_mul hD]
  exact ENNReal.ofReal_le_ofReal (regMicro_secondMoment_le_of_circleCoeff P N f g hf hg D hD hc)

end Riesz1.Internal
