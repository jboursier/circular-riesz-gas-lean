/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryReductionFinalBridge
public import Riesz1.ToMathlib.BoundedCovarianceVariance

/-!
# Statistics of observation-circle representatives

The pullback and centering steps in Lemma 5.3.
Square integrability is derived from the existing circle carrier.
Almost everywhere changes in a representative preserve both the plain
sum and its variance. Centering is a deterministic shift.
-/

public section

open MeasureTheory Filter

namespace Riesz1.Internal

/-- Dilation transports arclength-null changes of representatives. -/
theorem regMicro_pullback_ae_eq (L : Length) {f g : Circle L → ℝ}
    (heq : f =ᵐ[arclength L] g) :
    loopMasterPullback L f =ᵐ[volume] loopMasterPullback L g := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hm : ∀ᵐ z ∂(volume : Measure UnitAddCircle).map
      (AddCircle.equivAddCircle 1 L.val one_ne_zero L.property.ne'), f z = g z := by
    rw [map_circleScale_volume]
    exact Measure.ae_smul_measure heq _
  exact ae_of_ae_map (AddCircle.continuous_equivAddCircle ..).measurable.aemeasurable hm

/-- The plain observation-circle statistic has a second moment. -/
theorem regMicro_plainSum_memLp (P : Parameters) (N : ℕ+) (ℓ : Scale)
    (f : Circle (observationLength ℓ) → ℝ)
    (hf : MemLp (fun z => (f z : ℂ)) 2 (arclength (observationLength ℓ))) :
    MemLp (fun X : Configuration N =>
      ∑ i : Fin (N : ℕ), f ((X.val i/ℓ.val : ℝ) : Circle (observationLength ℓ)))
      2 (gibbsMeasure P N) := by
  have h := memLp_linearStatistic P N
    (memLp_real_of_complex (loopMasterPullback_memLp (observationLength ℓ) ⟨f, hf⟩))
  convert h using 1
  funext X
  unfold linearStatistic
  apply Finset.sum_congr rfl
  intro i _
  rw [loopMasterPullback_coe]
  rfl

/-- Equality of the actual plain statistics follows from equality of
the observation-circle functions almost everywhere. -/
theorem regMicro_plainSum_ae_eq (P : Parameters) (N : ℕ+) (ℓ : Scale)
    {f g : Circle (observationLength ℓ) → ℝ}
    (heq : f =ᵐ[arclength (observationLength ℓ)] g) :
    (fun X : Configuration N =>
      ∑ i : Fin (N : ℕ), f ((X.val i/ℓ.val : ℝ) : Circle (observationLength ℓ))) =ᵐ[gibbsMeasure P N]
    (fun X : Configuration N =>
      ∑ i : Fin (N : ℕ), g ((X.val i/ℓ.val : ℝ) : Circle (observationLength ℓ))) := by
  have h := linearStatistic_ae_eq P N (regMicro_pullback_ae_eq (observationLength ℓ) heq)
  have hk (k : Circle (observationLength ℓ) → ℝ) (X : Configuration N) :
      (∑ i : Fin (N : ℕ), k ((X.val i/ℓ.val : ℝ) : Circle (observationLength ℓ))) =
        linearStatistic (loopMasterPullback (observationLength ℓ) k) X := by
    unfold linearStatistic
    apply Finset.sum_congr rfl
    intro i _
    rw [loopMasterPullback_coe]
    rfl
  filter_upwards [h] with X hx
  rw [hk f X, hk g X]
  exact hx

/-- The mixed fluctuation and plain sum have exactly the same
variance, with arbitrary first-moment certificates. -/
theorem regMicro_mixedStat_variance (P : Parameters) (N : ℕ+) (ℓ : Scale)
    (f : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))})
    (hF : Integrable (mixedStat P N ℓ f) (gibbsMeasure P N))
    (hS : Integrable (fun X : Configuration N =>
      ∑ i : Fin (N : ℕ), f.val ((X.val i/ℓ.val : ℝ) : Circle (loopMasterLength ℓ)))
      (gibbsMeasure P N)) :
    variance (gibbsMeasure P N) (mixedStat P N ℓ f) hF =
      variance (gibbsMeasure P N) (fun X : Configuration N =>
        ∑ i : Fin (N : ℕ), f.val ((X.val i/ℓ.val : ℝ) : Circle (loopMasterLength ℓ))) hS := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  let c := (N : ℝ) * ∫ z, loopMasterPullback (loopMasterLength ℓ) f.val z
  have he : mixedStat P N ℓ f = fun X : Configuration N =>
      (∑ i : Fin (N : ℕ), f.val ((X.val i/ℓ.val : ℝ) : Circle (loopMasterLength ℓ))) - c := by
    funext X
    unfold mixedStat fluctuation linearStatistic
    dsimp only [c]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [loopMasterPullback_coe]
    rfl
  exact (auxiliary_variance_congr hF (hS.sub (integrable_const c))
    (Eventually.of_forall (congrFun he))).trans (frozenVariance_sub_const hS c)

end Riesz1.Internal
