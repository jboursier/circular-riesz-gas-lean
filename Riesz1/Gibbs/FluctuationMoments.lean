/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Gibbs.UniformMarginals
public import Riesz1.Frozen.LinearStatistic
public import Riesz1.Frozen.Fluctuation

/-!
# Moments of the linear statistic and of the fluctuation under the Gibbs law

For `f ∈ L²(𝕋)`, the linear statistic `∑ᵢ f([Xᵢ])` is square
integrable under the Gibbs law, and the fluctuation `Fluct_N[f]` has mean zero. The proof uses
that each `[Xᵢ]` has law `dx` (`map_coord_gibbsMeasure`), so each summand is square integrable with
integral `∫ f`. A change of `f` on a Lebesgue null set changes the statistic only on a null set of
configurations.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Riesz1

/-- The circle coordinate `[X_i]` pushes the Gibbs law to Lebesgue measure on the circle, so an
`L²` function of it is square integrable under the Gibbs law. -/
lemma memLp_comp_coord (P : Parameters) (N : ℕ+) (i : Fin (N : ℕ)) {f : UnitAddCircle → ℝ}
    (hf : MemLp f 2 volume) :
    MemLp (fun X : Configuration N => f ((X.val i : ℝ) : UnitAddCircle)) 2 (gibbsMeasure P N) := by
  have hmap := map_coord_gibbsMeasure P N i
  have hA : AEStronglyMeasurable f
      ((gibbsMeasure P N).map (fun X : Configuration N => ((X.val i : ℝ) : UnitAddCircle))) := by
    rw [hmap]
    exact hf.aestronglyMeasurable
  have hL : MemLp f 2
      ((gibbsMeasure P N).map (fun X : Configuration N => ((X.val i : ℝ) : UnitAddCircle))) := by
    rw [hmap]
    exact hf
  exact (memLp_map_measure_iff hA (measurable_coord N i).aemeasurable).1 hL

/-- **Square integrability.** The linear statistic of an `L²` function is
square integrable under the Gibbs law. -/
theorem memLp_linearStatistic (P : Parameters) (N : ℕ+) {f : UnitAddCircle → ℝ}
    (hf : MemLp f 2 volume) :
    MemLp (fun X : Configuration N => linearStatistic f X) 2 (gibbsMeasure P N) := by
  unfold linearStatistic
  exact memLp_finsetSum Finset.univ fun i _ => memLp_comp_coord P N i hf

/-- The linear statistic of an `L²` function is integrable under the Gibbs law. -/
lemma integrable_linearStatistic (P : Parameters) (N : ℕ+) {f : UnitAddCircle → ℝ}
    (hf : MemLp f 2 volume) :
    Integrable (fun X : Configuration N => linearStatistic f X) (gibbsMeasure P N) := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  exact (memLp_linearStatistic P N hf).integrable one_le_two

/-- Each circle coordinate has the integral of `f` under the Gibbs law. -/
lemma integral_comp_coord (P : Parameters) (N : ℕ+) (i : Fin (N : ℕ)) {f : UnitAddCircle → ℝ}
    (hf : MemLp f 2 volume) :
    ∫ X : Configuration N, f ((X.val i : ℝ) : UnitAddCircle) ∂(gibbsMeasure P N) = ∫ x, f x := by
  have hA : AEStronglyMeasurable f
      ((gibbsMeasure P N).map (fun X : Configuration N => ((X.val i : ℝ) : UnitAddCircle))) := by
    rw [map_coord_gibbsMeasure]
    exact hf.aestronglyMeasurable
  rw [← integral_map (measurable_coord N i).aemeasurable hA, map_coord_gibbsMeasure]

/-- The mean of the linear statistic is `N` times the mean of `f`. -/
lemma integral_linearStatistic (P : Parameters) (N : ℕ+) {f : UnitAddCircle → ℝ}
    (hf : MemLp f 2 volume) :
    ∫ X, linearStatistic f X ∂(gibbsMeasure P N) = (N : ℝ) * ∫ x, f x := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  unfold linearStatistic
  rw [integral_finsetSum _ fun i _ => (memLp_comp_coord P N i hf).integrable one_le_two]
  rw [Finset.sum_congr rfl fun i _ => integral_comp_coord P N i hf]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Mean-zero fluctuations.** The fluctuation `Fluct_N[f]` of an `L²`
function has mean zero under the Gibbs law. -/
theorem integral_fluctuation_eq_zero (P : Parameters) (N : ℕ+) {f : UnitAddCircle → ℝ}
    (hf : MemLp f 2 volume) :
    ∫ X, fluctuation ⟨f, hf.integrable one_le_two⟩ X ∂(gibbsMeasure P N) = 0 := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  show ∫ X, (linearStatistic f X - (N : ℝ) * ∫ x, f x) ∂(gibbsMeasure P N) = 0
  rw [integral_sub (integrable_linearStatistic P N hf) (integrable_const _),
    integral_linearStatistic P N hf, integral_const]
  simp

/-- **Almost-everywhere invariance.** If `f = g` almost everywhere on the
circle, then the linear statistics of `f` and `g` agree almost surely under the Gibbs law. -/
theorem linearStatistic_ae_eq (P : Parameters) (N : ℕ+) {f g : UnitAddCircle → ℝ}
    (hfg : f =ᵐ[volume] g) :
    ∀ᵐ X ∂(gibbsMeasure P N), linearStatistic f X = linearStatistic g X := by
  have hi : ∀ i : Fin (N : ℕ), ∀ᵐ X ∂(gibbsMeasure P N),
      f ((X.val i : ℝ) : UnitAddCircle) = g ((X.val i : ℝ) : UnitAddCircle) := by
    intro i
    refine ae_of_ae_map (p := fun y => f y = g y) (measurable_coord N i).aemeasurable ?_
    rw [map_coord_gibbsMeasure]
    exact hfg
  filter_upwards [ae_all_iff.2 hi] with X hX
  unfold linearStatistic
  exact Finset.sum_congr rfl fun i _ => hX i

end Riesz1

end
end
