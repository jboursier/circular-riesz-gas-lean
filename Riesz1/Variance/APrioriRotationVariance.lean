/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.GapLawMoments
public import Riesz1.ToMathlib.Moments.SizeBiasedVariance

/-!
# Size-biased variance on the anchored law

Part of Lemma 5.2 (the rotation part), variance claim and mass claim. The anchored law `μ*` is the
image of the Gibbs law under the anchored coordinates `y_i = x_i - x_1` (labels counted from zero),
and the size-biasing weight is `w(y) = N y_2`, the paper's `y_2` being the coordinate of label two.

* `integral_sizeBiasWeight_rotAnchoredLaw`: `E_{μ*} w = 1`, the mass claim.
* `variance_sizeBiased_anchored`: `Var_{wμ*}(T) ≤ κ Var_{μ*}(T) + 4M² E_{μ*}[w 1_{w>κ}]` for every
  bounded measurable `T` on the anchored coordinates, with `|T| ≤ M` and `κ > 0`.

The general inequality is `Riesz1.variance_sizeBiased_le`. Its weight must be nonnegative
everywhere, so it is applied to `max(w, 0)`, which equals `w` on the support of `μ*` and gives
the same density `ENNReal.ofReal ∘ w`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace Riesz1

/-- The anchored coordinates `y_i = x_i - x_1` of a configuration, with labels counted from zero. -/
noncomputable def rotAnchorVec (N : ℕ+) (X : Configuration N) : Fin (N : ℕ) → ℝ :=
  fun i => cyclicLift X (i : ℕ) - cyclicLift X 0

/-- The anchored law `μ* = (Anch_N)_# dGi` on the anchored coordinates. -/
noncomputable def rotAnchoredLaw (P : Parameters) (N : ℕ+) : Measure (Fin (N : ℕ) → ℝ) :=
  (gibbsMeasure P N).map (rotAnchorVec N)

/-- The size-biasing weight `w(y) = N y_2` of the rotation part of Lemma 5.2, where the
paper's `y_2` is the coordinate of label two, that is index one. -/
noncomputable def sizeBiasWeight (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (y : Fin (N : ℕ) → ℝ) : ℝ :=
  ((N : ℕ) : ℝ) * y ⟨1, by omega⟩

/-- The anchored coordinates are measurable. -/
theorem measurable_rotAnchorVec (N : ℕ+) : Measurable (rotAnchorVec N) :=
  measurable_pi_iff.mpr fun _ => (measurable_cyclicLift _).sub (measurable_cyclicLift _)

/-- The size-biasing weight is measurable. -/
theorem measurable_sizeBiasWeight (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    Measurable (sizeBiasWeight N hN) :=
  measurable_const.mul (measurable_pi_apply _)

/-- The anchored law is a probability measure. -/
instance isProbabilityMeasure_rotAnchoredLaw (P : Parameters) (N : ℕ+) :
    IsProbabilityMeasure (rotAnchoredLaw P N) := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  unfold rotAnchoredLaw
  infer_instance

/-- On the anchored coordinates, the weight is the gap `N(x_2 - x_1)` after the origin label. -/
theorem sizeBiasWeight_anchorVec (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (X : Configuration N) :
    sizeBiasWeight N hN (rotAnchorVec N X) = gap X 0 := by
  unfold sizeBiasWeight rotAnchorVec gap
  simp

/-- **Mass claim** (rotation part of Lemma 5.2): the size-biasing weight has unit mean
under the anchored law, `E_{μ*} w = 1`. -/
theorem integral_sizeBiasWeight_rotAnchoredLaw (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    ∫ y, sizeBiasWeight N hN y ∂(rotAnchoredLaw P N) = 1 := by
  unfold rotAnchoredLaw
  rw [integral_map (measurable_rotAnchorVec N).aemeasurable
    (measurable_sizeBiasWeight N hN).aestronglyMeasurable]
  simp only [sizeBiasWeight_anchorVec]
  exact integral_gap_gibbsMeasure P N hN 0

/-- The size-biasing weight is integrable under the anchored law. -/
theorem integrable_sizeBiasWeight_rotAnchoredLaw (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    Integrable (sizeBiasWeight N hN) (rotAnchoredLaw P N) := by
  unfold rotAnchoredLaw
  rw [integrable_map_measure (measurable_sizeBiasWeight N hN).aestronglyMeasurable
    (measurable_rotAnchorVec N).aemeasurable]
  have h : (sizeBiasWeight N hN ∘ rotAnchorVec N) = fun X => gap X 0 :=
    funext fun X => sizeBiasWeight_anchorVec N hN X
  rw [h]
  exact integrable_gap P N 0

/-- The positive part of the weight has unit mean under the anchored law. -/
theorem integral_max_sizeBiasWeight_rotAnchoredLaw (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    ∫ y, max (sizeBiasWeight N hN y) 0 ∂(rotAnchoredLaw P N) = 1 := by
  unfold rotAnchoredLaw
  rw [integral_map (measurable_rotAnchorVec N).aemeasurable
    ((measurable_sizeBiasWeight N hN).max measurable_const).aestronglyMeasurable]
  have h : ∀ X : Configuration N, max (sizeBiasWeight N hN (rotAnchorVec N X)) 0 = gap X 0 :=
    fun X => by rw [sizeBiasWeight_anchorVec, max_eq_left (gap_pos X 0).le]
  simp only [h]
  exact integral_gap_gibbsMeasure P N hN 0

/-- **Variance claim** (rotation part of Lemma 5.2). For every bounded measurable `T` on
the anchored coordinates, with `|T| ≤ M` and `κ > 0`,
`Var_{wμ*}(T) ≤ κ Var_{μ*}(T) + 4M² E_{μ*}[w 1_{w > κ}]`, where `w = N y_2` and
`wμ*` has density `ENNReal.ofReal ∘ w` with respect to `μ*`. -/
theorem variance_sizeBiased_anchored (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    {T : (Fin (N : ℕ) → ℝ) → ℝ} (hT : Measurable T) {M : ℝ} (hTM : ∀ y, |T y| ≤ M)
    {κ : ℝ} (hκ : 0 < κ) :
    variance T ((rotAnchoredLaw P N).withDensity fun y => ENNReal.ofReal (sizeBiasWeight N hN y)) ≤
      κ * variance T (rotAnchoredLaw P N) + 4 * M ^ 2 *
        ∫ y in {y | κ < sizeBiasWeight N hN y}, sizeBiasWeight N hN y ∂(rotAnchoredLaw P N) := by
  set w := sizeBiasWeight N hN with hw_def
  have hwmeas : Measurable w := measurable_sizeBiasWeight N hN
  have hwm : Measurable (fun y => max (w y) 0) := hwmeas.max measurable_const
  have hofReal : ∀ x : ℝ, ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
    intro x
    rcases le_total x 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
    · rw [max_eq_left h]
  have hdens : (rotAnchoredLaw P N).withDensity (fun y => ENNReal.ofReal (w y)) =
      (rotAnchoredLaw P N).withDensity (fun y => ENNReal.ofReal (max (w y) 0)) := by
    have hfun : (fun y => ENNReal.ofReal (w y)) = (fun y => ENNReal.ofReal (max (w y) 0)) :=
      funext fun y => hofReal (w y)
    rw [hfun]
  have hwint' : Integrable (fun y => max (w y) 0) (rotAnchoredLaw P N) :=
    (integrable_sizeBiasWeight_rotAnchoredLaw P N hN).pos_part
  have hset : {y | κ < max (w y) 0} = {y | κ < w y} := by
    ext y
    constructor
    · intro h
      have h0 : κ < max (w y) 0 := h
      rcases lt_max_iff.1 h0 with h' | h'
      · exact h'
      · exact absurd h' (not_lt.2 hκ.le)
    · intro h
      have h0 : κ < w y := h
      exact lt_max_of_lt_left h0
  have hint : ∫ y in {y | κ < w y}, max (w y) 0 ∂(rotAnchoredLaw P N) =
      ∫ y in {y | κ < w y}, w y ∂(rotAnchoredLaw P N) := by
    refine setIntegral_congr_fun ?_ fun y hy => ?_
    · exact measurableSet_lt measurable_const hwmeas
    · have hy' : κ < w y := hy
      exact max_eq_left (by linarith)
  rw [hdens]
  calc variance T ((rotAnchoredLaw P N).withDensity fun y => ENNReal.ofReal (max (w y) 0))
      ≤ κ * variance T (rotAnchoredLaw P N) + 4 * M ^ 2 *
          ∫ y in {y | κ < max (w y) 0}, max (w y) 0 ∂(rotAnchoredLaw P N) :=
        variance_sizeBiased_le (rotAnchoredLaw P N) hwm (fun y => le_max_right _ _) hwint'
          (integral_max_sizeBiasWeight_rotAnchoredLaw P N hN) hT hTM hκ
    _ = κ * variance T (rotAnchoredLaw P N) + 4 * M ^ 2 *
        ∫ y in {y | κ < w y}, w y ∂(rotAnchoredLaw P N) := by
        rw [hset, hint]

end Riesz1

end
