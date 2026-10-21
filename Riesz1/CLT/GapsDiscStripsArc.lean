/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Bridges.ExplicitFormulasCentred
public import Riesz1.Bridges.IndicatorArc
public import Riesz1.Kernel.AdmissibleExamplesCompact
public import Riesz1.Kernel.AdmissibilityRegularityVariance
public import Mathlib.MeasureTheory.Group.AddCircle
public import Riesz1.Frozen.TestAtScale
public import Riesz1.Frozen.CircleVariance
public import Riesz1.Frozen.CountVariance
public import Riesz1.Frozen.ArcCount
public import Riesz1.Frozen.RescaledProfile

/-!
# Arcs at scale `ℓ` for the boundary strips

Part of the proof of Corollary 1. The profile `1_{(-1/4,1/4)}` at scale `ℓ`
is the indicator of the open arc of half-width `ℓ/4` about `0`, and its circle variance is
`countVariance P ℓ^{-s} V_s(ℓ/2)` by the explicit formula for indicators of arcs. An open arc of
length `t` is `arcIndicator c (t/2)`, so the centred count of the lemma is the fluctuation of this
indicator.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz1

/-- The integral of the indicator of an arc of half-width `a` is its length `2a`, for
`0 ≤ a ≤ 1/2`. -/
lemma integral_arcIndicator (c : UnitAddCircle) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) :
    ∫ x, arcIndicator c a x = 2 * a := by
  have hind : arcIndicator c a = (Metric.ball c a).indicator 1 := by
    funext x
    simp only [arcIndicator, Set.indicator, Metric.mem_ball, Pi.one_apply]
  rw [hind, integral_indicator_one measurableSet_ball, Measure.real]
  have hvol : volume (Metric.ball c a) = volume (Metric.closedBall c a) :=
    measure_congr (AddCircle.closedBall_ae_eq_ball).symm
  rw [hvol, AddCircle.volume_closedBall, ENNReal.toReal_ofReal (le_min zero_le_one (by linarith))]
  rw [min_eq_right (by linarith)]

/-- For a real `y` with `|y| < 1/2`, the class of `y` on the unit circle has distance `|y|`
from `0`. -/
lemma dist_coe_zero_eq_abs {y : ℝ} (hy : |y| < 1 / 2) :
    dist (y : UnitAddCircle) 0 = |y| := by
  rw [dist_zero_right, UnitAddCircle.norm_eq]
  have hr : round y = 0 :=
    round_eq_zero_iff.mpr ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  rw [hr]
  simp

/-- The distance from a point of the unit circle to `0` is the absolute value of its central
representative in `[-1/2, 1/2)`. -/
lemma dist_zero_eq_abs_centralRep (x : UnitAddCircle) :
    dist x 0 = |centralRep unitLength x| := by
  obtain ⟨x0, rfl⟩ := exists_real_coe x
  obtain ⟨n, hn⟩ := centralRep_coe_eq unitLength x0
  have hn' : centralRep unitLength (x0 : UnitAddCircle) = x0 - n * 1 := hn
  have hmem := centralRep_mem_Ico unitLength (x0 : UnitAddCircle)
  rw [hn'] at hmem
  simp only [Set.mem_Ico, unitLength] at hmem
  have hround : round x0 = n := by
    rw [round_eq, Int.floor_eq_iff]
    constructor <;> linarith [hmem.1, hmem.2]
  have key : |centralRep unitLength (x0 : UnitAddCircle)| = |x0 - n| := by
    rw [hn', mul_one]
  rw [dist_zero_right, UnitAddCircle.norm_eq, hround, key]

/-- The arc profile of the strip lemma: the open arc of half-width `1/4` about `0`. -/
def gapsArcProfile : Profile :=
  ⟨arcIndicator 0 (1 / 4), memLp_arcIndicator 0 (1 / 4)⟩

/-- At every scale `ℓ` in `(0, 1]`, the profile `gapsArcProfile` rescales to the open arc of
half-width `ℓ/4`. -/
lemma testAtScale_gapsArcProfile (ell : Scale) :
    testAtScale gapsArcProfile ell = arcIndicator 0 (ell.val / 4) := by
  have hℓ : 0 < ell.val := ell.property.1
  funext x
  unfold testAtScale
  by_cases h1 : ell.val = 1
  · simp only [h1, ↓reduceIte]
    norm_num
    rfl
  · simp only [h1, ↓reduceIte]
    unfold rescaledProfile zeroExtension
    set c := centralRep unitLength x with hc
    have hdist : dist x 0 = |c| := dist_zero_eq_abs_centralRep x
    unfold arcIndicator
    rw [hdist]
    by_cases hy : |c / ell.val| < 1 / 2
    · simp only [hy, ↓reduceIte]
      have hyx : gapsArcProfile.val ((c / ell.val : ℝ) : UnitAddCircle) =
          if dist ((c / ell.val : ℝ) : UnitAddCircle) 0 < 1 / 4 then 1 else 0 := rfl
      rw [hyx, dist_coe_zero_eq_abs hy, abs_div, abs_of_pos hℓ]
      have hcond : |c| / ell.val < 1 / 4 ↔ |c| < ell.val / 4 := by
        rw [div_lt_iff₀ hℓ]
        constructor <;> intro h <;> linarith
      simp only [hcond]
    · simp only [hy, ↓reduceIte]
      have hge : ell.val / 2 ≤ |c| := by
        have h' : 1 / 2 ≤ |c / ell.val| := not_lt.mp hy
        rw [abs_div, abs_of_pos hℓ, le_div_iff₀ hℓ] at h'
        linarith
      have hnot : ¬ |c| < ell.val / 4 := fun h => by linarith
      simp only [hnot, ↓reduceIte]

/-- The circle variance of the arc profile at scale `ℓ`: the prefactor `(2π)^{1-s}/(2β c_s)` times
`ℓ^{-s}` times the seminorm of the indicator of the open arc of half-width `ℓ/4`, which equals
`v_s ℓ^{-s} V_s(ℓ/2)` with the count constant `v_s = countVariance P`. -/
lemma circleVariance_gapsArcProfile (P : Parameters) (ell : Scale) :
    (circleVariance P gapsArcProfile ell).toReal =
      ell.val ^ (-P.val.2) * countVariance P *
        periodicZeta (parametersExponent P) ((ell.val / 2 : ℝ) : UnitAddCircle) := by
  have hℓ : 0 < ell.val := ell.property.1
  have hℓ1 : ell.val ≤ 1 := ell.property.2
  obtain ⟨_, _, ⟨_, hform⟩, _, hunc⟩ :=
    explicit_formulas_indicator_centered (parametersExponent P) P.val.1 P.property.1 0
      (ell.val / 4) (by linarith) (by linarith)
  have hsub : (⟨fun x => (testAtScale gapsArcProfile ell x : ℂ),
      testAtScaleL2 gapsArcProfile ell⟩ : {g : UnitAddCircle → ℂ // MemLp g 2 volume}) =
        ⟨fun x => (arcIndicator 0 (ell.val / 4) x : ℂ), memLp_arcIndicator 0 (ell.val / 4)⟩ :=
    Subtype.ext (by simp only [testAtScale_gapsArcProfile])
  have hpref : 0 ≤ (2 * Real.pi) ^ (1 - P.val.2) /
      (2 * P.val.1 * rieszConstant (parametersExponent P)) := by
    have := rieszConstant_pos (parametersExponent P)
    have := P.property.1
    positivity
  have hpos : 0 ≤ ell.val ^ (-P.val.2) := Real.rpow_nonneg hℓ.le _
  have hpe : (parametersExponent P).val = P.val.2 := rfl
  rw [hpe] at hunc hform
  unfold circleVariance
  rw [hsub, ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hpref hpos), hunc]
  have hV : ((2 * (ell.val / 4) : ℝ) : UnitAddCircle) = ((ell.val / 2 : ℝ) : UnitAddCircle) := by
    congr 1
    ring
  rw [hV] at hform
  unfold countVariance
  rw [show 2 * P.val.1 * Real.pi * P.val.2 = 2 * Real.pi * P.val.1 * P.val.2 by ring]
  linear_combination (ell.val ^ (-P.val.2)) * hform

end Riesz1

end
end
