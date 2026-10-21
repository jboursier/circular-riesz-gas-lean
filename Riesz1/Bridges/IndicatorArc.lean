/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.ArcIndicator
public import Riesz1.Kernel.ExplicitFormulasIndicatorCoeffs
public import Riesz1.Kernel.PeriodicZetaFourier

/-!
# Bridge: the arc indicators `indicatorArc` and `arcIndicator`

The function `indicatorArc a` is the indicator of the open arc `(-a, a)` on `UnitAddCircle`. The
function `arcIndicator center a` of `Riesz1/Frozen/ArcIndicator.lean` is the indicator of the open
ball of radius `a` about `center`.

Main results:
* `indicatorArc_eq_arcIndicator`: the two indicators agree at centre `0`, for `a < 1/2`.
* `arcIndicator_eq_indicatorArc_sub`: the arc about `c` is the translate by `c` of the arc about `0`.
* `memLp_arcIndicator`, `memLp_centredArc`: the arc indicator about any centre, and its centred
  version `arcIndicator c a - 2a`, are square integrable on the circle.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- A real point `x` lies in the arc `arcImage a` exactly when its distance to the nearest integer
is less than `a`, for `a < 1/2`. The forward direction uses that a representative `y ∈ (-a, a)`
has nearest integer `0`. The backward direction shifts `x` by the integer `round x`. -/
lemma mem_arcImage_iff_abs_lt {a : ℝ} (ha1 : a < 1 / 2) (x : ℝ) :
    (x : UnitAddCircle) ∈ arcImage a ↔ |x - round x| < a := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : (y : UnitAddCircle) = (x : UnitAddCircle) := hyx
    have hround : round y = 0 := round_eq_zero_iff.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hnorm : |x - round x| = |y - round y| := by
      rw [← UnitAddCircle.norm_eq, ← UnitAddCircle.norm_eq, hyx']
    rw [hnorm, hround, Int.cast_zero, sub_zero]
    exact abs_lt.mpr hy
  · intro h
    refine ⟨x - round x, ⟨(abs_lt.mp h).1, (abs_lt.mp h).2⟩, ?_⟩
    have hn : ((round x : ℝ) : UnitAddCircle) = 0 := by
      rw [show (round x : ℝ) = (round x : ℤ) • (1 : ℝ) by rw [zsmul_eq_mul, mul_one],
        AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero]
    show ((x - round x : ℝ) : UnitAddCircle) = (x : UnitAddCircle)
    rw [AddCircle.coe_sub, hn, sub_zero]

/-- The arc indicator `indicatorArc a` is `arcIndicator` about the centre `0`,
for every `a < 1/2`. The proof uses only the upper bound, so the statement holds on the wider range
`a < 1/2` than `0 < a < 1/2`. -/
theorem indicatorArc_eq_arcIndicator {a : ℝ} (ha1 : a < 1 / 2) :
    indicatorArc a = arcIndicator 0 a := by
  funext t
  obtain ⟨x, rfl⟩ := exists_real_coe t
  unfold arcIndicator indicatorArc
  rw [dist_zero_right, UnitAddCircle.norm_eq]
  by_cases h : |x - round x| < a
  · simp only [h, ↓reduceIte]
    rw [Set.indicator_of_mem ((mem_arcImage_iff_abs_lt ha1 x).mpr h)]
  · simp only [h, ↓reduceIte]
    rw [Set.indicator_of_notMem (fun hm => h ((mem_arcImage_iff_abs_lt ha1 x).mp hm))]

/-- The arc about the centre `c` is the translate by `c` of the arc about `0`: the point `t` lies
within `a` of `c` exactly when `t - c` lies within `a` of `0`. -/
lemma arcIndicator_eq_arcIndicator_zero_sub (a : ℝ) (c t : UnitAddCircle) :
    arcIndicator c a t = arcIndicator 0 a (t - c) := by
  have h : dist (t - c) 0 = dist t c := by
    rw [← dist_sub_right t c c, sub_self]
  unfold arcIndicator
  rw [h]

/-- For `a < 1/2`, the arc indicator `arcIndicator c a` about any centre `c` is the translate by `c`
of the indicator `indicatorArc a`. -/
lemma arcIndicator_eq_indicatorArc_sub {a : ℝ} (ha1 : a < 1 / 2) (c t : UnitAddCircle) :
    arcIndicator c a t = indicatorArc a (t - c) := by
  rw [arcIndicator_eq_arcIndicator_zero_sub, ← indicatorArc_eq_arcIndicator ha1]

/-- The arc indicator about `c` is measurable, as the indicator of an open set. -/
lemma measurable_arcIndicator (c : UnitAddCircle) (a : ℝ) : Measurable (arcIndicator c a) := by
  unfold arcIndicator
  exact Measurable.ite (measurableSet_lt (continuous_id.dist continuous_const).measurable
    measurable_const) measurable_const measurable_const

/-- The arc indicator about any centre is square integrable on the circle, since it is
bounded and measurable on a finite measure space. -/
lemma memLp_arcIndicator (c : UnitAddCircle) (a : ℝ) :
    MemLp (fun t : UnitAddCircle => (arcIndicator c a t : ℂ)) 2 volume := by
  refine MemLp.of_bound
    (Complex.measurable_ofReal.comp (measurable_arcIndicator c a)).aestronglyMeasurable
    1 (ae_of_all _ fun t => ?_)
  unfold arcIndicator
  split_ifs <;> simp

/-- The centred arc indicator `arcIndicator c a - 2a` about any centre is square integrable on the
circle. -/
lemma memLp_centredArc (c : UnitAddCircle) (a : ℝ) :
    MemLp (fun t : UnitAddCircle => ((arcIndicator c a t - 2 * a : ℝ) : ℂ)) 2 volume := by
  have e : (fun t : UnitAddCircle => ((arcIndicator c a t - 2 * a : ℝ) : ℂ)) =
      fun t => (arcIndicator c a t : ℂ) - ((2 * a : ℝ) : ℂ) := by
    funext t
    exact Complex.ofReal_sub _ _
  rw [e]
  exact (memLp_arcIndicator c a).sub (memLp_const _)

end Riesz1

end
