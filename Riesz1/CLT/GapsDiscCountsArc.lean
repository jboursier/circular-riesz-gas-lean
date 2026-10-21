/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscStripsArc
public import Riesz1.Bridges.ExplicitFormulasCentred
public import Riesz1.Bridges.IndicatorArc
public import Riesz1.Kernel.AdmissibleExamplesCompact
public import Riesz1.Kernel.AdmissibilityRegularityVariance
public import Riesz1.Kernel.PeriodicZeta
public import Mathlib.MeasureTheory.Group.AddCircle
public import Mathlib.Topology.Order.Compact
public import Riesz1.Frozen.TestAtScale
public import Riesz1.Frozen.CircleVariance
public import Riesz1.Frozen.CountVariance
public import Riesz1.Frozen.RescaledProfile

/-!
# Arcs of general half-width at scale `ℓ`, and the periodic zeta function on short arcs

This file generalises `Riesz1.CLT.GapsDiscStripsArc`, whose profile is the open arc of
half-width `1/4`. For every half-width `a` with `0 < a < 1/2`, the profile `arcIndicator 0 a`
rescales at scale `ℓ` to the open arc of half-width `a ℓ` about `0`, and its circle variance is
`countVariance P ℓ^{-s} V_s(2 a ℓ)` by the explicit formula for indicators of arcs.

The file also proves a lower bound `c t^s ≤ V_s(t)` on `(0, T]` for every `T ≤ 1/2`, where
`V_s = periodicZeta s`. The matching upper bound is `periodicZeta_le_mul_rpow`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz1

/-- The arc profile of half-width `a`: the open arc of half-width `a` about `0`. -/
def arcProfile (a : ℝ) : Profile :=
  ⟨arcIndicator 0 a, memLp_arcIndicator 0 a⟩

/-- For `0 < a < 1/2`, at every scale `ℓ` in `(0, 1]`, the profile `arcProfile a` rescales to
the open arc of half-width `a ℓ` about `0`. -/
lemma testAtScale_arcProfile {a : ℝ} (_ha0 : 0 < a) (ha1 : a < 1 / 2) (ell : Scale) :
    testAtScale (arcProfile a) ell = arcIndicator 0 (a * ell.val) := by
  have hℓ : 0 < ell.val := ell.property.1
  funext x
  unfold testAtScale
  by_cases h1 : ell.val = 1
  · simp only [h1, ↓reduceIte, mul_one]
    rfl
  · simp only [h1, ↓reduceIte]
    unfold rescaledProfile zeroExtension
    set c := centralRep unitLength x with hc
    have hdist : dist x 0 = |c| := dist_zero_eq_abs_centralRep x
    unfold arcIndicator
    rw [hdist]
    by_cases hy : |c / ell.val| < 1 / 2
    · simp only [hy, ↓reduceIte]
      have hyx : (arcProfile a).val ((c / ell.val : ℝ) : UnitAddCircle) =
          if dist ((c / ell.val : ℝ) : UnitAddCircle) 0 < a then 1 else 0 := rfl
      rw [hyx, dist_coe_zero_eq_abs hy, abs_div, abs_of_pos hℓ]
      have hcond : |c| / ell.val < a ↔ |c| < a * ell.val := by
        rw [div_lt_iff₀ hℓ]
      simp only [hcond]
    · simp only [hy, ↓reduceIte]
      have hge : ell.val / 2 ≤ |c| := by
        have h' : 1 / 2 ≤ |c / ell.val| := not_lt.mp hy
        rw [abs_div, abs_of_pos hℓ, le_div_iff₀ hℓ] at h'
        linarith
      have hlt : a * ell.val < ell.val / 2 := by
        have := mul_lt_mul_of_pos_right ha1 hℓ
        linarith
      have hnot : ¬ |c| < a * ell.val := fun h => by linarith
      simp only [hnot, ↓reduceIte]

/-- For `0 < a < 1/2`, the circle variance of the arc profile `arcProfile a` at scale `ℓ` is
`ℓ^{-s}` times the count constant `countVariance P` times `V_s(2 a ℓ)`, where `V_s` is
`periodicZeta` at the exponent `s` of `P`. -/
lemma circleVariance_arcProfile {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (P : Parameters)
    (ell : Scale) :
    (circleVariance P (arcProfile a) ell).toReal =
      ell.val ^ (-P.val.2) * countVariance P *
        periodicZeta (parametersExponent P) ((2 * a * ell.val : ℝ) : UnitAddCircle) := by
  have hℓ : 0 < ell.val := ell.property.1
  have hℓ1 : ell.val ≤ 1 := ell.property.2
  have haℓ0 : 0 < a * ell.val := mul_pos ha0 hℓ
  have haℓ1 : a * ell.val < 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hℓ1 ha0.le
    linarith
  obtain ⟨_, _, ⟨_, hform⟩, _, hunc⟩ :=
    explicit_formulas_indicator_centered (parametersExponent P) P.val.1 P.property.1 0
      (a * ell.val) haℓ0 haℓ1
  have hsub : (⟨fun x => (testAtScale (arcProfile a) ell x : ℂ),
      testAtScaleL2 (arcProfile a) ell⟩ : {g : UnitAddCircle → ℂ // MemLp g 2 volume}) =
        ⟨fun x => (arcIndicator 0 (a * ell.val) x : ℂ), memLp_arcIndicator 0 (a * ell.val)⟩ :=
    Subtype.ext (by simp only [testAtScale_arcProfile ha0 ha1 ell])
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
  have hV : ((2 * (a * ell.val) : ℝ) : UnitAddCircle) =
      ((2 * a * ell.val : ℝ) : UnitAddCircle) := by
    congr 1
    ring
  rw [hV] at hform
  unfold countVariance
  rw [show 2 * P.val.1 * Real.pi * P.val.2 = 2 * Real.pi * P.val.1 * P.val.2 by ring]
  linear_combination (ell.val ^ (-P.val.2)) * hform

/-- Lower bound for the periodic zeta function on short arcs: for every Riesz exponent `s` and
every `T ≤ 1/2`, there is a positive constant `c` with `c t^s ≤ V_s(t)` for all `0 < t ≤ T`.
Near `0` this follows from the expansion `V_s(t) = t^s + O(t²)`, and on `[δ, T]` from the
positivity and continuity of `V_s`. -/
lemma periodicZeta_ge_mul_rpow_of_le (s : RieszExponent) {T : ℝ} (hT0 : 0 < T)
    (hT1 : T ≤ 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t → t ≤ T →
      c * t ^ s.val ≤ periodicZeta s (t : UnitAddCircle) := by
  obtain ⟨C, hC, t₀, ht₀, hasymp⟩ := periodicZeta_asymptotic s
  -- The threshold `δ` lies below `T`, below `t₀`, and below `1 / (2 C)`.
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min (min t₀ T) (1 / (2 * C)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min ht₀ hT0) (one_div_pos.mpr (mul_pos two_pos hC))
  have hδT : δ ≤ T := by
    rw [hδdef]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδt₀ : δ ≤ t₀ := by
    rw [hδdef]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδC : δ ≤ 1 / (2 * C) := by
    rw [hδdef]
    exact min_le_right _ _
  -- On the compact interval `[δ, T]` the continuous function `V_s` attains a minimum `V_s(x₀)`,
  -- which is positive because `0 < x₀ < 1`.
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_Icc (a := δ) (b := T)).exists_isMinOn
    (Set.nonempty_Icc.mpr hδT) (periodicZeta_continuous s).continuousOn
  have hmin' : ∀ y ∈ Set.Icc δ T,
      periodicZeta s (x₀ : UnitAddCircle) ≤ periodicZeta s (y : UnitAddCircle) :=
    fun y hy => isMinOn_iff.mp hmin y hy
  have hm₀ : 0 < periodicZeta s (x₀ : UnitAddCircle) :=
    periodicZeta_pos s (lt_of_lt_of_le hδ0 hx₀.1) (lt_of_le_of_lt hx₀.2 (by linarith))
  have hm0 : 0 < min (1 / 2) (periodicZeta s (x₀ : UnitAddCircle)) := lt_min (by norm_num) hm₀
  refine ⟨min (1 / 2) (periodicZeta s (x₀ : UnitAddCircle)), hm0, ?_⟩
  intro t ht0 htT
  have hts0 : 0 ≤ t ^ s.val := Real.rpow_nonneg ht0.le _
  have ht1 : t ≤ 1 := by linarith
  have hts1 : t ^ s.val ≤ 1 := Real.rpow_le_one ht0.le ht1 s.2.1.le
  have hm_le_half : min (1 / 2) (periodicZeta s (x₀ : UnitAddCircle)) ≤ 1 / 2 :=
    min_le_left _ _
  have hm_le_V : min (1 / 2) (periodicZeta s (x₀ : UnitAddCircle)) ≤
      periodicZeta s (x₀ : UnitAddCircle) := min_le_right _ _
  rcases le_total t δ with htδ | htδ
  · -- Short range: `V_s(t) ≥ t^s - C t² ≥ t^s / 2`, since `t² ≤ t^s · t` and `C t ≤ 1/2`.
    have htt₀ : t ≤ t₀ := le_trans htδ hδt₀
    have hasy := (abs_le.mp (hasymp t ht0 htt₀)).1
    have hCt : C * t ≤ 1 / 2 := by
      have h1 : t ≤ 1 / (2 * C) := le_trans htδ hδC
      rw [le_div_iff₀ (mul_pos two_pos hC)] at h1
      linarith
    have htle : t ≤ t ^ s.val := by
      have h := Real.rpow_le_rpow_of_exponent_ge ht0 ht1 s.2.2.le
      rwa [Real.rpow_one] at h
    have ht2 : t ^ 2 ≤ t ^ s.val * t := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right htle ht0.le
    have h3 : C * t ^ 2 ≤ C * (t ^ s.val * t) := mul_le_mul_of_nonneg_left ht2 hC.le
    have h4 : t ^ s.val * (C * t) ≤ t ^ s.val * (1 / 2) :=
      mul_le_mul_of_nonneg_left hCt hts0
    have h5 : min (1 / 2) (periodicZeta s (x₀ : UnitAddCircle)) * t ^ s.val ≤ 1 / 2 * t ^ s.val :=
      mul_le_mul_of_nonneg_right hm_le_half hts0
    nlinarith
  · -- Middle range: `V_s(t) ≥ V_s(x₀) ≥ min(1/2, V_s(x₀)) ≥ min(1/2, V_s(x₀)) t^s`.
    have hV := hmin' t ⟨htδ, htT⟩
    have hle : min (1 / 2) (periodicZeta s (x₀ : UnitAddCircle)) * t ^ s.val ≤
        min (1 / 2) (periodicZeta s (x₀ : UnitAddCircle)) :=
      mul_le_of_le_one_right hm0.le hts1
    linarith

end Riesz1

end
end
