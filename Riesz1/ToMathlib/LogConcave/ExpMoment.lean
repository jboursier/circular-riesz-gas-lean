/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LogConcave.Survival
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Exponential moment of a log-concave density

Let `f` be a positive log-concave density on `(0, b)` with mean one. The survival bound of
`Riesz1.logConcave_survival_le` gives `S t ≤ 2 exp (-(log 2) t / 2)`, where
`S t = ∫_{[t, ∞)} f`. The layer cake formula for the measure `ν = f dx` then gives
`∫ exp (c x) dν ≤ 3` for `c = (log 2) / 4`.

The proof writes `exp (c x) - 1 = ∫_0^x c exp (c t) dt`. Hence
`∫ (exp (c x) - 1) dν = ∫_0^∞ c exp (c t) S t dt`, which is at most `∫_0^∞ 2 c exp (-c t) dt = 2`.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- **Exponential moment of a log-concave density.** Let `b > 0` and let `f` be positive and
log-concave on `(0, b)`, extended by zero. Suppose `∫ f = 1` and `∫ x f(x) = 1`. Then the function
`x ↦ exp ((log 2) / 4 * x) f x` is integrable and its integral is at most three. -/
theorem logConcave_exp_moment_le {b : ℝ} (hb : 0 < b) (f : ℝ → ℝ)
    (hfpos : ∀ x ∈ Set.Ioo 0 b, 0 < f x) (hf0 : ∀ x ∉ Set.Ioo 0 b, f x = 0)
    (hconc : ConcaveOn ℝ (Set.Ioo 0 b) (fun x => Real.log (f x)))
    (hint : ∫ x, f x = 1) (hmean : ∫ x, x * f x = 1) :
    Integrable (fun x => Real.exp (Real.log 2 / 4 * x) * f x) ∧
      ∫ x, Real.exp (Real.log 2 / 4 * x) * f x ≤ 3 := by
  set c : ℝ := Real.log 2 / 4 with hc_def
  have hc : 0 < c := by
    rw [hc_def]
    exact div_pos (Real.log_pos one_lt_two) (by norm_num)
  have hfint : Integrable f := by
    by_contra h
    rw [integral_undef h] at hint
    exact zero_ne_one hint
  have hfnn := logConcave_nonneg hfpos hf0
  have hfmeas : Measurable f := by
    classical
    have hpw : Measurable ((Ioo 0 b).piecewise f (fun _ => (0 : ℝ))) :=
      ContinuousOn.measurable_piecewise (logConcave_continuousOn hfpos hconc) continuousOn_const
        measurableSet_Ioo
    have heq : (Ioo 0 b).piecewise f (fun _ => (0 : ℝ)) = f := by
      funext x
      by_cases hx : x ∈ Ioo 0 b
      · rw [Set.piecewise_eq_of_mem _ _ _ hx]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hx, hf0 x hx]
    rw [← heq]
    exact hpw
  have hexpmeas : Measurable (fun x : ℝ => Real.exp (c * x)) :=
    (by fun_prop : Continuous fun x : ℝ => Real.exp (c * x)).measurable
  have hsurv : ∀ t : ℝ, 0 ≤ t → ∫ x in Ici t, f x ≤ 2 * Real.exp (-(Real.log 2) * t / 2) :=
    fun t ht => logConcave_survival_le hb f hfpos hf0 hconc hint hmean t ht
  -- The probability-like measure `ν = f dx`.
  set ν : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (f x)) with hν_def
  have hfmeasE : Measurable (fun x => ENNReal.ofReal (f x)) := hfmeas.ennreal_ofReal
  have hν_univ : ν univ = 1 := by
    rw [hν_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hfint (Filter.Eventually.of_forall hfnn), hint,
      ENNReal.ofReal_one]
  have hν_Ioi : ∀ t : ℝ, ν (Ioi t) = ENNReal.ofReal (∫ x in Ici t, f x) := by
    intro t
    rw [hν_def, withDensity_apply _ measurableSet_Ioi, integral_Ici_eq_integral_Ioi,
      ← ofReal_integral_eq_lintegral_ofReal hfint.integrableOn
        (Filter.Eventually.of_forall hfnn)]
  -- Layer cake: `∫ (exp (c x) - 1) dν = ∫_{t > 0} ν (t, ∞) c exp (c t) dt`.
  have hG : ∀ x : ℝ, ∫ t in (0 : ℝ)..x, c * Real.exp (c * t) = Real.exp (c * x) - 1 := by
    intro x
    have hd : ∀ t ∈ uIcc (0 : ℝ) x,
        HasDerivAt (fun t => Real.exp (c * t)) (c * Real.exp (c * t)) t := by
      intro t _
      have h := ((hasDerivAt_id t).const_mul c).exp
      simp only [id, mul_one] at h
      convert h using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun t : ℝ => c * Real.exp (c * t)).intervalIntegrable 0 x)]
    simp
  have hnnν : 0 ≤ᵐ[ν] fun x : ℝ => x := by
    rw [hν_def]
    refine (ae_withDensity_iff hfmeasE).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    by_cases hxI : x ∈ Ioo 0 b
    · exact hxI.1.le
    · exfalso
      apply hx
      show ENNReal.ofReal (f x) = 0
      rw [hf0 x hxI, ENNReal.ofReal_zero]
  have hlc := lintegral_comp_eq_lintegral_meas_lt_mul (μ := ν) (f := fun x : ℝ => x)
    (g := fun t => c * Real.exp (c * t)) hnnν measurable_id.aemeasurable
    (fun t _ => (by fun_prop : Continuous fun t : ℝ => c * Real.exp (c * t)).intervalIntegrable 0 t)
    (Filter.Eventually.of_forall fun t => (mul_pos hc (Real.exp_pos _)).le)
  simp only [hG] at hlc
  -- Tail formula: `ν (t, ∞) = ∫_{[t, ∞)} f`.
  have hνt : ∀ t : ℝ, ν {a : ℝ | t < a} = ENNReal.ofReal (∫ x in Ici t, f x) :=
    fun t => hν_Ioi t
  -- The layer cake integrand is at most `2 c exp (-c t)`, which integrates to `2`.
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ν {a : ℝ | t < a} * ENNReal.ofReal (c * Real.exp (c * t)) ≤
      ENNReal.ofReal (2 * c * Real.exp (-c * t)) := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have hid : 2 * Real.exp (-(Real.log 2) * t / 2) * (c * Real.exp (c * t)) =
        2 * c * Real.exp (-c * t) := by
      have h1 : Real.exp (-(Real.log 2) * t / 2) * Real.exp (c * t) = Real.exp (-c * t) := by
        rw [← Real.exp_add]
        congr 1
        rw [hc_def]
        ring
      calc 2 * Real.exp (-(Real.log 2) * t / 2) * (c * Real.exp (c * t))
          = 2 * c * (Real.exp (-(Real.log 2) * t / 2) * Real.exp (c * t)) := by ring
        _ = 2 * c * Real.exp (-c * t) := by rw [h1]
    have hG0 : 0 ≤ c * Real.exp (c * t) := (mul_pos hc (Real.exp_pos _)).le
    rw [hνt t, ← ENNReal.ofReal_mul (setIntegral_nonneg measurableSet_Ici fun x _ => hfnn x)]
    apply ENNReal.ofReal_le_ofReal
    calc (∫ x in Ici t, f x) * (c * Real.exp (c * t))
        ≤ 2 * Real.exp (-(Real.log 2) * t / 2) * (c * Real.exp (c * t)) :=
          mul_le_mul_of_nonneg_right (hsurv t ht0) hG0
      _ = 2 * c * Real.exp (-c * t) := hid
  have hint_bound : ∫⁻ t in Ioi (0 : ℝ), ν {a : ℝ | t < a} *
      ENNReal.ofReal (c * Real.exp (c * t)) ≤ ENNReal.ofReal 2 := by
    have hHint : IntegrableOn (fun t : ℝ => 2 * c * Real.exp (-c * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hc |>.const_mul (2 * c))
    have hHnn : ∀ t : ℝ, 0 ≤ 2 * c * Real.exp (-c * t) := fun t =>
      mul_nonneg (mul_nonneg two_pos.le hc.le) (Real.exp_pos _).le
    calc ∫⁻ t in Ioi (0 : ℝ), ν {a : ℝ | t < a} * ENNReal.ofReal (c * Real.exp (c * t))
        ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2 * c * Real.exp (-c * t)) :=
          setLIntegral_mono (by fun_prop : Continuous fun t : ℝ => 2 * c * Real.exp (-c * t)).measurable.ennreal_ofReal
            hpt
      _ = ENNReal.ofReal (∫ t in Ioi (0 : ℝ), 2 * c * Real.exp (-c * t)) :=
          (ofReal_integral_eq_lintegral_ofReal hHint
            (Filter.Eventually.of_forall hHnn)).symm
      _ = ENNReal.ofReal 2 := by
          congr 1
          rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -c < 0) 0]
          field_simp
          simp
  -- Splitting `exp (c x) ≤ (exp (c x) - 1) + 1` gives the bound on `∫ exp (c x) dν`.
  have hpw : ∀ a : ℝ, ENNReal.ofReal a ≤ ENNReal.ofReal (a - 1) + 1 := by
    intro a
    rcases le_total 1 a with ha | ha
    · rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (show (0 : ℝ) ≤ a - 1 by linarith) zero_le_one]
      apply ENNReal.ofReal_le_ofReal
      linarith
    · rw [ENNReal.ofReal_eq_zero.mpr (by linarith : a - 1 ≤ 0), zero_add]
      calc ENNReal.ofReal a ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal ha
        _ = 1 := ENNReal.ofReal_one
  have hsplit : ∫⁻ x, ENNReal.ofReal (Real.exp (c * x)) ∂ν ≤ ENNReal.ofReal 3 := by
    calc ∫⁻ x, ENNReal.ofReal (Real.exp (c * x)) ∂ν
        ≤ ∫⁻ x, (ENNReal.ofReal (Real.exp (c * x) - 1) + 1) ∂ν :=
          lintegral_mono fun x => hpw (Real.exp (c * x))
      _ = (∫⁻ x, ENNReal.ofReal (Real.exp (c * x) - 1) ∂ν) + ν univ := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, one_mul]
      _ ≤ ENNReal.ofReal 2 + 1 := by
          rw [hν_univ, hlc]
          exact add_le_add hint_bound le_rfl
      _ = ENNReal.ofReal 3 := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (show (0 : ℝ) ≤ 2 by norm_num) zero_le_one]
          norm_num
  -- Transfer the bound from `ν` to Lebesgue measure: `∫⁻ exp(c x) dν = ∫⁻ exp(c x) f(x) dx`.
  have hL : ∫⁻ x, ENNReal.ofReal (Real.exp (c * x) * f x) ≤ ENNReal.ofReal 3 := by
    have hwd : ∫⁻ x, ENNReal.ofReal (Real.exp (c * x)) ∂ν =
        ∫⁻ x, ENNReal.ofReal (Real.exp (c * x) * f x) := by
      rw [hν_def, lintegral_withDensity_eq_lintegral_mul volume hfmeasE hexpmeas.ennreal_ofReal]
      congr 1
      funext x
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (hfnn x)]
      congr 1
      ring
    rw [← hwd]
    exact hsplit
  have hmeasg : Measurable (fun x => Real.exp (c * x) * f x) := hexpmeas.mul hfmeas
  have hnng : ∀ x, 0 ≤ Real.exp (c * x) * f x := fun x => mul_nonneg (Real.exp_pos _).le (hfnn x)
  have hfin : HasFiniteIntegral (fun x => Real.exp (c * x) * f x) volume :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnng)).mpr
      (lt_of_le_of_lt hL ENNReal.ofReal_lt_top)
  refine ⟨⟨hmeasg.aestronglyMeasurable, hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnng)
    hmeasg.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hL

end Riesz1
