/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.TransportCoeffs
public import Riesz1.Kernel.ExplicitFormulasIndicatorEnergy
public import Riesz1.Kernel.ExplicitFormulasIndicatorLimit

/-!
# Indicator transport and energy

This is the indicator case of Lemma 2.3. For `0 < s < 1`, `β > 0` and `0 < a < 1/2`, let
`ξ = 1_{(-a,a)} - 2a` on the circle `Circle ⟨1, _⟩`. The statement collects the three claims:

* the mean-zero transport of `ξ` is the continuous function
  `-(V_s(x + a) - V_s(x - a)) / (4πβ s tan(πs/2))`: every `L²` representative with the
  transport coefficients agrees with it almost everywhere.
* the energy identity `(2π)^{1-s}/(2β c_s) ‖ξ‖² = cot(πs/2) V_s(2a) / (2πβs)`.
* the uncentered indicator `1_{(-a,a)}` has the same transport and the same seminorm.

The definitions `transportCoeffs`, `coeff` and `circleSobolevSq` are used as they stand.
-/

public section

open MeasureTheory Set Filter Topology
open scoped Real Interval

namespace Riesz1

/-- The uncentered and centred indicators have the same nonzero Fourier coefficients. -/
lemma fourierCoeff_indicatorArc_eq_centered {a : ℝ} {k : ℤ} (hk : k ≠ 0) :
    fourierCoeff (fun t : UnitAddCircle => (indicatorArc a t : ℂ)) k =
      fourierCoeff (fun t : UnitAddCircle => (centeredIndicatorArc a t : ℂ)) k := by
  rw [centeredIndicatorArc_eq, fourierCoeff_sub_const (integrable_indicatorArc a),
    fourierCoeff_one]
  simp [hk]

/-- The uncentered indicator has the same transport coefficients as the centred one. -/
lemma transportCoeffs_indicatorArc (s : RieszExponent) (β a : ℝ) (hβ : 0 < β) (k : ℤ) :
    transportCoeffs ⟨(β, s.val), hβ, s.2.1, s.2.2⟩ ⟨1, one_pos⟩
        ⟨indicatorArc a, memLp_indicatorArc a⟩ k =
      transportCoeffs ⟨(β, s.val), hβ, s.2.1, s.2.2⟩ ⟨1, one_pos⟩
        ⟨centeredIndicatorArc a, memLp_centeredIndicatorArc a⟩ k := by
  by_cases hk : k = 0
  · simp [transportCoeffs, hk]
  · dsimp only [transportCoeffs, coeff]
    simp only [hk, ↓reduceIte]
    rw [fourierCoeff_indicatorArc_eq_centered hk]

/-- The uncentered indicator has the same seminorm as the centred one. -/
lemma circleSobolevSq_indicatorArc (s : RieszExponent) (a : ℝ) :
    circleSobolevSq ((1 - s.val) / 2)
        ⟨fun t : UnitAddCircle => (indicatorArc a t : ℂ), memLp_indicatorArc a⟩ =
      circleSobolevSq ((1 - s.val) / 2)
        ⟨fun t : UnitAddCircle => (centeredIndicatorArc a t : ℂ), memLp_centeredIndicatorArc a⟩ := by
  unfold circleSobolevSq
  congr 1
  funext k
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte]
    rw [fourierCoeff_indicatorArc_eq_centered hk]

/-- The indicator case of Lemma 2.3. For `0 < s < 1`, `β > 0` and `0 < a < 1/2`,
with the centred indicator `ξ = 1_{(-a,a)} - 2a` on `Circle ⟨1, _⟩`:

* the transport `V_s(x + a) - V_s(x - a)` form is continuous, and every `L²` function with the
  transport coefficients of `ξ` equals it almost everywhere.
* the energy identity `(2π)^{1-s}/(2β c_s) ‖ξ‖² = cot(πs/2) V_s(2a)/(2πβs)` holds, and `‖ξ‖²` is
  finite.
* the uncentered indicator `1_{(-a,a)}` has the same transport coefficients and seminorm. -/
theorem explicit_formulas_indicator (s : RieszExponent) (β : ℝ) (hβ : 0 < β) (a : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    Continuous (fun t : UnitAddCircle => transportFormula s β a t) ∧
    (∀ ψ : {g : Circle ⟨1, one_pos⟩ → ℝ // MemLp (fun x => (g x : ℂ)) 2
          (arclength ⟨1, one_pos⟩)},
      (∀ k : ℤ, coeff ⟨1, one_pos⟩
          ⟨fun x => (ψ.val x : ℂ), complexL2Integrable ⟨1, one_pos⟩ _ ψ.property⟩ k =
        transportCoeffs ⟨(β, s.val), hβ, s.2.1, s.2.2⟩ ⟨1, one_pos⟩
          ⟨centeredIndicatorArc a, memLp_centeredIndicatorArc a⟩ k) →
      ∀ᵐ x ∂(arclength ⟨1, one_pos⟩), ψ.val x = transportFormula s β a x) ∧
    (circleSobolevSq ((1 - s.val) / 2)
        ⟨fun t : UnitAddCircle => (centeredIndicatorArc a t : ℂ), memLp_centeredIndicatorArc a⟩ ≠ ⊤ ∧
      (2 * Real.pi) ^ (1 - s.val) / (2 * β * rieszConstant s) *
          (circleSobolevSq ((1 - s.val) / 2)
            ⟨fun t : UnitAddCircle => (centeredIndicatorArc a t : ℂ),
              memLp_centeredIndicatorArc a⟩).toReal =
        Real.cos (Real.pi * s.val / 2) / Real.sin (Real.pi * s.val / 2) /
            (2 * Real.pi * β * s.val) * periodicZeta s ((2 * a : ℝ) : UnitAddCircle)) ∧
    (∀ k : ℤ, transportCoeffs ⟨(β, s.val), hβ, s.2.1, s.2.2⟩ ⟨1, one_pos⟩
          ⟨indicatorArc a, memLp_indicatorArc a⟩ k =
        transportCoeffs ⟨(β, s.val), hβ, s.2.1, s.2.2⟩ ⟨1, one_pos⟩
          ⟨centeredIndicatorArc a, memLp_centeredIndicatorArc a⟩ k) ∧
    circleSobolevSq ((1 - s.val) / 2)
        ⟨fun t : UnitAddCircle => (indicatorArc a t : ℂ), memLp_indicatorArc a⟩ =
      circleSobolevSq ((1 - s.val) / 2)
        ⟨fun t : UnitAddCircle => (centeredIndicatorArc a t : ℂ), memLp_centeredIndicatorArc a⟩ := by
  have hcont := continuous_transportFormula (s := s) β a
  refine ⟨continuous_transportFormula_real β a, ?_, (energy_identity_indicator s β hβ a ha0 ha1),
    transportCoeffs_indicatorArc s β a hβ, circleSobolevSq_indicatorArc s a⟩
  intro ψ hψ
  have hcoeff : ∀ k : ℤ, fourierCoeff (fun x : UnitAddCircle => (transportFormula s β a x : ℂ)) k =
      transportSeriesCoeff s.val β a k := by
    intro k
    rw [show (fun x : UnitAddCircle => (transportFormula s β a x : ℂ)) =
        fun x => ∑' n : ℤ, transportSeriesCoeff s.val β a n * fourier n x from
          funext fun x => transportFormula_coe β a x]
    exact fourierCoeff_tsum_fourier _ (summable_norm_transportSeriesCoeff s.2.1 β a) k
  have hae : (fun x : UnitAddCircle => (ψ.val x : ℂ)) =ᵐ[volume]
      (fun x : UnitAddCircle => (transportFormula s β a x : ℂ)) := by
    refine ae_eq_of_fourierCoeff_eq ψ.property (memLp_of_continuous_circle hcont) fun k => ?_
    have h1 : fourierCoeff (fun x : UnitAddCircle => (ψ.val x : ℂ)) k =
        transportCoeffs ⟨(β, s.val), hβ, s.2.1, s.2.2⟩ ⟨1, one_pos⟩
          ⟨centeredIndicatorArc a, memLp_centeredIndicatorArc a⟩ k := hψ k
    rw [h1, transportCoeffs_centered s β a hβ ha0 ha1 k, hcoeff k]
  filter_upwards [hae] with x hx
  exact_mod_cast hx

end Riesz1

end
