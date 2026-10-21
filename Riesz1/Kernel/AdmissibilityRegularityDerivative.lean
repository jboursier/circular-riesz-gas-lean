/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityAbsoluteContinuity
public import Riesz1.ToMathlib.CircleFourierDerivative

/-!
# The derivative Fourier integral of the admissible transport

The locally integrable derivative of the continuous transport has exactly the
distributional coefficients prescribed by the transport multiplier. This is the
identification step in the Fourier-decay argument.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- The classical derivative of the continuous transport has the distributional
coefficients, including across the marks. All hypotheses are the original (A1)–(A3)
conditions. Derivative integrability is proved here rather than assumed. -/
theorem exists_transport_derivative_integral (P : Parameters) (L : Length)
    (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (p : ℕ+) (marks : Fin (p : ℕ) → ℝ) (α C : ℝ)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hC : 0 ≤ C)
    (hprim : PrimitiveRegularity L η P.val.2 B f)
    (hreg : TransportRegularity P L f p marks α C) :
    ∃ ψ : Circle L → ℝ, Continuous ψ ∧
      ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength L),
        (∀ k : ℤ, coeff L ⟨(fun x => (ψ x : ℂ)), complexL2Integrable L _ hψ⟩ k =
          transportCoeffs P L f k) ∧
        LocallyIntegrable (deriv (fun t : ℝ => ψ (t : Circle L))) volume ∧
        ∀ k : ℤ, k ≠ 0 →
          (∫ t in (0 : ℝ)..L.val,
            ((deriv (fun u : ℝ => ψ (u : Circle L)) t : ℝ) : ℂ) *
              fourier (-k) (t : Circle L)) =
            -(L.val : ℂ) * (|2 * Real.pi * (k : ℝ) / L.val| ^ (1 - P.val.2) : ℝ) /
              (2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) *
                coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨ψ, hc, hψ, hcoef, hpoint⟩ :=
    exists_continuous_transport_with_regularity P L η B hη hB f p marks α C hprim hreg
  have hi := Internal.locallyIntegrable_deriv_of_transport_bound P L marks α C
    hα0 hα1 hC _ hpoint
  refine ⟨ψ, hc, hψ, hcoef, hi, fun k hk => ?_⟩
  have hint : IntervalIntegrable (deriv (fun u : ℝ => ψ (u : Circle L))) volume 0 L.val :=
    (intervalIntegrable_iff' (by finiteness)).mpr (hi.integrableOn_isCompact isCompact_uIcc)
  have heq := CircleFourier.integral_deriv_mul_fourier hc
    (CircleSingularity.countable_marked_lifts (T := L.val) marks)
    (fun x hx => (hpoint x (by simpa only [mem_ofPred_eq, not_exists] using hx)).1.differentiableAt
      (by norm_num)) hint k
  have hω : (2 * Real.pi * Complex.I * (k : ℂ) / (L.val : ℂ)) ≠ 0 := by
    apply div_ne_zero
    · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast hk)
    · exact_mod_cast L.property.ne'
  change _ = (L.val : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ) / L.val) *
    coeff L ⟨(fun x => (ψ x : ℂ)), complexL2Integrable L _ hψ⟩ k at heq
  rw [heq, hcoef, transportCoeffs, ite_eq_right hk]
  push_cast
  field_simp

end Riesz1
