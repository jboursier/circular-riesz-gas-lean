/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularitySingularFourier
public import Riesz1.Kernel.AdmissibilityRegularityVariance
public import Riesz1.Frozen.TransportCoeffs
/-!
# Continuous transport supplied by the Hölder primitive

The continuous-representative clause of the transport regularity follows from (A1) alone.
The absolutely convergent singular integral of the primitive is continuous. Its
Fourier multiplier, computed in `AdmissibilityRegularitySingularFourier`, agrees exactly with
the transport coefficients `transportCoeffs` after normalization. No smoothness or derivative
bounds are assumed for the transport.
-/

public section

open MeasureTheory
namespace Riesz1
/-- The (A1) primitive supplies a continuous, square-integrable representative of the
transport, with exactly the coefficients `transportCoeffs`, on every circle. This proves the
continuous-representative clause. Absolute continuity is a separate claim. -/
theorem exists_continuous_transport_of_primitiveRegularity (P : Parameters) (L : Length)
    (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (hprim : PrimitiveRegularity L η P.val.2 B f) :
    ∃ ψ : Circle L → ℝ, Continuous ψ ∧
      ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength L),
        ∀ k : ℤ, coeff L ⟨(fun x => (ψ x : ℂ)), complexL2Integrable L _ hψ⟩ k =
          transportCoeffs P L f k := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨Xi, hXi, hprim⟩ := hprim
  let τ : ℝ := 1 - P.val.2
  have hτ : 0 < τ := by dsimp [τ]; linarith [P.property.2.2]
  have hr : τ < 1 - P.val.2 + η := by dsimp [τ]; linarith
  let J : Circle L → ℝ := fun x => ∫ u : ℝ,
    (Xi.val x - Xi.val (x - (u : Circle L))) * |u| ^ (-(1 + τ))
  have hJ := holderBound_singular_integral hXi hτ hr hB
  let c : ℝ := -((2 * Real.pi) ^ τ / (2 * P.val.1 * rieszConstant (parametersExponent P) * levyIntegral τ))
  let ψ : Circle L → ℝ := fun x => c * J x
  have hc : Continuous ψ := hJ.2.1.const_mul c
  have hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength L) := by
    change MemLp (fun x => (ψ x : ℂ)) 2 volume
    exact (Complex.continuous_ofReal.comp hc).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨ψ, hc, hψ, fun k => ?_⟩
  have hcoef : fourierCoeff (fun x => (J x : ℂ)) k =
      ((|(k : ℝ) / L.val| ^ τ * levyIntegral τ : ℝ) : ℂ) *
        fourierCoeff (fun x => (Xi.val x : ℂ)) k :=
    Internal.fourierCoeff_holder_singular_integral hτ hr hB Xi.val hXi.1
      (holderBound_residual_le hXi (by linarith) hB) (holderBound_residual_le_two hXi) k
  change fourierCoeff (fun x => ((c * J x : ℝ) : ℂ)) k = transportCoeffs P L f k
  simp only [Complex.ofReal_mul]
  rw [fourierCoeff.const_mul, hcoef]
  by_cases hk : k = 0
  · subst k
    simp only [Int.cast_zero, zero_div, abs_zero, Real.zero_rpow hτ.ne', zero_mul,
      Complex.ofReal_zero, mul_zero, transportCoeffs, ite_true]
  · have hpk := hprim k hk
    change (2 * Real.pi * Complex.I * (k : ℂ) / L.val) *
      fourierCoeff (fun x => (Xi.val x : ℂ)) k =
        fourierCoeff (fun x => (f.val x : ℂ)) k at hpk
    unfold transportCoeffs
    rw [ite_eq_right hk]
    change (c : ℂ) * (((|(k : ℝ) / L.val| ^ τ * levyIntegral τ : ℝ) : ℂ) *
      fourierCoeff (fun x => (Xi.val x : ℂ)) k) =
        -((|2 * Real.pi * (k : ℝ) / L.val| ^ τ : ℝ) : ℂ) /
          ((2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) *
            (2 * Real.pi * Complex.I * (k : ℂ) / L.val)) *
          fourierCoeff (fun x => (f.val x : ℂ)) k
    rw [← hpk]
    have hfreq : |2 * Real.pi * (k : ℝ) / L.val| ^ τ =
        (2 * Real.pi) ^ τ * |(k : ℝ) / L.val| ^ τ := by
      rw [show 2 * Real.pi * (k : ℝ) / L.val = (2 * Real.pi) * ((k : ℝ) / L.val) by ring,
        abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi),
        Real.mul_rpow (by positivity) (abs_nonneg _)]
    have hc0 : (2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) ≠ 0 := by
      exact ne_of_gt (mul_pos (mul_pos (by norm_num) P.property.1) (rieszConstant_pos _))
    have hI : levyIntegral τ ≠ 0 := (levyIntegral_pos hτ (by dsimp [τ]; linarith [P.property.2.1])).ne'
    have hω : (2 * Real.pi * Complex.I * (k : ℂ) / (L.val : ℂ)) ≠ 0 := by
      apply div_ne_zero
      · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast hk)
      · exact_mod_cast L.property.ne'
    rw [hfreq]
    dsimp [c]
    push_cast
    field_simp [hI, L.property.ne']
end Riesz1
