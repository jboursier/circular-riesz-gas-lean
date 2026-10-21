/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityRepresentative

/-!
# A uniform supremum bound for the admissible transport

Quantitative representative construction. The singular-integral
majorant and its normalization depend only on the primitive data and model parameters.
The bound is chosen before the circle length and the profile on that circle.
-/

public section

open MeasureTheory

namespace Riesz1

/-- The continuous transport supplied by (A1) has a bound independent of circle length.
This retains the bound of the singular-integral construction. -/
theorem exists_uniform_bounded_transport (P : Parameters) (η B : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (L : Length)
      (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}),
      PrimitiveRegularity L η P.val.2 B f →
      ∃ ψ : Circle L → ℝ, Continuous ψ ∧
        ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength L),
          (∀ x, |ψ x| ≤ M) ∧
          ∀ k : ℤ, coeff L ⟨(fun x => (ψ x : ℂ)), complexL2Integrable L _ hψ⟩ k =
            transportCoeffs P L f k := by
  let τ : ℝ := 1 - P.val.2
  let c : ℝ := -((2 * Real.pi) ^ τ /
    (2 * P.val.1 * rieszConstant (parametersExponent P) * levyIntegral τ))
  refine ⟨|c| * (∫ u : ℝ, holderSingularEnvelope τ (1 - P.val.2 + η) B u),
    mul_nonneg (abs_nonneg c) (integral_nonneg (holderSingularEnvelope_nonneg hB)), ?_⟩
  intro L f hprim
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨Xi, hXi, hprim⟩ := hprim
  have hτ : 0 < τ := by dsimp [τ]; linarith [P.property.2.2]
  have hr : τ < 1 - P.val.2 + η := by dsimp [τ]; linarith
  let J : Circle L → ℝ := fun x => ∫ u : ℝ,
    (Xi.val x - Xi.val (x - (u : Circle L))) * |u| ^ (-(1 + τ))
  have hJ := holderBound_singular_integral hXi hτ hr hB
  let ψ : Circle L → ℝ := fun x => c * J x
  have hc : Continuous ψ := hJ.2.1.const_mul c
  have hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength L) := by
    change MemLp (fun x => (ψ x : ℂ)) 2 volume
    exact (Complex.continuous_ofReal.comp hc).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨ψ, hc, hψ, ?_, ?_⟩
  · intro x
    dsimp [ψ]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hJ.2.2 x) (abs_nonneg c)
  · intro k
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

namespace Internal

/-- Every continuous representative with the transport coefficients has the same
uniform bound. The representative premises identify the object in this internal helper. -/
theorem continuous_transport_uniform_bound (P : Parameters) (η B : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (L : Length)
      (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}),
      PrimitiveRegularity L η P.val.2 B f →
      ∀ (ψ : Circle L → ℝ), Continuous ψ →
      ∀ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength L),
      (∀ k : ℤ, coeff L ⟨(fun x => (ψ x : ℂ)), complexL2Integrable L _ hψ⟩ k =
        transportCoeffs P L f k) → ∀ x, |ψ x| ≤ M := by
  obtain ⟨M, hM, hb⟩ := exists_uniform_bounded_transport P η B hη hB
  refine ⟨M, hM, fun L f hp ψ hc hψ hcoeff => ?_⟩
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨g, hgc, hg, hgb, hcoeffg⟩ := hb L f hp
  have heqC : (fun x => (ψ x : ℂ)) =ᵐ[arclength L] (fun x => (g x : ℂ)) := by
    apply CircleFourier.ae_eq_of_coeff_eq hψ hg
    intro k
    exact (hcoeff k).trans (hcoeffg k).symm
  have heq : ψ =ᵐ[arclength L] g := by
    filter_upwards [heqC] with x hx
    exact Complex.ofReal_injective hx
  have heq' : ψ = g := Measure.eq_of_ae_eq (show ψ =ᵐ[volume] g from heq) hc hgc
  simpa only [heq'] using hgb

end Internal

/-- The (A1) supremum bound and (A2)–(A3) hold for the same continuous representative,
with the supremum bound chosen before every circle and all marked-point data. -/
theorem exists_uniform_regular_transport (P : Parameters) (η B : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (L : Length)
      (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
      (p : ℕ+) (marks : Fin (p : ℕ) → ℝ) (α C : ℝ),
      PrimitiveRegularity L η P.val.2 B f → TransportRegularity P L f p marks α C →
      ∃ ψ : Circle L → ℝ, Continuous ψ ∧
        ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength L),
          (∀ k : ℤ, coeff L ⟨(fun x => (ψ x : ℂ)), complexL2Integrable L _ hψ⟩ k =
            transportCoeffs P L f k) ∧
          (∀ x, |ψ x| ≤ M) ∧
          ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
            ContDiffAt ℝ 2 (fun t : ℝ => ψ (t : Circle L)) x ∧
            |deriv (deriv (fun t : ℝ => ψ (t : Circle L))) x| ≤ C *
              ((if dist (x : Circle L) 0 ≤ 1 then
                  ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - α)
                else 0) +
               (if 1 ≤ dist (x : Circle L) 0 then
                  dist (x : Circle L) 0 ^ (-3 + P.val.2) else 0)) := by
  obtain ⟨M, hM, hbound⟩ := Internal.continuous_transport_uniform_bound P η B hη hB
  refine ⟨M, hM, fun L f p marks α C hprim hreg => ?_⟩
  obtain ⟨ψ, hc, hψ, hcoeff, hpoint⟩ :=
    exists_continuous_transport_with_regularity P L η B hη hB f p marks α C hprim hreg
  exact ⟨ψ, hc, hψ, hcoeff, hbound L f hprim ψ hc hψ hcoeff, hpoint⟩

end Riesz1
