/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Chamber.PeriodizationIntegrable
public import Riesz1.ToMathlib.EllipticRegularity.WeakEnergy
public import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Square partition cancellation in the cutoff energy

The energy residual of a cutoff multiplied by a strip weight has a
quadratic weight term and one mixed term. The latter cancels exactly
under integer periodization. No gradient of a sum is used.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory MeasureTheory.Measure Set
open scoped ComplexInnerProductSpace

namespace Riesz1.Internal

/-- Square partition averaging cancels the mixed derivative term. -/
theorem finsum_square_partition_linear (t w A B : ℝ) :
    (∑ᶠ k : ℤ, (periodicSquareCutoff (t + k) ^ 2 * A +
      periodicSquareCutoff (t + k) * fderiv ℝ periodicSquareCutoff (t + k) w * B)) = A := by
  have h₁ : HasFiniteSupport (fun k : ℤ => periodicSquareCutoff (t + k) ^ 2 * A) := by
    have hs : HasCompactSupport (fun x : ℝ => periodicSquareCutoff x ^ 2 * A) :=
      (hasCompactSupport_periodicSquareCutoff.comp_left
        (g := fun x : ℝ => x ^ 2) (zero_pow (by norm_num))).mul_right
    simpa only [smul_eq_mul, mul_one] using
      vectorPeriodize_finite_support (v := (1 : ℝ)) one_ne_zero hs t
  have h₂ : HasFiniteSupport (fun k : ℤ => periodicSquareCutoff (t + k) *
      fderiv ℝ periodicSquareCutoff (t + k) w * B) := by
    have hs : HasCompactSupport (fun x : ℝ => periodicSquareCutoff x *
        (fderiv ℝ periodicSquareCutoff x w * B)) := hasCompactSupport_periodicSquareCutoff.mul_right
    have hh := vectorPeriodize_finite_support (v := (1 : ℝ)) one_ne_zero hs t
    simpa only [smul_eq_mul, mul_one, mul_assoc] using hh
  rw [finsum_add_distrib h₁ h₂, ← finsum_mul, ← finsum_mul,
    finsum_periodicSquareCutoff_sq, finsum_periodicSquareCutoff_mul_fderiv,
    one_mul, zero_mul, add_zero]

/-- Integration of a compact square-weight residual over the cover is
exactly integration of its periodic main term over a fundamental strip.
The periodic mixed term contributes zero. Integrability on the strip is
concluded from the compact cover residual. -/
theorem integral_square_partition_residual {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsAddHaarMeasure μ] {v : E} (hv : v ≠ 0)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1) (w : ℝ) {A B : E → ℝ}
    (hA : ∀ (k : ℤ) x, A (x + (k : ℝ) • v) = A x)
    (hB : ∀ (k : ℤ) x, B (x + (k : ℝ) • v) = B x)
    (hc : HasCompactSupport (fun x => periodicSquareCutoff (ℓ x) ^ 2 * A x +
      periodicSquareCutoff (ℓ x) * fderiv ℝ periodicSquareCutoff (ℓ x) w * B x))
    (hI : Integrable (fun x => periodicSquareCutoff (ℓ x) ^ 2 * A x +
      periodicSquareCutoff (ℓ x) * fderiv ℝ periodicSquareCutoff (ℓ x) w * B x) μ) :
    IntegrableOn A (ℓ ⁻¹' Ico (0 : ℝ) 1) μ ∧
      (∫ x in ℓ ⁻¹' Ico (0 : ℝ) 1, A x ∂μ) =
        ∫ x, periodicSquareCutoff (ℓ x) ^ 2 * A x +
          periodicSquareCutoff (ℓ x) * fderiv ℝ periodicSquareCutoff (ℓ x) w * B x ∂μ := by
  have he : vectorPeriodize v hv
      (fun x => periodicSquareCutoff (ℓ x) ^ 2 * A x +
        periodicSquareCutoff (ℓ x) * fderiv ℝ periodicSquareCutoff (ℓ x) w * B x) hc = A := by
    funext x
    simp only [vectorPeriodize, map_add, map_smul, hℓ, smul_eq_mul, mul_one, hA, hB]
    exact finsum_square_partition_linear (ℓ x) w (A x) (B x)
  exact ⟨by simpa only [he] using integrableOn_vectorPeriodize hv ℓ hℓ hc hI,
    by simpa only [he] using integral_vectorPeriodize hv ℓ hℓ hc hI⟩

/-- The scalar residual appearing when a real cutoff multiplies a
complex function and its weak directional derivative. -/
theorem cutoff_energy_residual (a d V : ℝ) (u g : ℂ) :
    ‖d • u + a • g‖ ^ 2 + V * ‖a • u‖ ^ 2 - d ^ 2 * ‖u‖ ^ 2 =
      2 * a * d * RCLike.re (⟪u, g⟫ : ℂ) + a ^ 2 * ‖g‖ ^ 2 +
        V * a ^ 2 * ‖u‖ ^ 2 := by
  rw [cutoff_energy_pointwise]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_add_left, inner_smul_left,
    RCLike.conj_ofReal, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
    map_add, RCLike.mul_re, RCLike.ofReal_re, RCLike.ofReal_im,
    zero_mul, sub_zero, norm_smul, RCLike.norm_ofReal, mul_pow, sq_abs]
  ring

/-- Multiplication by a strip weight changes the energy residual by
one mixed term. This formula keeps every term, including the strip
derivative terms that would be lost by naively periodizing gradients. -/
theorem square_cutoff_energy_residual (r dr b db V : ℝ) (u g : ℂ) :
    ‖(r * db + dr * b) • u + (r * b) • g‖ ^ 2 + V * ‖(r * b) • u‖ ^ 2 -
      (r * db + dr * b) ^ 2 * ‖u‖ ^ 2 =
    r ^ 2 * (‖db • u + b • g‖ ^ 2 + V * ‖b • u‖ ^ 2 - db ^ 2 * ‖u‖ ^ 2) +
      (r * dr) * (2 * b ^ 2 * RCLike.re (⟪u, g⟫ : ℂ)) := by
  rw [cutoff_energy_residual, cutoff_energy_residual]
  ring

/-- Integer translates of the smooth square weight preserve the whole
directional energy residual. The mixed terms cancel exactly. -/
theorem finsum_square_cutoff_energy_residual (t w b db V : ℝ) (u g : ℂ) :
    (∑ᶠ k : ℤ,
      (‖(periodicSquareCutoff (t + k) * db +
          fderiv ℝ periodicSquareCutoff (t + k) w * b) • u +
        (periodicSquareCutoff (t + k) * b) • g‖ ^ 2 +
      V * ‖(periodicSquareCutoff (t + k) * b) • u‖ ^ 2 -
      (periodicSquareCutoff (t + k) * db +
        fderiv ℝ periodicSquareCutoff (t + k) w * b) ^ 2 * ‖u‖ ^ 2)) =
      ‖db • u + b • g‖ ^ 2 + V * ‖b • u‖ ^ 2 - db ^ 2 * ‖u‖ ^ 2 := by
  have h₁ : HasFiniteSupport (fun k : ℤ => periodicSquareCutoff (t + k) ^ 2) := by
    have hs : HasCompactSupport (fun x => periodicSquareCutoff x ^ 2) :=
      hasCompactSupport_periodicSquareCutoff.comp_left
        (g := fun x : ℝ => x ^ 2) (zero_pow (by norm_num))
    simpa only [smul_eq_mul, mul_one] using
      vectorPeriodize_finite_support (v := (1 : ℝ)) one_ne_zero hs t
  have h₂ : HasFiniteSupport (fun k : ℤ => periodicSquareCutoff (t + k) *
      fderiv ℝ periodicSquareCutoff (t + k) w) := by
    have hs : HasCompactSupport (fun x => periodicSquareCutoff x *
        fderiv ℝ periodicSquareCutoff x w) := hasCompactSupport_periodicSquareCutoff.mul_right
    simpa only [smul_eq_mul, mul_one] using
      vectorPeriodize_finite_support (v := (1 : ℝ)) one_ne_zero hs t
  let A := ‖db • u + b • g‖ ^ 2 + V * ‖b • u‖ ^ 2 - db ^ 2 * ‖u‖ ^ 2
  let B := 2 * b ^ 2 * RCLike.re (⟪u, g⟫ : ℂ)
  have h₁' : HasFiniteSupport (fun k : ℤ => periodicSquareCutoff (t + k) ^ 2 * A) := by
    apply Set.Finite.subset h₁
    intro k hk
    change periodicSquareCutoff (t + k) ^ 2 ≠ 0
    intro hz
    exact hk (by change periodicSquareCutoff (t + k) ^ 2 * A = 0; rw [hz, zero_mul])
  have h₂' : HasFiniteSupport (fun k : ℤ => periodicSquareCutoff (t + k) *
      fderiv ℝ periodicSquareCutoff (t + k) w * B) := by
    apply Set.Finite.subset h₂
    intro k hk
    change periodicSquareCutoff (t + k) * fderiv ℝ periodicSquareCutoff (t + k) w ≠ 0
    intro hz
    exact hk (by change (periodicSquareCutoff (t + k) *
      fderiv ℝ periodicSquareCutoff (t + k) w) * B = 0; rw [hz, zero_mul])
  simp_rw [square_cutoff_energy_residual]
  rw [finsum_add_distrib h₁' h₂',
    ← finsum_mul, ← finsum_mul,
    finsum_periodicSquareCutoff_sq, finsum_periodicSquareCutoff_mul_fderiv, one_mul, zero_mul,
    add_zero]

end Riesz1.Internal
