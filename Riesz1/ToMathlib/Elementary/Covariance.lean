/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Covariance signs for monotone functions of a random variable

Chebyshev's association inequality: if `a` and `b` are monotone on a set `I` that contains the
values of `Y`, then `Cov(a(Y), b(Y)) ≥ 0`. If `a` is antitone and `b` is monotone, then the
covariance is nonpositive.

The proof works on the product `P.prod P`, where the two coordinates are independent copies
`Y₁`, `Y₂` of `Y`. The integrand `(a(Y₁) - a(Y₂)) (b(Y₁) - b(Y₂))` is nonnegative pointwise,
and its integral is `2 Cov(a(Y), b(Y))`.

This is part of Lemma 4.5 of the paper.
-/

public section

open MeasureTheory

namespace Riesz1

/-- Chebyshev's association inequality for monotone functions of a random variable with values
in `I` (Lemma 4.5). -/
theorem covariance_nonneg_of_monotone {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {I : Set ℝ} (Y : Ω → ℝ) (hYI : ∀ ω, Y ω ∈ I)
    (a b : ℝ → ℝ) (ha : MonotoneOn a I) (hb : MonotoneOn b I)
    (hia : Integrable (fun ω => a (Y ω)) P) (hib : Integrable (fun ω => b (Y ω)) P)
    (hiab : Integrable (fun ω => a (Y ω) * b (Y ω)) P) :
    0 ≤ ∫ ω, a (Y ω) * b (Y ω) ∂P - (∫ ω, a (Y ω) ∂P) * ∫ ω, b (Y ω) ∂P := by
  -- Both differences have the same sign as the difference of their arguments.
  have hsign : ∀ z : Ω × Ω, 0 ≤ (a (Y z.1) - a (Y z.2)) * (b (Y z.1) - b (Y z.2)) := by
    intro z
    rcases le_total (Y z.1) (Y z.2) with h | h
    · have h1 : a (Y z.1) ≤ a (Y z.2) := ha (hYI z.1) (hYI z.2) h
      have h2 : b (Y z.1) ≤ b (Y z.2) := hb (hYI z.1) (hYI z.2) h
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 h1) (sub_nonpos.2 h2)
    · have h1 : a (Y z.2) ≤ a (Y z.1) := ha (hYI z.2) (hYI z.1) h
      have h2 : b (Y z.2) ≤ b (Y z.1) := hb (hYI z.2) (hYI z.1) h
      exact mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)
  -- Integrability of the four terms of the expansion on the product space.
  have hI1 : Integrable (fun z : Ω × Ω => a (Y z.1) * b (Y z.1)) (P.prod P) :=
    hiab.comp_fst P
  have hI2 : Integrable (fun z : Ω × Ω => a (Y z.2) * b (Y z.2)) (P.prod P) :=
    hiab.comp_snd P
  have hI3 : Integrable (fun z : Ω × Ω => a (Y z.1) * b (Y z.2)) (P.prod P) :=
    hia.mul_prod hib
  have hI4 : Integrable (fun z : Ω × Ω => b (Y z.1) * a (Y z.2)) (P.prod P) :=
    hib.mul_prod hia
  -- Each term of the expansion, with its value under `P.prod P`.
  have J1 : ∫ z, a (Y z.1) * b (Y z.1) ∂(P.prod P) = ∫ ω, a (Y ω) * b (Y ω) ∂P := by
    simpa using integral_fun_fst (μ := P) (ν := P) (fun ω => a (Y ω) * b (Y ω))
  have J2 : ∫ z, a (Y z.2) * b (Y z.2) ∂(P.prod P) = ∫ ω, a (Y ω) * b (Y ω) ∂P := by
    simpa using integral_fun_snd (μ := P) (ν := P) (fun ω => a (Y ω) * b (Y ω))
  have J3 : ∫ z, a (Y z.1) * b (Y z.2) ∂(P.prod P)
      = (∫ ω, a (Y ω) ∂P) * ∫ ω, b (Y ω) ∂P :=
    integral_prod_mul (μ := P) (ν := P) (fun ω => a (Y ω)) (fun ω => b (Y ω))
  have J4 : ∫ z, b (Y z.1) * a (Y z.2) ∂(P.prod P)
      = (∫ ω, b (Y ω) ∂P) * ∫ ω, a (Y ω) ∂P :=
    integral_prod_mul (μ := P) (ν := P) (fun ω => b (Y ω)) (fun ω => a (Y ω))
  -- The integral of the product of differences is twice the covariance.
  have hexp : ∫ z, (a (Y z.1) - a (Y z.2)) * (b (Y z.1) - b (Y z.2)) ∂(P.prod P)
      = 2 * (∫ ω, a (Y ω) * b (Y ω) ∂P - (∫ ω, a (Y ω) ∂P) * ∫ ω, b (Y ω) ∂P) := by
    have hsplit : (fun z : Ω × Ω => (a (Y z.1) - a (Y z.2)) * (b (Y z.1) - b (Y z.2)))
        = fun z => a (Y z.1) * b (Y z.1) + a (Y z.2) * b (Y z.2)
          - a (Y z.1) * b (Y z.2) - b (Y z.1) * a (Y z.2) := by
      funext z
      ring
    have hA : Integrable (fun z : Ω × Ω => a (Y z.1) * b (Y z.1) + a (Y z.2) * b (Y z.2))
        (P.prod P) := hI1.add hI2
    have hB : Integrable (fun z : Ω × Ω => a (Y z.1) * b (Y z.1) + a (Y z.2) * b (Y z.2)
        - a (Y z.1) * b (Y z.2)) (P.prod P) := hA.sub hI3
    rw [hsplit, integral_sub hB hI4, integral_sub hA hI3, integral_add hI1 hI2, J1, J2, J3, J4]
    ring
  have hnonneg : 0 ≤ ∫ z, (a (Y z.1) - a (Y z.2)) * (b (Y z.1) - b (Y z.2)) ∂(P.prod P) :=
    integral_nonneg hsign
  rw [hexp] at hnonneg
  linarith

/-- Chebyshev's association inequality for an antitone and a monotone function of a random
variable with values in `I` (Lemma 4.5). -/
theorem covariance_nonpos_of_antitone_monotone {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {I : Set ℝ} (Y : Ω → ℝ) (hYI : ∀ ω, Y ω ∈ I)
    (a b : ℝ → ℝ) (ha : AntitoneOn a I) (hb : MonotoneOn b I)
    (hia : Integrable (fun ω => a (Y ω)) P) (hib : Integrable (fun ω => b (Y ω)) P)
    (hiab : Integrable (fun ω => a (Y ω) * b (Y ω)) P) :
    ∫ ω, a (Y ω) * b (Y ω) ∂P - (∫ ω, a (Y ω) ∂P) * ∫ ω, b (Y ω) ∂P ≤ 0 := by
  have hna : MonotoneOn (fun x => -a x) I := fun x hx y hy hxy => neg_le_neg (ha hx hy hxy)
  have hia' : Integrable (fun ω => -a (Y ω)) P := hia.neg
  have hiab' : Integrable (fun ω => -a (Y ω) * b (Y ω)) P := by
    simp only [neg_mul]
    exact hiab.neg
  have h := covariance_nonneg_of_monotone (P := P) Y hYI (fun x => -a x) b hna hb hia' hib
    hiab'
  simp only [neg_mul, integral_neg] at h
  linarith

end Riesz1
