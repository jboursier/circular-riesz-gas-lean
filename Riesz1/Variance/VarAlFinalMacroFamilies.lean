/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlFinalMacro
public import Riesz1.Variance.RegUniformFamilyTransportBounds

/-!
# One macroscopic loop coefficient for both convolution families

Proposition 5.9 and the uniformity argument of
Theorem 2, on the macroscopic circle.
The additional family radius ranges over its entire interval `(0,1]`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Riesz1.Internal

/-- Uniform variance for the macroscopic analytic envelope class. -/
theorem varAlFinal_macro_envelopes
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (n : ℕ) (marks : Fin n → ℝ)
    (hinj : Function.Injective (fun j => (marks j : Circle unitLength)))
    {α S A ε : ℝ} (hα : P.val.2 - 1 < α) (hα2 : α < P.val.2 / 2)
    (hS : 0 ≤ S) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (h : ℝ), (N : ℝ)⁻¹ ≤ h →
      ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → Function.Periodic F 1 →
      (∀ x, |F x| ≤ S) →
      (∀ x, |deriv F x| ≤ A * (1 + ∑ j,
        max (circDist 1 (x - marks j)) h ^ (-(1 - P.val.2 + α)))) →
      (∀ x, |deriv (deriv F) x| ≤ A * (1 + ∑ j,
        max (circDist 1 (x - marks j)) h ^ (-1 - (1 - P.val.2 + α)))) →
      ∃ hi : Integrable (fun X : Configuration N =>
          loopFunctional P.val.2 (N : ℕ) (loopScaleField 1 F) X.val) (gibbsMeasure P N),
        variance (gibbsMeasure P N) _ hi ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (ε + max 1 (2 * (1 - P.val.2 + α)))) := by
  obtain ⟨E, hE, he⟩ := varAlPiecesUniform_macro n marks hinj
    (s := P.val.2) (b := 1 - P.val.2 + α) (by linarith) hS hA
  obtain ⟨C, hC, hv⟩ := varAlFinal_finite_pieces hBE hPL P (n + 1) hα.le hα2 hE hε
  refine ⟨C, hC, fun N h hh F hF hp hsup h1 h2 => ?_⟩
  have hN : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ (N : ℕ) from N.pos)
  obtain ⟨φ, hφ, hsum, henv⟩ := he (N : ℝ) h hN hh F hF hp hsup h1 h2
  obtain ⟨hi, hbound⟩ := hv N 1 F φ one_pos le_rfl (by simpa using hN)
    (by simpa only [inv_one] using hφ) hsum
    (by simpa only [mul_one, inv_one] using henv)
  exact ⟨hi, by simpa only [mul_one] using hbound⟩

/-- A common coefficient for the actual smoothed transport and its
difference from the original transport. The two coefficient identities
identify exactly the transports of the two convolution families.
This internal form retains the representatives supplied by the analytic API. -/
theorem varAlFinal_macro_transport_families
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (hα : P.val.2 - 1 ≤ α) (hα2 : α < P.val.2 / 2)
    (hη : 0 < d.1) (hB : 0 < d.2.1) (hC₀ : 0 < d.2.2.1)
    (hprim : PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩
      d.2.2.2.1 d.2.2.2.2 α d.2.2.1)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∃ ψ : {f : Circle unitLength → ℝ //
        MemLp (fun x => (f x : ℂ)) 2 (arclength unitLength)},
        Continuous ψ.val ∧
        (∀ k, coeff unitLength ⟨(fun x => (ψ.val x : ℂ)),
          complexL2Integrable _ _ ψ.property⟩ k =
            transportCoeffs P unitLength ⟨p.val, p.property⟩ k) ∧
        ∀ t : ℝ, 0 < t → t ≤ 1 →
          ∃ φ χ : {f : Circle unitLength → ℝ //
            MemLp (fun x => (f x : ℂ)) 2 (arclength unitLength)},
            (∀ x : ℝ, φ.val (x : Circle unitLength) =
              circleMollify ρ 1 t (fun y : ℝ => ψ.val (y : Circle unitLength)) x) ∧
            (∀ x, χ.val x = ψ.val x - φ.val x) ∧
            (∀ k, coeff unitLength ⟨(fun x => (φ.val x : ℂ)),
                complexL2Integrable _ _ φ.property⟩ k =
              transportCoeffs P unitLength ⟨p.val, p.property⟩ k *
                (mollifierFT ρ (t * k) : ℂ)) ∧
            (∀ k, coeff unitLength ⟨(fun x => (χ.val x : ℂ)),
                complexL2Integrable _ _ χ.property⟩ k =
              transportCoeffs P unitLength ⟨p.val, p.property⟩ k -
              transportCoeffs P unitLength ⟨p.val, p.property⟩ k *
                (mollifierFT ρ (t * k) : ℂ)) ∧
            ∀ v, (v = φ ∨ v = χ) →
              ∀ (N : ℕ+) (h : ℝ), (N : ℝ)⁻¹ ≤ h → h ≤ 1 →
                ∃ hi : Integrable (fun X : Configuration N => loopFunctional P.val.2 (N : ℕ)
                    (loopScaleField 1 (circleMollify ρ 1 h
                      (fun y : ℝ => v.val (y : Circle unitLength)))) X.val) (gibbsMeasure P N),
                  variance (gibbsMeasure P N) _ hi ≤ ENNReal.ofReal
                    (C * (N : ℝ) ^ (ε + max 1 (2 * (1 - P.val.2 + α)))) := by
  obtain ⟨α', hα'0, hα'2, hαα', hpow⟩ := varAlFinal_interior_exponent P.2.2.2 hα hα2
  obtain ⟨A, hA, ψ, hc, hf, hfamily⟩ := regUniform_familyTransport_macroscopic P p
    d.1 d.2.1 d.2.2.2.1 d.2.2.2.2 α α' d.2.2.1 hη hB.le hC₀.le
    hα hα2 hαα' hα'0 hα'2 hprim hreg ρ hρ
  obtain ⟨C, hC, hvariance⟩ := varAlFinal_macro_envelopes hBE hPL P
    (d.2.2.2.1 : ℕ) d.2.2.2.2 hreg.1 hα'0 hα'2 hA.le hA.le hε
  refine ⟨C, hC, ψ, hc, hf, fun t ht ht1 => ?_⟩
  obtain ⟨φ, χ, hφ, hχ, hfφ, hfχ, hbound⟩ := hfamily t ht ht1
  refine ⟨φ, χ, hφ, hχ, ?_, ?_, fun v hv N h hh hh1 => ?_⟩
  · simpa only [hf, show unitLength.val = 1 from rfl, div_one] using hfφ
  · simpa only [hfχ, hfφ, hf, show unitLength.val = 1 from rfl, div_one] using hfχ
  · have hN : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ (N : ℕ) from N.pos)
    have hh0 : 0 < h := lt_of_lt_of_le (inv_pos.mpr (by linarith : 0 < (N : ℝ))) hh
    obtain ⟨hvc, _, hb⟩ := hbound v hv
    have hp : Function.Periodic (fun y : ℝ => v.val (y : Circle unitLength)) 1 := by
      change Function.Periodic _ unitLength.val
      intro y
      simp only [AddCircle.coe_add_period]
    have hi : LocallyIntegrable (fun y : ℝ => v.val (y : Circle unitLength)) volume :=
      (hvc.comp (AddCircle.continuous_mk' unitLength.val)).locallyIntegrable
    have hsm := contDiff_circleMollify hρ one_pos hh0 hi hp
    have hper := circleMollify_periodic hρ one_pos hh0 hi hp
    have h1 := fun x => (hb h hh0 hh1 x).2.1
    have h2 := fun x => (hb h hh0 hh1 x).2.2
    simp only [dist_coe_eq_circDist_sub unitLength.property,
      show -1 + P.val.2 - α' = -(1 - P.val.2 + α') by ring,
      show -2 + P.val.2 - α' = -1 - (1 - P.val.2 + α') by ring] at h1 h2
    obtain ⟨hL, hV⟩ := hvariance N h hh _ hsm hper
      (fun x => (hb h hh0 hh1 x).1) h1 h2
    exact ⟨hL, by simpa only [hpow] using hV⟩

end Riesz1.Internal

end
