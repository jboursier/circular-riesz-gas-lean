/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlFinalPieces
public import Riesz1.Variance.VarAlPiecesUniformMacro
public import Riesz1.Variance.RegUniformSecondTransport
public import Riesz1.Variance.RegUniformTransport
public import Riesz1.Frozen.TestData

/-!
# Loop variance for a fixed macroscopic profile

Proposition 5.9, the macroscopic branch, including the endpoint
exponent and every particle count and smoothing radius.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Riesz1.Internal

/-- An interior exponent with exactly the same final loop power. -/
theorem varAlFinal_interior_exponent {s α : ℝ} (hs : s < 1)
    (hα : s - 1 ≤ α) (hα2 : α < s / 2) :
    ∃ α' : ℝ, s - 1 < α' ∧ α' < s / 2 ∧ α ≤ α' ∧
      max 1 (2 * (1 - s + α')) = max 1 (2 * (1 - s + α)) := by
  rcases eq_or_lt_of_le hα with he | he
  · obtain ⟨α', h0, h1, hp⟩ := varAlLoop_endpoint_exponent hs
    exact ⟨α', h0, h1, by linarith, by simpa only [he] using hp⟩
  · exact ⟨α, he, hα2, le_rfl, rfl⟩

end Riesz1.Internal

namespace Riesz1

/-- Proposition 5.9 on the macroscopic circle. The coefficient
precedes the particle number, smoothing radius, and transport representative.
Only `External.BakryEmery`, `External.PrekopaLeindler` and the actual profile
assumptions are premises. -/
theorem varAl_loop_variance_macroscopic
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (hα : P.val.2 - 1 ≤ α) (hα2 : α < P.val.2 / 2)
    (hη : 0 < d.1) (hB : 0 < d.2.1) (hC₀ : 0 < d.2.2.1)
    (hprim : PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩
      d.2.2.2.1 d.2.2.2.2 α d.2.2.1)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (h : ℝ), (N : ℝ)⁻¹ ≤ h → h ≤ 1 →
      ∀ ψ : {g : Circle unitLength → ℝ //
          MemLp (fun x => (g x : ℂ)) 2 (arclength unitLength)},
        (∀ k, coeff unitLength ⟨(fun x => (ψ.val x : ℂ)),
          complexL2Integrable _ _ ψ.property⟩ k =
            transportCoeffs P unitLength ⟨p.val, p.property⟩ k) →
        ∃ hi : Integrable (fun X : Configuration N => loopFunctional P.val.2 (N : ℕ)
            (loopScaleField 1 (circleMollify ρ 1 h
              (fun t : ℝ => ψ.val (t : Circle unitLength)))) X.val) (gibbsMeasure P N),
          variance (gibbsMeasure P N) _ hi ≤
            ENNReal.ofReal (C * (N : ℝ) ^ (ε + max 1 (2 * (1 - P.val.2 + α)))) := by
  obtain ⟨α', hα'0, hα'2, hαα', hpow⟩ :=
    Internal.varAlFinal_interior_exponent P.2.2.2 hα hα2
  let n := d.2.2.2.1
  let marks := d.2.2.2.2
  obtain ⟨C₁, hC₁, ψ₁, hc₁, hm₁, hf₁, hb₁⟩ := regUniform_firstTransport_macroscopic
    P p d.1 d.2.1 n marks α α' d.2.2.1 hη hB.le hC₀.le hα hα2
    hαα' hα'0 hα'2 hprim hreg ρ hρ
  obtain ⟨C₂, hC₂, ψ₂, hc₂, hm₂, hf₂, hb₂⟩ := regUniform_secondTransport_macroscopic
    P p d.1 d.2.1 n marks α α' d.2.2.1 hη hB.le hC₀.le hα hα2
    hαα' hα'0 hα'2 hprim hreg ρ hρ
  obtain ⟨S, hS, hs⟩ := regUniform_transport_sup P d.1 d.2.1 hη hB.le
  obtain ⟨ψs, hcs, hms, hfs, _, hbs⟩ := hs unitLength ⟨p.val, p.property⟩ hprim
  let A := C₁ + C₂
  have hA : 0 < A := add_pos hC₁ hC₂
  obtain ⟨E, hE, he⟩ := Internal.varAlPiecesUniform_macro (n : ℕ) marks hreg.1
    (s := P.val.2) (b := 1 - P.val.2 + α') (by linarith) hS.le hA.le
  obtain ⟨C, hC, hv⟩ := Internal.varAlFinal_finite_pieces hBE hPL P ((n : ℕ) + 1)
    hα'0.le hα'2 hE hε
  refine ⟨C, hC, fun N h hh hh1 ψ hf => ?_⟩
  have hN : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ (N : ℕ) from N.pos)
  have hh0 : 0 < h := lt_of_lt_of_le (inv_pos.mpr (by linarith : 0 < (N : ℝ))) hh
  have heq₁ : ψ.val =ᵐ[arclength unitLength] ψ₁ :=
    ae_eq_of_coeff_eq_real ψ.property hm₁ (fun k => (hf k).trans (hf₁ k).symm)
  have heq₂ : ψ₂ = ψ₁ := continuous_eq_of_coeff_eq hc₂ hc₁ hm₂ hm₁
    (fun k => (hf₂ k).trans (hf₁ k).symm)
  have heqs : ψs = ψ₁ := continuous_eq_of_coeff_eq hcs hc₁ hms hm₁
    (fun k => (hfs k).trans (hf₁ k).symm)
  let F := circleMollify ρ 1 h (fun t : ℝ => ψ₁ (t : Circle unitLength))
  have hp : Function.Periodic (fun t : ℝ => ψ₁ (t : Circle unitLength)) 1 := by
    change Function.Periodic _ unitLength.val
    intro t
    simp only [AddCircle.coe_add_period]
  have hi : LocallyIntegrable (fun t : ℝ => ψ₁ (t : Circle unitLength)) volume :=
    (hc₁.comp (AddCircle.continuous_mk' unitLength.val)).locallyIntegrable
  have hF : ContDiff ℝ ∞ F := contDiff_circleMollify hρ one_pos hh0 hi hp
  have hFp : Function.Periodic F 1 :=
    Internal.circleMollify_periodic hρ one_pos hh0 hi hp
  have hsup : ∀ x, |F x| ≤ S := by
    intro x
    have hb := hbs ρ hρ h hh0 x
    rw [heqs] at hb
    exact hb
  have h1 : ∀ x, |deriv F x| ≤ A * (1 + ∑ j,
      max (circDist 1 (x - marks j)) h ^ (-(1 - P.val.2 + α'))) := by
    intro x
    have hb := hb₁ h hh0 hh1 x
    simp only [dist_coe_eq_circDist_sub unitLength.property,
      show -1 + P.val.2 - α' = -(1 - P.val.2 + α') by ring] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith)
      (by positivity))
  have h2 : ∀ x, |deriv (deriv F) x| ≤ A * (1 + ∑ j,
      max (circDist 1 (x - marks j)) h ^ (-1 - (1 - P.val.2 + α'))) := by
    intro x
    have hb := hb₂ h hh0 hh1 x
    rw [heq₂] at hb
    simp only [dist_coe_eq_circDist_sub unitLength.property,
      show -2 + P.val.2 - α' = -1 - (1 - P.val.2 + α') by ring] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith)
      (by positivity))
  obtain ⟨φ, hφ, hsum, henv⟩ := he (N : ℝ) h hN hh F hF hFp hsup h1 h2
  have hφ' : ∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) (1 : ℝ)⁻¹ := by
    simpa only [inv_one] using hφ
  obtain ⟨hL, hbound⟩ := hv N 1 F φ one_pos le_rfl (by simpa using hN) hφ' hsum
    (by simpa only [mul_one, inv_one] using henv)
  have hfun : circleMollify ρ 1 h (fun t : ℝ => ψ.val (t : Circle unitLength)) = F :=
    circleMollify_congr_circle ρ unitLength h heq₁
  rw [hfun]
  exact ⟨hL, by simpa only [mul_one, hpow] using hbound⟩

end Riesz1

end
