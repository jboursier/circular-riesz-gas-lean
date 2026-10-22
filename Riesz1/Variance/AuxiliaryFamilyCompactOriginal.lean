/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryFamilyDerivativeEnvelope
public import Riesz1.Variance.RegMicroMarksComplete
public import Riesz1.Variance.AuxiliaryFamilyEnergyEnvelope
public import Riesz1.Variance.AuxiliaryReductionIdentity
public import Riesz1.CLT.ErrorTwoFinalCompact
public import Riesz1.CLT.ErrorOneBridge
public import Riesz1.Variance.RegUniformComplete

/-!
# Both auxiliary estimates for original compact profiles

The two analytic steps of Proposition 5.6, with constants
before the shrinking sequence and all its initial circles. The exponent
may be increased to treat the endpoint before absorbing the loss.
-/

public section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace Riesz1.Internal

/-- The sharp derivative-statistic variance and energy bounds for an
original compact profile. All constants precede the scale sequence. -/
theorem auxiliary_family_compact_original_estimates (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (hp : CompactProfile p) (d : TestData)
    (α α' ε : ℝ) (hε : 0 < ε)
    (hη : 0 < d.1) (hB : 0 ≤ d.2.1) (hC₀ : 0 ≤ d.2.2.1)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hαα' : α ≤ α')
    (hα'0 : P.val.2 - 1 < α') (hα'1 : α' < P.val.2 / 2)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (nhds 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) d.1 P.val.2 d.2.1
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            d.2.2.2.1 d.2.2.2.2 α d.2.2.1) →
      ∀ N : ℕ+, 1 ≤ (N : ℝ) * (ell N).val →
        ∀ ψ : Circle (loopMasterLength (ell N)) → ℝ,
          ∀ hψ : ContDiff ℝ ∞ (fun x : ℝ => ψ (x : Circle (loopMasterLength (ell N)))),
            (∀ k : ℤ, coeff (loopMasterLength (ell N))
              ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _
                (loopMasterLengthTest _ ψ hψ).property⟩ k =
              transportCoeffs P (loopMasterLength (ell N))
                (loopMasterLengthTest _ (cltReg hρ P N (ell N)
                  ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩)
                  (cltReg_contDiff hρ P N (ell N) _)) k) →
            ∃ hQ : MemLp (fun X : Configuration N =>
              fluctIntegral (fun u => deriv (loopMasterProfile (ell N) ψ hψ).val
                (u / (ell N).val)) N X.val) 2 (gibbsMeasure P N),
              variance (gibbsMeasure P N) _ (hQ.integrable one_le_two) ≤ ENNReal.ofReal
                (C * (((N : ℝ) * (ell N).val) ^ ε * (((N : ℝ) * (ell N).val) ^ P.val.2 +
                  ((N : ℝ) * (ell N).val) ^ (2 * (1 - P.val.2 + α'))))) ∧
              bellEnergy (ell N).val (loopMasterProfile (ell N) ψ hψ).val ≤
                C * (((N : ℝ) * (ell N).val) ^ ε *
                  (1 + ((N : ℝ) * (ell N).val) ^ (2 * (1 - P.val.2 + α') - 1))) := by
  obtain ⟨m, marks, Cmark, δmark, hCmark, hδmark, hsepmark, hreplace, _⟩ :=
    regMicro_compact_family_marks P p hp d.1 d.2.1 d.2.2.1 α d.2.2.2.1 d.2.2.2.2
      hη hB hC₀ hα0 hα1
  let d' : TestData := ⟨d.1, d.2.1, Cmark, ⟨m, marks⟩⟩
  let b := 1 - P.val.2 + α'
  have hb : 0 ≤ b := by dsimp [b]; linarith
  obtain ⟨C₁, hC₁, hT1⟩ := regUniform_firstTransport_compact P p hp d'.1 d'.2.1
    d'.2.2.2.1 d'.2.2.2.2 α α' d'.2.2.1 hη hB hCmark.le hα0 hα1 hαα' hα'0 hα'1 ρ hρ
  obtain ⟨C₂, hC₂, hT2⟩ := regUniform_secondTransport_compact P p hp d'.1 d'.2.1
    d'.2.2.2.1 d'.2.2.2.2 α α' d'.2.2.1 hη hB hCmark.le hα0 hα1 hαα' hα'0 hα'1 ρ hρ
  obtain ⟨Ct, hCt, hTails⟩ := regUniform_transportTails_compact P p hp d'.1 d'.2.1
    d'.2.2.2.1 d'.2.2.2.2 α α' d'.2.2.1 hη hB hCmark.le hα0 hα1 hαα' hα'0 hα'1 ρ hρ
  let A := C₁ + C₂ + Ct
  have hA : 0 < A := by dsimp [A]; positivity
  have h₁ : C₁ ≤ A := by dsimp [A]; linarith
  have h₂ : C₂ ≤ A := by dsimp [A]; linarith
  have htA : Ct ≤ A := by dsimp [A]; linarith
  obtain ⟨V, hV, hvariance⟩ := auxiliary_family_derivative_envelopes hBE hPL P (d'.2.2.2.1 : ℕ)
    d'.2.2.2.2 δmark hδmark b ε hb hε
  obtain ⟨D, hD, henergy⟩ := auxiliary_family_transport_energy_envelopes
    (d'.2.2.2.1 : ℕ) d'.2.2.2.2 P.property.2.2 hb hε
  let C := (V + D + 1) * A ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hVC : V * A ^ 2 ≤ C := by dsimp [C]; nlinarith [sq_nonneg A]
  have hDC : D * A ^ 2 ≤ C := by dsimp [C]; nlinarith [sq_nonneg A]
  refine ⟨C, hC, fun ell hell hdata N hK ψ hψ htr => ?_⟩
  have hreg : ∀ N,
      PrimitiveRegularity (observationLength (ell N)) d'.1 P.val.2 d'.2.1
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
      TransportRegularity P (observationLength (ell N))
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
          d'.2.2.2.1 d'.2.2.2.2 α d'.2.2.1 :=
    fun N => ⟨(hdata N).1, hreplace ell hell hdata (ell N) (hdata N).1⟩
  let a := ell N
  have hsepc (i k : Fin (m : ℕ)) (hik : i ≠ k) :
      δmark ≤ circDist a.val⁻¹ (marks i - marks k) := by
    have ht := hsepmark a i k hik
    rw [dist_coe_eq_circDist_sub (observationLength a).property,
      show (observationLength a).val = a.val⁻¹ from rfl] at ht
    exact ht
  let Ψ := loopMasterProfile a ψ hψ
  have hΨ : ContDiff ℝ ∞ Ψ.val := hψ
  have hΨp : Function.Periodic Ψ.val a.val⁻¹ := Ψ.property.1
  have hh := cltDelta_pos P N a
  have hh1 := cltDelta_le_one P N a hK
  obtain ⟨ψ₁, hc₁, hm₁, hf₁, hb₁⟩ := hT1 ell hell hreg a (hreg N).1 (hreg N).2
  obtain ⟨ψ₂, hc₂, hm₂, hf₂, hb₂⟩ := hT2 ell hell hreg a (hreg N).1 (hreg N).2
  obtain ⟨ψt, hct, hmt, hft, hbt⟩ := hTails ell hell hreg a (hreg N).1 (hreg N).2
  have he₂ : ψ₂ = ψ₁ := continuous_eq_of_coeff_eq hc₂ hc₁ hm₂ hm₁
    (fun k => (hf₂ k).trans (hf₁ k).symm)
  have het : ψt = ψ₁ := continuous_eq_of_coeff_eq hct hc₁ hmt hm₁
    (fun k => (hft k).trans (hf₁ k).symm)
  have he : Ψ.val = circleMollify ρ (observationLength a).val (cltDelta P N a)
      (fun t : ℝ => ψ₁ (t : Circle (observationLength a))) :=
    funext (loopMasterProfile_eq_circleMollify hρ P N a p ψ hψ htr ψ₁ hm₁ hf₁)
  have hval (x : ℝ) : |deriv Ψ.val x| ≤ A * (1 + ∑ j,
      max (circDist a.val⁻¹ (x - d'.2.2.2.2 j)) (cltDelta P N a) ^ (-b)) := by
    have hh' := hb₁ (cltDelta P N a) hh hh1 x
    rw [← he] at hh'
    simp only [dist_coe_eq_circDist_sub (observationLength a).property,
      show -1 + P.val.2 - α' = -b by dsimp [b]; ring] at hh'
    exact hh'.trans (mul_le_mul_of_nonneg_right h₁ (by positivity))
  have hder (x : ℝ) : |deriv (deriv Ψ.val) x| ≤ A * (1 + ∑ j,
      max (circDist a.val⁻¹ (x - d'.2.2.2.2 j)) (cltDelta P N a) ^ (-1 - b)) := by
    have hh' := hb₂ (cltDelta P N a) hh hh1 x
    rw [he₂, ← he] at hh'
    simp only [dist_coe_eq_circDist_sub (observationLength a).property,
      show -2 + P.val.2 - α' = -1 - b by dsimp [b]; ring] at hh'
    exact hh'.trans (mul_le_mul_of_nonneg_right h₂ (by positivity))
  have htail (x : ℝ) (hx : 2 ≤ circDist a.val⁻¹ x) :
      |deriv Ψ.val x| ≤ A * circDist a.val⁻¹ x ^ (P.val.2 - 2) ∧
        |deriv (deriv Ψ.val) x| ≤ A * circDist a.val⁻¹ x ^ (P.val.2 - 3) := by
    have hcentral (y : ℝ) (hy : 2 ≤ |y|) (hyL : |y| ≤ a.val⁻¹ / 2) :=
      hbt (cltDelta P N a) hh hh1 y hy hyL
    simp only [het, ← he] at hcentral
    have hh' := tail_of_central (inv_pos.mpr a.property.1) hΨp hcentral x hx
    exact ⟨hh'.1.trans (mul_le_mul_of_nonneg_right htA (by positivity)),
      hh'.2.trans (mul_le_mul_of_nonneg_right htA (by positivity))⟩
  obtain ⟨hi, hbnd⟩ := hvariance N a hK hsepc (cltDelta P N a) A hh
    (cltDelta_ge_inv P N a hK) hA.le (deriv Ψ.val)
    (contDiff_infty_iff_deriv.mp hΨ).2 (Riesz1.periodic_deriv hΨp) hval hder htail
  have hmem := auxiliary_derivative_stat_memLp P N a Ψ hΨ
  refine ⟨hmem, ?_, ?_⟩
  · apply hbnd.trans (ENNReal.ofReal_le_ofReal ?_)
    have hm := mul_le_mul_of_nonneg_right hVC
      (show 0 ≤ ((N : ℝ) * a.val) ^ ε * (((N : ℝ) * a.val) ^ P.val.2 +
        ((N : ℝ) * a.val) ^ (2 * b)) by positivity)
    exact hm
  · have he := henergy a.val ((N : ℝ) * a.val) (cltDelta P N a) A a.property.1 hK
      hh (cltDelta_ge_inv P N a hK) hA.le Ψ.val hΨ hΨp hval
      (fun x hx => (htail x hx).1)
    exact he.trans (mul_le_mul_of_nonneg_right hDC (by positivity))

end Riesz1.Internal
