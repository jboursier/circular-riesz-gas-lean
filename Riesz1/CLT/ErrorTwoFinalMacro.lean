/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorTwoFinalCompact
public import Riesz1.CLT.ErrorOneTransfer

/-!
# The macroscopic derivative variance in the loop error

The second error bound in the proof of Theorem 3, on every observation scale of value one.
The periodized profile and its transport coefficients are
transferred using the unit-circle bridges.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace Riesz1.Internal

/-- Macroscopic derivative variance, with the constant chosen before the scale and
any permitted increased singularity exponent. -/
theorem errorTwo_macro_derivative_variance (hAP : APrioriConclusion)
    (P : Parameters) (p : Profile) (d : TestData) (α α' ε : ℝ) (hε : 0 < ε)
    (hη : 0 < d.1) (hB : 0 ≤ d.2.1) (hC₀ : 0 ≤ d.2.2.1)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hαα' : α ≤ α')
    (hα'0 : P.val.2 - 1 < α') (hα'1 : α' < P.val.2 / 2)
    (hprim : PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ d.2.2.2.1 d.2.2.2.2 α d.2.2.1)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (a : Scale), a.val = 1 →
      1 ≤ (N : ℝ) * a.val → ∀ ψ : Circle (loopMasterLength a) → ℝ,
        ∀ hψ : ContDiff ℝ ∞ (fun x : ℝ => ψ (x : Circle (loopMasterLength a))),
          (∀ k : ℤ, coeff (loopMasterLength a)
            ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _
              (loopMasterLengthTest _ ψ hψ).property⟩ k =
            transportCoeffs P (loopMasterLength a)
              (loopMasterLengthTest _ (cltReg hρ P N a
                ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩)
                (cltReg_contDiff hρ P N a _)) k) →
          ∃ hi : Integrable (fun X : Configuration N =>
            fluctIntegral (fun u => deriv (loopMasterProfile a ψ hψ).val
              (u / a.val)) N X.val) (gibbsMeasure P N),
            variance (gibbsMeasure P N) _ hi ≤ ENNReal.ofReal
              (C * (((N : ℝ) * a.val) ^ ε * ((N : ℝ) * a.val +
                ((N : ℝ) * a.val) ^ (2 * (1 - P.val.2 + α'))))) := by
  let b := 1 - P.val.2 + α'
  have hb : 0 ≤ b := by dsimp [b]; linarith
  obtain ⟨C₁, hC₁, ψ₁, hc₁, hm₁, hf₁, hb₁⟩ := regUniform_firstTransport_macroscopic
    P p d.1 d.2.1 d.2.2.2.1 d.2.2.2.2 α α' d.2.2.1 hη hB hC₀
    hα0 hα1 hαα' hα'0 hα'1 hprim hreg ρ hρ
  obtain ⟨C₂, hC₂, ψ₂, hc₂, hm₂, hf₂, hb₂⟩ := regUniform_secondTransport_macroscopic
    P p d.1 d.2.1 d.2.2.2.1 d.2.2.2.2 α α' d.2.2.1 hη hB hC₀
    hα0 hα1 hαα' hα'0 hα'1 hprim hreg ρ hρ
  have he₂ : ψ₂ = ψ₁ := continuous_eq_of_coeff_eq hc₂ hc₁ hm₂ hm₁
    (fun k => (hf₂ k).trans (hf₁ k).symm)
  let A := C₁ + C₂
  have hA : 0 < A := by dsimp [A]; positivity
  have h₁ : C₁ ≤ A := by dsimp [A]; linarith
  have h₂ : C₂ ≤ A := by dsimp [A]; linarith
  obtain ⟨δmark, hδmark, hsepmark⟩ := exists_pos_le_dist_of_injective hreg.1
  obtain ⟨V, hV, hvariance⟩ := errorTwo_variance_of_envelopes hAP P (d.2.2.2.1 : ℕ)
    d.2.2.2.2 δmark hδmark b ε hb hε
  refine ⟨V * A ^ 2, by positivity, fun N a ha hK ψ hψ htr => ?_⟩
  let Ψ := loopMasterProfile a ψ hψ
  have hΨ : ContDiff ℝ ∞ Ψ.val := hψ
  have hΨp : Function.Periodic Ψ.val a.val⁻¹ := Ψ.property.1
  have hh := cltDelta_pos P N a
  have hh1 := cltDelta_le_one P N a hK
  have hL : (loopMasterLength a).val = 1 := by change a.val⁻¹ = 1; rw [ha, inv_one]
  have hL' : (observationLength a).val = 1 := hL
  have hsepc (i k : Fin (d.2.2.2.1 : ℕ)) (hik : i ≠ k) :
      δmark ≤ circDist a.val⁻¹ (d.2.2.2.2 i - d.2.2.2.2 k) := by
    have ht := hsepmark i k hik
    rw [dist_coe_eq_circDist_sub unitLength.property, show unitLength.val = 1 from rfl] at ht
    simpa only [ha, inv_one] using ht
  obtain ⟨ψ0, hψ0pt, _, hψ0coef⟩ := exists_transfer_of_val_one
    (loopMasterLength a) hL ⟨ψ₁, hm₁⟩
  have hf0 (k : ℤ) : coeff (loopMasterLength a)
      ⟨(fun z => (ψ0.val z : ℂ)), complexL2Integrable _ _ ψ0.property⟩ k =
      transportCoeffs P (loopMasterLength a)
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k :=
    (hψ0coef k).trans ((hf₁ k).trans
      (transportCoeffs_periodizedProfile_eq_unit P p (observationLength a) hL'
        (periodizedProfileL2 p a) k).symm)
  have he : Ψ.val = circleMollify ρ 1 (cltDelta P N a)
      (fun t : ℝ => ψ₁ (t : Circle unitLength)) := by
    funext x
    exact (loopMasterProfile_eq_circleMollify hρ P N a p ψ hψ htr ψ0.val
      ψ0.property hf0 x).trans (circleMollify_eq_of_val_one ρ (loopMasterLength a) hL
        (cltDelta P N a) ψ0.val ψ₁ hψ0pt x)
  have hdist (x m : ℝ) : dist (x : Circle unitLength) (m : Circle unitLength) =
      circDist 1 (x - m) := by
    change dist (x : AddCircle (1 : ℝ)) (m : AddCircle (1 : ℝ)) = _
    exact dist_coe_eq_circDist_sub (by norm_num) x m
  have hval (x : ℝ) : |deriv Ψ.val x| ≤ A * (1 + ∑ j,
      max (circDist a.val⁻¹ (x - d.2.2.2.2 j)) (cltDelta P N a) ^ (-b)) := by
    have hh' := hb₁ (cltDelta P N a) hh hh1 x
    rw [← he] at hh'
    simp only [hdist,
      show -1 + P.val.2 - α' = -b by dsimp [b]; ring] at hh'
    conv_rhs => rw [ha, inv_one]
    exact hh'.trans (mul_le_mul_of_nonneg_right h₁ (by positivity))
  have hder (x : ℝ) : |deriv (deriv Ψ.val) x| ≤ A * (1 + ∑ j,
      max (circDist a.val⁻¹ (x - d.2.2.2.2 j)) (cltDelta P N a) ^ (-1 - b)) := by
    have hh' := hb₂ (cltDelta P N a) hh hh1 x
    rw [he₂, ← he] at hh'
    simp only [hdist,
      show -2 + P.val.2 - α' = -1 - b by dsimp [b]; ring] at hh'
    conv_rhs => rw [ha, inv_one]
    exact hh'.trans (mul_le_mul_of_nonneg_right h₂ (by positivity))
  have htail (x : ℝ) (hx : 2 ≤ circDist a.val⁻¹ x) :
      |deriv Ψ.val x| ≤ A * circDist a.val⁻¹ x ^ (P.val.2 - 2) ∧
        |deriv (deriv Ψ.val) x| ≤ A * circDist a.val⁻¹ x ^ (P.val.2 - 3) := by
    have hh' := abs_cutRep_le_half (inv_pos.mpr a.property.1) x
    change circDist a.val⁻¹ x ≤ a.val⁻¹ / 2 at hh'
    rw [ha, inv_one] at hh' hx
    linarith
  obtain ⟨hi, hbnd⟩ := hvariance N a hK hsepc (cltDelta P N a) A hh
    (cltDelta_ge_inv P N a hK) hA.le (deriv Ψ.val)
    (contDiff_infty_iff_deriv.mp hΨ).2 (Riesz1.periodic_deriv hΨp) hval hder htail
  refine ⟨hi, hbnd.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  exact errorTwo_cutoff_rate hK P.property.2.2.le (mul_nonneg hV.le (sq_nonneg A))

end Riesz1.Internal
