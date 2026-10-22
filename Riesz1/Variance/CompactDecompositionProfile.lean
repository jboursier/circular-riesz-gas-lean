/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlPiecesFixedCutoffs
public import Riesz1.Variance.RegUniformTails
public import Riesz1.ToMathlib.CircleMollifyAE

/-!
# Compact decomposition for the original fixed profile

Proposition 5.9, with the coefficient chosen before the scale
sequence. The original exponent may be the endpoint.
The analytic envelope uses any permitted increased interior exponent.
-/

public section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace Riesz1.Internal

/-- Decompose the actual mollified transport of the original compact
profile, uniformly before every shrinking scale sequence. Every L²
representative with the prescribed Fourier coefficients is allowed. -/
theorem compactDecomposition_profile (P : Parameters) (p : Profile) (hp : CompactProfile p)
    (η B C₀ : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα : P.val.2 - 1 ≤ α) (hα2 : α < P.val.2 / 2) (hαα' : α ≤ α')
    (hα' : P.val.2 - 1 < α') (hα'2 : α' < P.val.2 / 2)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ c : Scale, ∀ i k, i ≠ k →
      δ ≤ circDist c.val⁻¹ (marks i - marks k))
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            n marks α C₀) →
      ∀ (N : ℕ+) (h : ℝ), 1 ≤ (N : ℝ) * (ell N).val →
        ((N : ℝ) * (ell N).val)⁻¹ ≤ h → h ≤ 1 →
        ∀ ψ : {g : Circle (observationLength (ell N)) → ℝ //
          MemLp (fun x => (g x : ℂ)) 2 (arclength (observationLength (ell N)))},
          (∀ k, coeff (observationLength (ell N)) ⟨(fun x => (ψ.val x : ℂ)),
            complexL2Integrable _ _ ψ.property⟩ k = transportCoeffs P (observationLength (ell N))
              ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ k) →
          ∃ φ : Fin ((n : ℕ) + 1) → ℝ → ℝ,
            (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) (ell N).val⁻¹) ∧
            (∀ x, circleMollify ρ (ell N).val⁻¹ h
              (fun t : ℝ => ψ.val (t : Circle (observationLength (ell N)))) x = ∑ j, φ j x) ∧
            (∀ j x,
              |deriv (φ j) x| ≤ C * gradWeightOne P.val.2 (1 - P.val.2 + α')
                ((N : ℝ) * (ell N).val) (ell N).val⁻¹ (x - Fin.lastCases 0 marks j) ∧
              |deriv (deriv (φ j)) x| ≤ C * gradWeightTwo P.val.2 (1 - P.val.2 + α')
                ((N : ℝ) * (ell N).val) (ell N).val⁻¹ (x - Fin.lastCases 0 marks j)) := by
  obtain ⟨C₁, hC₁, hT1⟩ := regUniform_firstTransport_compact P p hp η B n marks α α' C₀
    hη hB hC₀ hα hα2 hαα' hα' hα'2 ρ hρ
  obtain ⟨C₂, hC₂, hT2⟩ := regUniform_secondTransport_compact P p hp η B n marks α α' C₀
    hη hB hC₀ hα hα2 hαα' hα' hα'2 ρ hρ
  obtain ⟨Ct, hCt, hTails⟩ := regUniform_transportTails_compact P p hp η B n marks α α' C₀
    hη hB hC₀ hα hα2 hαα' hα' hα'2 ρ hρ
  let A := C₁ + C₂ + Ct
  have hA : 0 < A := by dsimp [A]; positivity
  have h₁ : C₁ ≤ A := by dsimp [A]; linarith
  have h₂ : C₂ ≤ A := by dsimp [A]; linarith
  have htA : Ct ≤ A := by dsimp [A]; linarith
  obtain ⟨S, hS, hsup⟩ := regUniform_transport_sup P η B hη hB
  obtain ⟨E, hE, hsplit⟩ := varAlPieces_fixed_uniform (n : ℕ) marks
    P.property.2.2 (by linarith : 0 < 1 - P.val.2 + α') hS.le hA.le hδ
  refine ⟨E, hE, fun ell hell hreg N h hK hh hh1 ψ hf => ?_⟩
  let a := ell N
  let L := observationLength a
  have hh0 : 0 < h := lt_of_lt_of_le (inv_pos.mpr (mul_pos (by positivity) a.property.1)) hh
  obtain ⟨ψ₁, hc₁, hm₁, hf₁, hb₁⟩ := hT1 ell hell hreg a (hreg N).1 (hreg N).2
  obtain ⟨ψ₂, hc₂, hm₂, hf₂, hb₂⟩ := hT2 ell hell hreg a (hreg N).1 (hreg N).2
  obtain ⟨ψt, hct, hmt, hft, hbt⟩ := hTails ell hell hreg a (hreg N).1 (hreg N).2
  have he₂ : ψ₂ = ψ₁ := continuous_eq_of_coeff_eq hc₂ hc₁ hm₂ hm₁
    (fun k => (hf₂ k).trans (hf₁ k).symm)
  have het : ψt = ψ₁ := continuous_eq_of_coeff_eq hct hc₁ hmt hm₁
    (fun k => (hft k).trans (hf₁ k).symm)
  let F := circleMollify ρ L.val h (fun t : ℝ => ψ₁ (t : Circle L))
  have hp : Function.Periodic (fun t : ℝ => ψ₁ (t : Circle L)) L.val := by
    intro t; simp only [AddCircle.coe_add_period]
  have hi : LocallyIntegrable (fun t : ℝ => ψ₁ (t : Circle L)) volume :=
    (hc₁.comp (AddCircle.continuous_mk' L.val)).locallyIntegrable
  have hF : ContDiff ℝ ∞ F := contDiff_circleMollify hρ L.property hh0 hi hp
  have hFp : Function.Periodic F L.val := circleMollify_periodic hρ L.property hh0 hi hp
  have h1 (x : ℝ) : |deriv F x| ≤ A * (1 + ∑ j,
      max (circDist L.val (x - marks j)) h ^ (-(1 - P.val.2 + α'))) := by
    have hb := hb₁ h hh0 hh1 x
    simp only [dist_coe_eq_circDist_sub L.property,
      show -1 + P.val.2 - α' = -(1 - P.val.2 + α') by ring] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right h₁ (by positivity))
  have h2 (x : ℝ) : |deriv (deriv F) x| ≤ A * (1 + ∑ j,
      max (circDist L.val (x - marks j)) h ^ (-1 - (1 - P.val.2 + α'))) := by
    have hb := hb₂ h hh0 hh1 x
    rw [he₂] at hb
    simp only [dist_coe_eq_circDist_sub L.property,
      show -2 + P.val.2 - α' = -1 - (1 - P.val.2 + α') by ring] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right h₂ (by positivity))
  have ht (x : ℝ) (hx : 2 ≤ circDist L.val x) :
      |deriv F x| ≤ A * circDist L.val x ^ (P.val.2 - 2) ∧
        |deriv (deriv F) x| ≤ A * circDist L.val x ^ (P.val.2 - 3) := by
    have hcentral (y : ℝ) (hy : 2 ≤ |y|) (hyL : |y| ≤ L.val / 2) := hbt h hh0 hh1 y hy hyL
    simp only [het] at hcentral
    have hb := tail_of_central L.property hFp hcentral x hx
    exact ⟨hb.1.trans (mul_le_mul_of_nonneg_right htA (by positivity)),
      hb.2.trans (mul_le_mul_of_nonneg_right htA (by positivity))⟩
  obtain ⟨ψs, hsc, hsm, hsf, _, hsbound⟩ := hsup L
    ⟨periodizedProfile p L, periodizedProfileL2 p a⟩ (hreg N).1
  have hes : ψs = ψ₁ := continuous_eq_of_coeff_eq hsc hc₁ hsm hm₁
    (fun k => (hsf k).trans (hf₁ k).symm)
  have hFS (x : ℝ) : |F x| ≤ S := by
    have ht := hsbound ρ hρ h hh0 x
    rw [hes] at ht
    exact ht
  obtain ⟨φ, hφ, hsum, henv⟩ := hsplit L.val ((N : ℝ) * a.val) h
    ((one_le_inv₀ a.property.1).mpr a.property.2) (hsep a) hK hh F hF hFp hFS h1 h2
    (fun x hx => ht x (by linarith))
  have hae : ψ.val =ᵐ[arclength L] ψ₁ := ae_eq_of_coeff_eq_real ψ.property hm₁
    (fun k => (hf k).trans (hf₁ k).symm)
  have heq : circleMollify ρ L.val h (fun t : ℝ => ψ.val (t : Circle L)) = F :=
    circleMollify_congr_circle ρ L h hae
  exact ⟨φ, hφ, fun x => (congrFun heq x).trans (hsum x), henv⟩

end Riesz1.Internal
