/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformFamilyTransportBounds
public import Riesz1.Variance.RegUniformTransport
public import Riesz1.Variance.VarAlFinalMacroInput
import all Riesz1.Variance.AuxiliaryMixed

/-!
# Macroscopic transport bounds for the actual auxiliary families

The uniform part of Lemma 5.1, as used by Proposition 5.6 and Theorem 2.
Fourier uniqueness identifies
all representatives on the existing `OptimalScalingTest` carrier.
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Riesz1.Internal

/-- Identify the microscopic transport with its mollification, for
an arbitrary observation-circle test. -/
theorem auxiliary_family_transport_eq (P : Parameters) (N : ℕ+) (a : Scale)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (f q : {f : Circle (loopMasterLength a) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength a))})
    (hq : ∀ k, coeff (loopMasterLength a) ⟨(fun x => (q.val x : ℂ)),
      complexL2Integrable _ _ q.property⟩ k = transportCoeffs P (loopMasterLength a) f k)
    (ψ : Circle (loopMasterLength a) → ℝ)
    (hψ : ContDiff ℝ ∞ (fun x : ℝ => ψ (x : Circle (loopMasterLength a))))
    (htr : ∀ k, coeff (loopMasterLength a) ⟨(fun x => (ψ x : ℂ)),
      complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
        transportCoeffs P (loopMasterLength a) (mixedReg hρ N a f) k) :
    (fun x : ℝ => ψ (x : Circle (loopMasterLength a))) =
      circleMollify ρ (loopMasterLength a).val (cltK N a)⁻¹
        (fun t : ℝ => q.val (t : Circle (loopMasterLength a))) := by
  funext x
  exact errorOne_eq_circleMollify_of_coeff P _ hρ (inv_pos.mpr (cltK_pos N a))
    f q.val q.property hq (mixedReg hρ N a f)
    (fun y => cltRegCircle_coe hρ _ (inv_pos.mpr (cltK_pos N a)) f y)
    (loopMasterLengthTest _ ψ hψ) (continuous_circle_of_lift _ hψ.continuous) htr x

/-- All three bounds for every actual family transport at a macroscopic
scale, with one coefficient before the sequence and both smoothing radii.
The exponent can be increased by any permitted amount at the endpoint. -/
theorem auxiliary_family_macro_transport_bounds
    (P : Parameters) (p : Profile) (α α' : ℝ) (d : TestData)
    (hα : P.val.2 - 1 ≤ α) (hα2 : α < P.val.2 / 2)
    (hαα' : α ≤ α') (hα' : P.val.2 - 1 < α') (hα'2 : α' < P.val.2 / 2)
    (hη : 0 < d.1) (hB : 0 ≤ d.2.1) (hC₀ : 0 ≤ d.2.2.1)
    (hprim : PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩
      d.2.2.2.1 d.2.2.2.2 α d.2.2.1)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (ell : Scales) (N : ℕ+), (ell N).val = 1 →
      ∀ (r : ℝ) (v : Profile)
        (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        ∀ (ψ : Circle (loopMasterLength (ell N)) → ℝ)
          (hψ : ContDiff ℝ ∞ (fun x : ℝ => ψ (x : Circle (loopMasterLength (ell N))))),
          (∀ k, coeff (loopMasterLength (ell N)) ⟨(fun x => (ψ x : ℂ)),
            complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
              transportCoeffs P (loopMasterLength (ell N)) (mixedReg hρ N (ell N) f) k) →
          let F := fun x : ℝ => ψ (x : Circle (loopMasterLength (ell N)))
          ∀ x : ℝ, |F x| ≤ A ∧
            |deriv F x| ≤ A * (1 + ∑ j,
              max (circDist 1 (x - d.2.2.2.2 j)) (N : ℝ)⁻¹ ^ (-(1 - P.val.2 + α'))) ∧
            |deriv (deriv F) x| ≤ A * (1 + ∑ j,
              max (circDist 1 (x - d.2.2.2.2 j)) (N : ℝ)⁻¹ ^ (-1 - (1 - P.val.2 + α'))) := by
  obtain ⟨C₁, hC₁, ψ₁, hc₁, hm₁, hf₁, hb₁⟩ := regUniform_firstTransport_macroscopic
    P p d.1 d.2.1 d.2.2.2.1 d.2.2.2.2 α α' d.2.2.1 hη hB hC₀ hα hα2
    hαα' hα' hα'2 hprim hreg ρ hρ
  obtain ⟨C₂, hC₂, ψ₂, hc₂, hm₂, hf₂, hb₂⟩ := regUniform_secondTransport_macroscopic
    P p d.1 d.2.1 d.2.2.2.1 d.2.2.2.2 α α' d.2.2.1 hη hB hC₀ hα hα2
    hαα' hα' hα'2 hprim hreg ρ hρ
  obtain ⟨S, hS, hs⟩ := regUniform_transport_sup P d.1 d.2.1 hη hB
  obtain ⟨ψs, hcs, hms, hfs, _, hbs⟩ := hs unitLength ⟨p.val, p.property⟩ hprim
  obtain ⟨T, hT, ψt, hct, hft, hfamily⟩ := regUniform_familyTransport_macroscopic P p
    d.1 d.2.1 d.2.2.2.1 d.2.2.2.2 α α' d.2.2.1 hη hB hC₀
    hα hα2 hαα' hα' hα'2 hprim hreg ρ hρ
  have he₂ : ψ₂ = ψ₁ := continuous_eq_of_coeff_eq hc₂ hc₁ hm₂ hm₁
    (fun k => (hf₂ k).trans (hf₁ k).symm)
  have hes : ψs = ψ₁ := continuous_eq_of_coeff_eq hcs hc₁ hms hm₁
    (fun k => (hfs k).trans (hf₁ k).symm)
  have het : ψt.val = ψ₁ := continuous_eq_of_coeff_eq hct hc₁ ψt.property hm₁
    (fun k => (hft k).trans (hf₁ k).symm)
  let A := C₁ + C₂ + S + T
  have hA : 0 < A := by dsimp [A]; positivity
  have h₁ : C₁ ≤ A := by dsimp [A]; linarith
  have h₂ : C₂ ≤ A := by dsimp [A]; linarith
  have hSA : S ≤ A := by dsimp [A]; linarith
  have hTA : T ≤ A := by dsimp [A]; linarith
  refine ⟨A, hA, fun ell N ha r v f hv ψ hψ htr => ?_⟩
  dsimp only
  let a := ell N
  let L := loopMasterLength a
  let ξ := (⟨periodizedProfile p L, periodizedProfileL2 p a⟩ :
    {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
  have hL : L.val = 1 := by change (ell N).val⁻¹ = 1; rw [ha, inv_one]
  have hK : cltK N a = (N : ℝ) := by change (N : ℝ) * (ell N).val = _; rw [ha, mul_one]
  have hN : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ (N : ℕ) from N.pos)
  have hh : 0 < (N : ℝ)⁻¹ := inv_pos.mpr (by linarith)
  have hh1 : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN
  have hξ (k : ℤ) : transportCoeffs P L ξ k =
      transportCoeffs P unitLength ⟨p.val, p.property⟩ k :=
    transportCoeffs_periodizedProfile_eq_unit P p L hL ξ.property k
  have heq (q : {g : Circle unitLength → ℝ //
      MemLp (fun x => (g x : ℂ)) 2 (arclength unitLength)})
      (hf : ∀ k, coeff unitLength ⟨(fun x => (q.val x : ℂ)),
        complexL2Integrable _ _ q.property⟩ k = transportCoeffs P L f k) :
      (fun x : ℝ => ψ (x : Circle L)) =
        circleMollify ρ 1 (N : ℝ)⁻¹ (fun t : ℝ => q.val (t : Circle unitLength)) := by
    obtain ⟨q', hq'v, _, hq'f⟩ := exists_transfer_of_val_one L hL q
    have hq' := fun k => (hq'f k).trans (hf k)
    have hi := auxiliary_family_transport_eq P N a hρ f q' hq' ψ hψ htr
    rw [hK] at hi
    exact hi.trans (funext fun x => circleMollify_eq_of_val_one ρ L hL
      (N : ℝ)⁻¹ q'.val q.val hq'v x)
  have hdist (x m : ℝ) : dist (x : Circle unitLength) (m : Circle unitLength) =
      circDist 1 (x - m) := dist_coe_eq_circDist_sub unitLength.property x m
  rcases hv with ⟨_, rfl⟩ | ⟨t, ht, ht1, _, hcases⟩
  · have he := heq ⟨ψ₁, hm₁⟩ (fun k => (hf₁ k).trans (hξ k).symm)
    change ∀ x, |(fun y : ℝ => ψ (y : Circle L)) x| ≤ _ ∧ _
    rw [he]
    intro x
    have h1 := hb₁ (N : ℝ)⁻¹ hh hh1 x
    have h2 := hb₂ (N : ℝ)⁻¹ hh hh1 x
    rw [he₂] at h2
    simp only [hdist,
      show -1 + P.val.2 - α' = -(1 - P.val.2 + α') by ring,
      show -2 + P.val.2 - α' = -1 - (1 - P.val.2 + α') by ring] at h1 h2
    refine ⟨?_, h1.trans (mul_le_mul_of_nonneg_right h₁ (by positivity)),
      h2.trans (mul_le_mul_of_nonneg_right h₂ (by positivity))⟩
    have hs := hbs ρ hρ (N : ℝ)⁻¹ hh x
    rw [hes] at hs
    exact hs.trans hSA
  · obtain ⟨φ, χ, _, _, hfφ, hfχ, hb⟩ := hfamily t ht ht1
    let g := loopMasterLengthTest L (cltRegCircle hρ L ht ξ)
      (cltRegCircle_contDiff hρ L ht ξ)
    have hg (k : ℤ) : transportCoeffs P L g k =
        transportCoeffs P unitLength ⟨p.val, p.property⟩ k *
          (mollifierFT ρ (t * k) : ℂ) := by
      have he := errorOne_transportCoeffs_smooth P L hρ ht ξ g
        (fun x => cltRegCircle_coe hρ L ht ξ x) k
      simpa only [hξ, hL, div_one] using he
    have hcase (q : {g : Circle unitLength → ℝ //
        MemLp (fun x => (g x : ℂ)) 2 (arclength unitLength)})
        (hq : q = φ ∨ q = χ)
        (hf : ∀ k, coeff unitLength ⟨(fun x => (q.val x : ℂ)),
          complexL2Integrable _ _ q.property⟩ k = transportCoeffs P L f k) :
        ∀ x : ℝ, |ψ (x : Circle L)| ≤ A ∧
          |deriv (fun y : ℝ => ψ (y : Circle L)) x| ≤ A * (1 + ∑ j,
            max (circDist 1 (x - d.2.2.2.2 j)) (N : ℝ)⁻¹ ^ (-(1 - P.val.2 + α'))) ∧
          |deriv (deriv (fun y : ℝ => ψ (y : Circle L))) x| ≤ A * (1 + ∑ j,
            max (circDist 1 (x - d.2.2.2.2 j)) (N : ℝ)⁻¹ ^ (-1 - (1 - P.val.2 + α'))) := by
      have he := heq q hf
      change ∀ x, |(fun y : ℝ => ψ (y : Circle L)) x| ≤ _ ∧ _
      rw [he]
      intro x
      have hh' := (hb q hq).2.2 (N : ℝ)⁻¹ hh hh1 x
      simp only [hdist,
        show -1 + P.val.2 - α' = -(1 - P.val.2 + α') by ring,
        show -2 + P.val.2 - α' = -1 - (1 - P.val.2 + α') by ring] at hh'
      exact ⟨hh'.1.trans hTA,
        hh'.2.1.trans (mul_le_mul_of_nonneg_right hTA (by positivity)),
        hh'.2.2.trans (mul_le_mul_of_nonneg_right hTA (by positivity))⟩
    rcases hcases with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · apply hcase φ (Or.inl rfl)
      intro k
      have hfφ' := hfφ k
      simp only [hft, show unitLength.val = 1 from rfl, div_one] at hfφ'
      exact hfφ'.trans (hg k).symm
    · apply hcase χ (Or.inr rfl)
      intro k
      simp only [hfχ, hfφ, hft, show unitLength.val = 1 from rfl, div_one]
      change transportCoeffs P unitLength ⟨p.val, p.property⟩ k -
        transportCoeffs P unitLength ⟨p.val, p.property⟩ k * (mollifierFT ρ (t * k) : ℂ) =
          transportCoeffs P L (subCircleL2 ξ g) k
      rw [varAlFinal_transport_sub, hξ k, hg k]

end Riesz1.Internal

end
