/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryMixedCovariance
public import Riesz1.Variance.AuxiliaryMixedEnergy
public import Riesz1.Variance.AuxiliaryMixedSobolev
public import Riesz1.Variance.AuxiliaryMixedApprox
public import Riesz1.Variance.AuxiliaryMixedFrobenius
public import Riesz1.ToMathlib.VarianceSplit
public import Riesz1.Variance.AuxiliaryMixedExpansion
public import Riesz1.Variance.LoopIBPMoments
public import Riesz1.CLT.IdentityDefs
public import Riesz1.CLT.IdentityMaster
public import Riesz1.ToMathlib.CirclePullback
public import Riesz1.Variance.LoopMasterScaling
public import Riesz1.Variance.LoopMasterTransport
public import Riesz1.Variance.LoopMaster
public import Riesz1.Variance.LoopIBPProposition

/-!
# The mixed mean-field variance

This is part of the proof of Proposition 5.6. For an `L²` profile `ξ` on the circle of length `ℓ⁻¹`,
the statistic `F = Fluct_N[ξ(ℓ⁻¹·)]`, the regularization `ξ_h = ξ ⋆ ρ_h` at `h = K⁻¹` with
`K = Nℓ`, its smooth mean-zero transport `ψ_h`, and `T = 𝓛Φ_{ψ_h}` (the loop operator potential at
`a = K^{s-1}`), the following identities hold:

* `F, T ∈ L²(μ)` and `Var F = 2 Cov(F,T) - Var T + Var(F - T)`.
* `2 Cov(F,T) - Var T = K^s σ_ℓ²(ξ) - K^s σ_ℓ²(ξ - ξ_h) - βK^{2s-2} E dB_ℓ[ψ_h] - K^{2s-1}‖ψ_h'‖²`.

The variance `σ_ℓ²` of a general `L²` function on `ℓ⁻¹𝕋` is encoded as `scaledVariance`,
which is `cltVariance` at the pullback to the unit circle. The only admissibility input used is
finiteness of `σ_ℓ²(ξ)`, which the statement assumes. The statement is generalized to every
profile for which the quantities used are finite.

The main result is `Riesz1.mixed_mean_field_variance`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology ComplexConjugate Real
open scoped ContDiff ENNReal

namespace Riesz1

/-- The regularization `ξ_h = ξ ⋆ ρ_h` of the profile on the circle of length `ℓ⁻¹` at the scale
`h = K⁻¹`, `K = Nℓ`. -/
def mixedRegCircle {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))}) :
    Circle (loopMasterLength ℓ) → ℝ :=
  cltRegCircle hρ (loopMasterLength ℓ) (inv_pos.mpr (cltK_pos N ℓ)) ξ

/-- The regularization is smooth on the line. -/
lemma mixedRegCircle_contDiff {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))}) :
    ContDiff ℝ ∞ (fun u : ℝ => mixedRegCircle hρ N ℓ ξ (u : Circle (loopMasterLength ℓ))) :=
  cltRegCircle_contDiff hρ (loopMasterLength ℓ) (inv_pos.mpr (cltK_pos N ℓ)) ξ

/-- The variance parameter `σ_ℓ²` of an `L²` profile on the circle of length `ℓ⁻¹`:
`cltVariance` at its pullback to the unit circle. -/
noncomputable def scaledVariance (P : Parameters) (ℓ : Ioc (0 : ℝ) 1)
    (f : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))}) : ℝ≥0∞ :=
  cltVariance P ℓ ⟨fun x => (loopMasterPullback (loopMasterLength ℓ) f.val x : ℂ),
    loopMasterPullback_memLp (loopMasterLength ℓ) f⟩

/-- The rescaled unit transport `φ = L^{-s} ψ_c` with `L = ℓ⁻¹` (`loopMasterTransportPullback`). -/
lemma loopMasterTransportPullback_smooth (P : Parameters) (ℓ : Ioc (0 : ℝ) 1)
    (ψh : Circle (loopMasterLength ℓ) → ℝ)
    (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength ℓ)))) :
    IsSmoothCircle (loopMasterTransportPullback P (loopMasterLength ℓ) ψh) := by
  unfold IsSmoothCircle loopMasterTransportPullback
  exact contDiff_const.mul (loopMasterPullback_smooth _ ψh hψh)

/-- The pulled-back transport is the rescaled unit transport: `ψ_c = L^s φ`. -/
lemma loopMasterPullback_eq_rpow_mul_transport (P : Parameters) (ℓ : Ioc (0 : ℝ) 1)
    (ψh : Circle (loopMasterLength ℓ) → ℝ) (z : UnitAddCircle) :
    loopMasterPullback (loopMasterLength ℓ) ψh z =
      (loopMasterLength ℓ).val ^ P.val.2 *
        loopMasterTransportPullback P (loopMasterLength ℓ) ψh z := by
  unfold loopMasterTransportPullback
  rw [← mul_assoc, ← Real.rpow_add (loopMasterLength ℓ).property, add_neg_cancel,
    Real.rpow_zero, one_mul]

/-- The derivative of the pulled-back transport is the rescaled derivative of the unit transport. -/
lemma loopMasterCircleDeriv_pullback_eq (P : Parameters) (ℓ : Ioc (0 : ℝ) 1)
    (ψh : Circle (loopMasterLength ℓ) → ℝ)
    (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength ℓ)))) (z : UnitAddCircle) :
    loopMasterCircleDeriv (loopMasterPullback (loopMasterLength ℓ) ψh)
        (loopMasterPullback_smooth _ ψh hψh) z =
      (loopMasterLength ℓ).val ^ P.val.2 *
        loopMasterCircleDeriv (loopMasterTransportPullback P (loopMasterLength ℓ) ψh)
          (loopMasterTransportPullback_smooth P ℓ ψh hψh) z := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [loopMasterCircleDeriv_coe, loopMasterCircleDeriv_coe]
  have hfun : (fun u : ℝ => loopMasterPullback (loopMasterLength ℓ) ψh (u : UnitAddCircle)) =
      fun u : ℝ => (loopMasterLength ℓ).val ^ P.val.2 *
        loopMasterTransportPullback P (loopMasterLength ℓ) ψh (u : UnitAddCircle) := by
    funext u
    exact loopMasterPullback_eq_rpow_mul_transport P ℓ ψh (u : UnitAddCircle)
  rw [hfun, deriv_const_mul]
  exact ((loopMasterTransportPullback_smooth P ℓ ψh hψh).differentiable (by simp)).differentiableAt

/-- The unit-circle profile `η_h = ξ_h(ℓ⁻¹ ·)` of the regularization. -/
noncomputable def mixedEta {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))}) : UnitAddCircle → ℝ :=
  loopMasterPullback (loopMasterLength ℓ) (mixedRegCircle hρ N ℓ ξ)

/-- The unit-circle profile `η_h` is smooth. -/
lemma mixedEta_smooth {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))}) :
    IsSmoothCircle (mixedEta hρ N ℓ ξ) :=
  loopMasterPullback_smooth _ _ (mixedRegCircle_contDiff hρ N ℓ ξ)

/-- The transport coefficients of the rescaled unit transport `φ = L^{-s} ψ_c`, against `η_h`. -/
lemma loopMasterTransportPullback_coeff {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1)
    (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))})
    (ψh : Circle (loopMasterLength ℓ) → ℝ)
    (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength ℓ))))
    (htr : ∀ k : ℤ, coeff (loopMasterLength ℓ)
      ⟨(fun z => (ψh z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψh hψh).property⟩ k =
      transportCoeffs P (loopMasterLength ℓ)
        (loopMasterLengthTest _ (mixedRegCircle hρ N ℓ ξ) (mixedRegCircle_contDiff hρ N ℓ ξ)) k)
    (k : ℤ) :
    circleCoeff (loopMasterTransportPullback P (loopMasterLength ℓ) ψh) k =
      transportCoeffs P unitLength (loopMasterTest (mixedEta hρ N ℓ ξ) (mixedEta_smooth hρ N ℓ ξ))
        k :=
  loopMaster_transport_pullback P (loopMasterLength ℓ) (mixedRegCircle hρ N ℓ ξ) ψh
    (mixedRegCircle_contDiff hρ N ℓ ξ) hψh htr k

/-- **The energy link.** The Hessian background of the loop
profile `f = ℓ ψ_h(·/ℓ)` satisfies `β ∫₀¹ G_f = κ² · (2π)^{1-s}/(2βR) · H(η_h)`, with `κ = ℓ L^s`
and `H` the Sobolev seminorm of `circleSobolevSq`. -/
theorem beta_integral_hessBackground_eq {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (P : Parameters)
    (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))})
    (ψh : Circle (loopMasterLength ℓ) → ℝ)
    (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength ℓ))))
    (htr : ∀ k : ℤ, coeff (loopMasterLength ℓ)
      ⟨(fun z => (ψh z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψh hψh).property⟩ k =
      transportCoeffs P (loopMasterLength ℓ)
        (loopMasterLengthTest _ (mixedRegCircle hρ N ℓ ξ) (mixedRegCircle_contDiff hρ N ℓ ξ)) k) :
    P.val.1 * (∫ a in (0 : ℝ)..1, hessBackground (parametersExponent P).val
        (loopScaleField ℓ.val (loopMasterProfile ℓ ψh hψh).val) a) =
      (ℓ.val * (loopMasterLength ℓ).val ^ P.val.2) ^ 2 *
        ((2 * π) ^ (1 - (parametersExponent P).val) /
          (2 * P.val.1 * rieszConstant (parametersExponent P))) *
        (circleSobolevSq ((1 - (parametersExponent P).val) / 2)
          ⟨fun x : UnitAddCircle => (mixedEta hρ N ℓ ξ x : ℂ),
            memLp_unitCircle_of_isSmoothCircle (mixedEta_smooth hρ N ℓ ξ)⟩).toReal := by
  set φ := loopMasterTransportPullback P (loopMasterLength ℓ) ψh with hφdef
  have hφS : IsSmoothCircle φ := loopMasterTransportPullback_smooth P ℓ ψh hψh
  have hφL2 : MemLp (fun x : UnitAddCircle => (φ x : ℂ)) 2 volume := memLp_unitCircle_of_isSmoothCircle hφS
  have htrφ := loopMasterTransportPullback_coeff hρ P N ℓ ξ ψh hψh htr
  obtain ⟨hint, _⟩ := energy_package P (mixedEta hρ N ℓ ξ) φ (mixedEta_smooth hρ N ℓ ξ) hφL2 htrφ
  have hen := beta_mul_energy_eq P (mixedEta hρ N ℓ ξ) φ (mixedEta_smooth hρ N ℓ ξ) hφL2 htrφ
  have hf : loopScaleField ℓ.val (loopMasterProfile ℓ ψh hψh).val =
      fun u : ℝ => (ℓ.val * (loopMasterLength ℓ).val ^ P.val.2) * φ (u : UnitAddCircle) := by
    funext u
    unfold loopScaleField
    rw [loopMasterProfile_val_div ℓ ψh hψh u, loopMasterPullback_eq_rpow_mul_transport P ℓ ψh]
    ring
  rw [hf, integral_hessBackground_scaled_eq (parametersExponent P).val
    (ℓ.val * (loopMasterLength ℓ).val ^ P.val.2) (fun u : ℝ => φ (u : UnitAddCircle)) hint]
  linear_combination (ℓ.val * (loopMasterLength ℓ).val ^ P.val.2) ^ 2 * hen

/-- The derivative of a periodic smooth function is periodic with the same period. -/
lemma deriv_periodic_of_periodic {ψ : ℝ → ℝ} {c : ℝ} (_hψ : ContDiff ℝ ∞ ψ)
    (hp : Function.Periodic ψ c) : Function.Periodic (deriv ψ) c := by
  intro x
  have h : (fun y => ψ (y + c)) = ψ := funext fun y => hp y
  have h2 := deriv_comp_add_const (f := ψ) (a := c) (x := x)
  rw [h] at h2
  exact h2.symm

/-- The Gibbs integrability of the frobenius term `Σ_k ψ'(x_k/ℓ)²`, as a linear statistic. -/
lemma integrable_frobeniusSqDiag (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) :
    Integrable (fun X : Configuration N => frobeniusSqDiag ℓ ψ X) (gibbsMeasure P N) := by
  have hd : ContDiff ℝ ∞ (deriv ψ.val) := (contDiff_infty_iff_deriv.mp hψ).2
  have hper1 : Function.Periodic (fun u : ℝ => deriv ψ.val (u / ℓ.val) ^ 2) 1 := by
    intro u
    simp only
    rw [add_div, one_div, deriv_periodic_of_periodic hψ ψ.property.1 (u / ℓ.val)]
  have hcont : Continuous (fun u : ℝ => deriv ψ.val (u / ℓ.val) ^ 2) :=
    ((hd.continuous).comp (continuous_id.div_const _)).pow 2
  have hmem := memLp_lift_of_continuous hcont hper1
  have h := (memLp_linearStatistic P N hmem).integrable one_le_two
  refine h.congr (Filter.Eventually.of_forall fun X => ?_)
  unfold linearStatistic frobeniusSqDiag
  simp only [Function.Periodic.lift_coe]

/-- The variance of the loop operator potential `T = 𝓛Φ_{ψ_h,a}` (`loop_equations_ibp`, clause 3,
with the Hessian expectation and the frobenius expectation): `Var T = a² (β N^{-s} (N² ∫ G_f + E hFE)
+ N ℓ ∫ (ψ')²)`. -/
theorem gibbsCov_loopOperator_self_eq (hPL : External.PrekopaLeindler) (P : Parameters)
    (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψh : Circle (loopMasterLength ℓ) → ℝ)
    (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength ℓ))))
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, (loopMasterProfile ℓ ψh hψh).val t = 0) :
    gibbsCov (gibbsMeasure P N) (loopOperatorPotential P N ℓ a (loopMasterProfile ℓ ψh hψh))
        (loopOperatorPotential P N ℓ a (loopMasterProfile ℓ ψh hψh)) =
      a ^ 2 * (P.val.1 * (N : ℝ) ^ (-(parametersExponent P).val) *
          ((N : ℝ) ^ 2 * (∫ u in (0 : ℝ)..1, hessBackground (parametersExponent P).val
            (loopScaleField ℓ.val (loopMasterProfile ℓ ψh hψh).val) u) +
          ∫ X : Configuration N, hessFluctExpansion (parametersExponent P).val (N : ℕ)
            (loopScaleField ℓ.val (loopMasterProfile ℓ ψh hψh).val) X.val ∂(gibbsMeasure P N)) +
        ((N : ℝ) * ℓ.val) * ∫ v in (0 : ℝ)..ℓ.val⁻¹,
          deriv (loopMasterProfile ℓ ψh hψh).val v ^ 2) := by
  have hloop := loop_equations_ibp P hPL N ℓ a (loopMasterProfile ℓ ψh hψh) hψh hmean
  have hQi : Integrable (fun X : Configuration N =>
      hessianQuadratic P N ℓ (loopMasterProfile ℓ ψh hψh) X) (gibbsMeasure P N) := by
    have h := (loop_moments P hPL N ℓ (loopMasterProfile ℓ ψh hψh)).2 1 one_pos
    have h' : Integrable (fun X : Configuration N =>
        ‖hessianQuadratic P N ℓ (loopMasterProfile ℓ ψh hψh) X‖) (gibbsMeasure P N) := by
      simpa [Real.norm_eq_abs] using h
    exact (integrable_norm_iff (measurable_hessianQuadratic P N ℓ
      (loopMasterProfile ℓ ψh hψh)).aestronglyMeasurable).mp h'
  have hFi := integrable_frobeniusSqDiag P N ℓ (loopMasterProfile ℓ ψh hψh) hψh
  rw [hloop.2.2.1, integral_add hQi hFi, integral_frobeniusSqDiag_profile P N ℓ
    (loopMasterProfile ℓ ψh hψh) hψh, integral_hessianQuadratic_eq P hPL N ℓ
    (loopMasterProfile ℓ ψh hψh)]

/-- The power identity of the energy step: `a² N^{2-s} κ² = K^s ℓ^{-s}` with `a = K^{s-1}`,
`K = Nℓ` and `κ = ℓ (ℓ⁻¹)^s`. -/
lemma rpow_energy_identity {N ℓ s : ℝ} (hN : 0 < N) (hℓ : 0 < ℓ) :
    ((N * ℓ) ^ (s - 1)) ^ 2 * N ^ (2 - s) * (ℓ * (ℓ⁻¹) ^ s) ^ 2 = (N * ℓ) ^ s * ℓ ^ (-s) := by
  have e1 : (N * ℓ) ^ (s - 1) = N ^ s / N * (ℓ ^ s / ℓ) := by
    rw [Real.mul_rpow hN.le hℓ.le, Real.rpow_sub_one hN.ne', Real.rpow_sub_one hℓ.ne']
  have e2 : N ^ (2 - s) = N ^ 2 / N ^ s := by
    rw [Real.rpow_sub hN, Real.rpow_two]
  have e3 : (ℓ⁻¹) ^ s = (ℓ ^ s)⁻¹ := Real.inv_rpow hℓ.le s
  have e4 : ℓ ^ (-s) = (ℓ ^ s)⁻¹ := Real.rpow_neg hℓ.le s
  have e5 : (N * ℓ) ^ s = N ^ s * ℓ ^ s := Real.mul_rpow hN.le hℓ.le
  rw [e1, e2, e3, e4, e5]
  have hx : N ^ s ≠ 0 := (Real.rpow_pos_of_pos hN s).ne'
  have hy : ℓ ^ s ≠ 0 := (Real.rpow_pos_of_pos hℓ s).ne'
  field_simp

/-- The scaled variance is finite exactly when the Sobolev seminorm of the pullback is finite. -/
lemma scaledVariance_ne_top_iff (P : Parameters) (ℓ : Ioc (0 : ℝ) 1)
    (f : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))}) :
    scaledVariance P ℓ f ≠ ⊤ ↔ circleSobolevSq ((1 - P.val.2) / 2)
      ⟨fun x : UnitAddCircle => (loopMasterPullback (loopMasterLength ℓ) f.val x : ℂ),
        loopMasterPullback_memLp (loopMasterLength ℓ) f⟩ ≠ ⊤ := by
  unfold scaledVariance cltVariance
  have hc : ENNReal.ofReal ((2 * π) ^ (1 - P.val.2) /
      (2 * P.val.1 * rieszConstant (parametersExponent P)) * ℓ.val ^ (-P.val.2)) ≠ 0 := by
    refine (ENNReal.ofReal_pos.mpr ?_).ne'
    have h1 : (0 : ℝ) < (2 * π) ^ (1 - P.val.2) := Real.rpow_pos_of_pos (by positivity) _
    have h2 : (0 : ℝ) < 2 * P.val.1 * rieszConstant (parametersExponent P) := by
      have hR : 0 < rieszConstant (parametersExponent P) := by
        unfold rieszConstant
        exact div_pos (mul_pos (mul_pos (by positivity) (Real.sqrt_pos.2 Real.pi_pos))
          (Real.Gamma_pos_of_pos (by linarith [(parametersExponent P).property.2])))
          (Real.Gamma_pos_of_pos (by linarith [(parametersExponent P).property.1]))
      have := P.property.1
      positivity
    have h3 : (0 : ℝ) < ℓ.val ^ (-P.val.2) := Real.rpow_pos_of_pos ℓ.property.1 _
    positivity
  constructor
  · intro h hH
    exact h (by rw [hH, ENNReal.mul_top hc])
  · intro h hfin
    rcases ENNReal.mul_eq_top.mp hfin with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h h2
    · exact absurd h1 ENNReal.ofReal_ne_top

/-- The Sobolev form of the scaled variance: `σ_ℓ²(f) = C ℓ^{-s} H(f)` as real numbers. -/
lemma scaledVariance_toReal_eq (P : Parameters) (ℓ : Ioc (0 : ℝ) 1)
    (f : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))}) :
    (scaledVariance P ℓ f).toReal = ((2 * π) ^ (1 - P.val.2) /
        (2 * P.val.1 * rieszConstant (parametersExponent P)) * ℓ.val ^ (-P.val.2)) *
      (circleSobolevSq ((1 - P.val.2) / 2)
        ⟨fun x : UnitAddCircle => (loopMasterPullback (loopMasterLength ℓ) f.val x : ℂ),
          loopMasterPullback_memLp (loopMasterLength ℓ) f⟩).toReal := by
  have hR : 0 < rieszConstant (parametersExponent P) := loopMaster_rieszConstant_pos P
  have hden : 0 < 2 * P.val.1 * rieszConstant (parametersExponent P) :=
    mul_pos (mul_pos two_pos P.property.1) hR
  have hpos : 0 ≤ (2 * π) ^ (1 - P.val.2) /
      (2 * P.val.1 * rieszConstant (parametersExponent P)) * ℓ.val ^ (-P.val.2) :=
    mul_nonneg (div_nonneg (Real.rpow_nonneg (by positivity) _) hden.le)
      (Real.rpow_nonneg ℓ.property.1.le _)
  unfold scaledVariance cltVariance
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpos]

/-- The constant of the covariance identity: `N a ℓ L^s = K^s ℓ^{-s}` with `a = K^{s-1}`,
`K = Nℓ`, `L = ℓ⁻¹`. -/
lemma cov_constant_identity {N ℓ s : ℝ} (hN : 0 < N) (hℓ : 0 < ℓ) :
    N * (N * ℓ) ^ (s - 1) * ℓ * (ℓ⁻¹) ^ s = (N * ℓ) ^ s * ℓ ^ (-s) := by
  have hK : 0 < N * ℓ := mul_pos hN hℓ
  have e1 : (N * ℓ) ^ (s - 1) * (N * ℓ) = (N * ℓ) ^ s := by
    rw [Real.rpow_sub_one hK.ne']
    field_simp
  have e2 : (ℓ⁻¹) ^ s = ℓ ^ (-s) := by
    rw [Real.inv_rpow hℓ.le, Real.rpow_neg hℓ.le]
  rw [e2]
  rw [← e1]
  ring

/-- The regularization `ξ_h` as an element of the `L²` carrier on the circle of length `ℓ⁻¹`. -/
noncomputable def mixedReg {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))}) :
    {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))} :=
  loopMasterLengthTest (loopMasterLength ℓ) (mixedRegCircle hρ N ℓ ξ)
    (mixedRegCircle_contDiff hρ N ℓ ξ)

/-- The statistic `F = Fluct_N[ξ(ℓ⁻¹·)]` of the profile. -/
noncomputable def mixedStat (_P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))}) :
    Configuration N → ℝ :=
  fun X => fluctuation ⟨loopMasterPullback (loopMasterLength ℓ) ξ.val,
    (memLp_real_of_complex (loopMasterPullback_memLp (loopMasterLength ℓ) ξ)).integrable
      one_le_two⟩ X

/-- The loop operator potential `T = 𝓛Φ_{ψ_h}` at `a = K^{s-1}`. -/
noncomputable def mixedOp (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ψh : Circle (loopMasterLength ℓ) → ℝ)
    (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength ℓ)))) :
    Configuration N → ℝ :=
  loopOperatorPotential P N ℓ (cltK N ℓ ^ (P.val.2 - 1)) (loopMasterProfile ℓ ψh hψh)

/-- **The covariance in variance form.** We have
`Cov(F, T) = (K^s/2) (σ_ℓ²(ξ) + σ_ℓ²(ξ_h) - σ_ℓ²(ξ - ξ_h))`, and the variance of `ξ - ξ_h` is
finite. -/
theorem gibbsCov_mixed_eq (hPL : External.PrekopaLeindler) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))})
    (hσ : scaledVariance P ℓ ξ ≠ ⊤)
    (ψh : Circle (loopMasterLength ℓ) → ℝ)
    (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength ℓ))))
    (htr : ∀ k : ℤ, coeff (loopMasterLength ℓ)
      ⟨(fun z => (ψh z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψh hψh).property⟩ k =
      transportCoeffs P (loopMasterLength ℓ)
        (loopMasterLengthTest _ (mixedRegCircle hρ N ℓ ξ) (mixedRegCircle_contDiff hρ N ℓ ξ)) k) :
    scaledVariance P ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ)) ≠ ⊤ ∧
    gibbsCov (gibbsMeasure P N) (mixedStat P N ℓ ξ) (mixedOp P N ℓ ψh hψh) =
      (cltK N ℓ ^ P.val.2 / 2) * ((scaledVariance P ℓ ξ).toReal +
        (scaledVariance P ℓ (mixedReg hρ N ℓ ξ)).toReal -
        (scaledVariance P ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ))).toReal) := by
  have hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, (loopMasterProfile ℓ ψh hψh).val t = 0 :=
    loopMaster_transport_mean_zero P (loopMasterLength ℓ) (mixedRegCircle hρ N ℓ ξ) ψh
      (mixedRegCircle_contDiff hρ N ℓ ξ) hψh htr
  have hs : P.val.2 < 1 := P.property.2.2
  have hξL2 : MemLp (fun x : UnitAddCircle => (loopMasterPullback (loopMasterLength ℓ) ξ.val x : ℂ))
      2 volume := loopMasterPullback_memLp _ ξ
  have hηS : IsSmoothCircle (mixedEta hρ N ℓ ξ) := mixedEta_smooth hρ N ℓ ξ
  have hφS := loopMasterTransportPullback_smooth P ℓ ψh hψh
  have hφL2 : MemLp (fun x : UnitAddCircle =>
      (loopMasterTransportPullback P (loopMasterLength ℓ) ψh x : ℂ)) 2 volume :=
    memLp_unitCircle_of_isSmoothCircle hφS
  have htrφ := loopMasterTransportPullback_coeff hρ P N ℓ ξ ψh hψh htr
  obtain ⟨_, hfinη⟩ := energy_package P (mixedEta hρ N ℓ ξ)
    (loopMasterTransportPullback P (loopMasterLength ℓ) ψh) hηS hφL2 htrφ
  have hfinf := (scaledVariance_ne_top_iff P ℓ ξ).mp hσ
  have hfinfη := circleSobolevSq_sub_ne_top hs _ _ hξL2 (memLp_unitCircle_of_isSmoothCircle hηS) hfinf hfinη
  refine ⟨(scaledVariance_ne_top_iff P ℓ _).mpr hfinfη, ?_⟩
  have hcov := gibbsCov_pullback_eq hPL P N ℓ (cltK N ℓ ^ (P.val.2 - 1)) hρ ξ ψh hψh hmean
  have hsob := neg_integral_mul_deriv_eq_sobolev P (loopMasterPullback (loopMasterLength ℓ) ξ.val)
    (mixedEta hρ N ℓ ξ) (loopMasterTransportPullback P (loopMasterLength ℓ) ψh) hξL2 hηS hφS
    htrφ hfinf hfinη hfinfη
  have hΨ : (∫ z : UnitAddCircle, loopMasterPullback (loopMasterLength ℓ) ξ.val z *
      loopMasterCircleDeriv (loopMasterPullback (loopMasterLength ℓ) ψh)
        (loopMasterPullback_smooth _ ψh hψh) z) =
      (loopMasterLength ℓ).val ^ P.val.2 * (∫ z : UnitAddCircle,
        loopMasterPullback (loopMasterLength ℓ) ξ.val z *
          loopMasterCircleDeriv (loopMasterTransportPullback P (loopMasterLength ℓ) ψh) hφS z) := by
    rw [← integral_const_mul]
    congr 1
    funext z
    rw [loopMasterCircleDeriv_pullback_eq P ℓ ψh hψh z]
    ring
  have hσf := scaledVariance_toReal_eq P ℓ ξ
  have hση : (scaledVariance P ℓ (mixedReg hρ N ℓ ξ)).toReal = ((2 * π) ^ (1 - P.val.2) /
      (2 * P.val.1 * rieszConstant (parametersExponent P)) * ℓ.val ^ (-P.val.2)) *
      (circleSobolevSq ((1 - P.val.2) / 2)
        ⟨fun x : UnitAddCircle => (mixedEta hρ N ℓ ξ x : ℂ), memLp_unitCircle_of_isSmoothCircle hηS⟩).toReal :=
    scaledVariance_toReal_eq P ℓ (mixedReg hρ N ℓ ξ)
  have hσfη : (scaledVariance P ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ))).toReal =
      ((2 * π) ^ (1 - P.val.2) / (2 * P.val.1 * rieszConstant (parametersExponent P)) *
        ℓ.val ^ (-P.val.2)) *
      (circleSobolevSq ((1 - P.val.2) / 2)
        ⟨fun x : UnitAddCircle => ((fun y => loopMasterPullback (loopMasterLength ℓ) ξ.val y -
          mixedEta hρ N ℓ ξ y) x : ℂ), memLp_sub_complex hξL2 (memLp_unitCircle_of_isSmoothCircle hηS)⟩).toReal :=
    scaledVariance_toReal_eq P ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ))
  beta_reduce at hsob
  have hconst : (N : ℝ) * (cltK N ℓ ^ (P.val.2 - 1)) * ℓ.val *
      (loopMasterLength ℓ).val ^ P.val.2 = cltK N ℓ ^ P.val.2 * ℓ.val ^ (-P.val.2) := by
    unfold cltK
    exact cov_constant_identity (N := (N : ℝ)) (ℓ := ℓ.val) (s := P.val.2) (by exact_mod_cast N.pos)
      ℓ.property.1
  unfold mixedStat mixedOp
  rw [hcov, hΨ, hσf, hση, hσfη]
  linear_combination ((N : ℝ) * (cltK N ℓ ^ (P.val.2 - 1)) * ℓ.val *
      (loopMasterLength ℓ).val ^ P.val.2) * hsob
    + ((((2 * π) ^ (1 - P.val.2) / (2 * P.val.1 * rieszConstant (parametersExponent P)))) *
      (((circleSobolevSq ((1 - P.val.2) / 2) ⟨fun x : UnitAddCircle => (loopMasterPullback (loopMasterLength ℓ) ξ.val x : ℂ), loopMasterPullback_memLp _ ξ⟩).toReal +
        (circleSobolevSq ((1 - P.val.2) / 2) ⟨fun x : UnitAddCircle => (mixedEta hρ N ℓ ξ x : ℂ), memLp_unitCircle_of_isSmoothCircle hηS⟩).toReal -
        (circleSobolevSq ((1 - P.val.2) / 2) ⟨fun x : UnitAddCircle => ((fun y => loopMasterPullback (loopMasterLength ℓ) ξ.val y - mixedEta hρ N ℓ ξ y) x : ℂ), memLp_sub_complex hξL2 (memLp_unitCircle_of_isSmoothCircle hηS)⟩).toReal) / 2)) * hconst

/-- **The variance of the loop operator potential in variance form.** We have
`Var T = K^s σ_ℓ²(ξ_h) + βK^{2s-2} E dB_ℓ[ψ_h] + K^{2s-1} ‖ψ_h'‖²`, where
`dB_ℓ[ψ] = N^{-s} E[hessFluctExpansion]` and `‖ψ_h'‖² = ∫_0^{ℓ⁻¹} (ψ_h')²`. -/
theorem gibbsCov_mixedOp_eq (hPL : External.PrekopaLeindler) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))})
    (ψh : Circle (loopMasterLength ℓ) → ℝ)
    (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength ℓ))))
    (htr : ∀ k : ℤ, coeff (loopMasterLength ℓ)
      ⟨(fun z => (ψh z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψh hψh).property⟩ k =
      transportCoeffs P (loopMasterLength ℓ)
        (loopMasterLengthTest _ (mixedRegCircle hρ N ℓ ξ) (mixedRegCircle_contDiff hρ N ℓ ξ)) k) :
    gibbsCov (gibbsMeasure P N) (mixedOp P N ℓ ψh hψh) (mixedOp P N ℓ ψh hψh) =
      cltK N ℓ ^ P.val.2 * (scaledVariance P ℓ (mixedReg hρ N ℓ ξ)).toReal +
        P.val.1 * cltK N ℓ ^ (2 * P.val.2 - 2) *
          ((N : ℝ) ^ (-P.val.2) * ∫ X : Configuration N,
            hessFluctExpansion P.val.2 (N : ℕ)
              (loopScaleField ℓ.val (loopMasterProfile ℓ ψh hψh).val) X.val ∂(gibbsMeasure P N)) +
        cltK N ℓ ^ (2 * P.val.2 - 1) * ∫ v in (0 : ℝ)..ℓ.val⁻¹,
          deriv (loopMasterProfile ℓ ψh hψh).val v ^ 2 := by
  have hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, (loopMasterProfile ℓ ψh hψh).val t = 0 :=
    loopMaster_transport_mean_zero P (loopMasterLength ℓ) (mixedRegCircle hρ N ℓ ξ) ψh
      (mixedRegCircle_contDiff hρ N ℓ ξ) hψh htr
  have hηS : IsSmoothCircle (mixedEta hρ N ℓ ξ) := mixedEta_smooth hρ N ℓ ξ
  have hb := beta_integral_hessBackground_eq hρ P N ℓ ξ ψh hψh htr
  have hση : (scaledVariance P ℓ (mixedReg hρ N ℓ ξ)).toReal = ((2 * π) ^ (1 - P.val.2) /
      (2 * P.val.1 * rieszConstant (parametersExponent P)) * ℓ.val ^ (-P.val.2)) *
      (circleSobolevSq ((1 - P.val.2) / 2)
        ⟨fun x : UnitAddCircle => (mixedEta hρ N ℓ ξ x : ℂ), memLp_unitCircle_of_isSmoothCircle hηS⟩).toReal :=
    scaledVariance_toReal_eq P ℓ (mixedReg hρ N ℓ ξ)
  unfold mixedOp
  rw [gibbsCov_loopOperator_self_eq hPL P N ℓ (cltK N ℓ ^ (P.val.2 - 1)) ψh hψh hmean]
  rw [show (parametersExponent P).val = P.val.2 from rfl] at hb ⊢
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hℓ : (0 : ℝ) < ℓ.val := ℓ.property.1
  have hK : (0 : ℝ) < cltK N ℓ := cltK_pos N ℓ
  have hKdef : cltK N ℓ = (N : ℝ) * ℓ.val := rfl
  -- The power identities of the energy step.
  have hE4 : (cltK N ℓ ^ (P.val.2 - 1)) ^ 2 = cltK N ℓ ^ (2 * P.val.2 - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK.le]
    congr 1
    push_cast
    ring
  have hE5 : (cltK N ℓ ^ (P.val.2 - 1)) ^ 2 * ((N : ℝ) * ℓ.val) =
      cltK N ℓ ^ (2 * P.val.2 - 1) := by
    rw [← hKdef, hE4, show 2 * P.val.2 - 1 = (2 * P.val.2 - 2) + 1 by ring,
      Real.rpow_add_one hK.ne']
  have hE3 : (cltK N ℓ ^ (P.val.2 - 1)) ^ 2 * (N : ℝ) ^ (2 - P.val.2) *
      (ℓ.val * ((loopMasterLength ℓ).val) ^ P.val.2) ^ 2 = cltK N ℓ ^ P.val.2 * ℓ.val ^ (-P.val.2) := by
    rw [hKdef]
    exact rpow_energy_identity hN hℓ
  have hE3' : (cltK N ℓ ^ (P.val.2 - 1)) ^ 2 * ((N : ℝ) ^ (-P.val.2) * (N : ℝ) ^ 2) *
      (ℓ.val * ((loopMasterLength ℓ).val) ^ P.val.2) ^ 2 =
        cltK N ℓ ^ P.val.2 * ℓ.val ^ (-P.val.2) := by
    rw [← hE3]
    congr 1
    rw [show (2 : ℝ) - P.val.2 = 2 + (-P.val.2) by ring, Real.rpow_add hN, Real.rpow_two]
    ring
  linear_combination ((cltK N ℓ ^ (P.val.2 - 1)) ^ 2 * (N : ℝ) ^ (-P.val.2) * (N : ℝ) ^ 2) * hb
    + ((2 * π) ^ (1 - P.val.2) / (2 * P.val.1 * rieszConstant (parametersExponent P)) *
      (circleSobolevSq ((1 - P.val.2) / 2)
        ⟨fun x : UnitAddCircle => (mixedEta hρ N ℓ ξ x : ℂ), memLp_unitCircle_of_isSmoothCircle hηS⟩).toReal) *
        hE3'
    - cltK N ℓ ^ P.val.2 * hση
    + (P.val.1 * (N : ℝ) ^ (-P.val.2) * ∫ X : Configuration N,
        hessFluctExpansion P.val.2 (N : ℕ)
          (loopScaleField ℓ.val (loopMasterProfile ℓ ψh hψh).val) X.val ∂(gibbsMeasure P N)) * hE4
    + (∫ v in (0 : ℝ)..ℓ.val⁻¹, deriv (loopMasterProfile ℓ ψh hψh).val v ^ 2) * hE5

/-- **Mixed mean-field variance** (part of the proof of Proposition 5.6).
Let `ξ` be an `L²` profile on the circle of length `ℓ⁻¹` with finite circle variance `σ_ℓ²(ξ)`
at scale `ℓ` (the admissibility input), `N ≥ 1` and `0 < ℓ ≤ 1` with `K = Nℓ ≥ 1`.
Let `ψ_h` be the smooth mean-zero transport of the regularization `ξ_h = ξ ⋆ ρ_{K⁻¹}`.
Put `F = Fluct_N[ξ(ℓ⁻¹·)]` and `T = 𝓛Φ_{ψ_h}`. Then:

1. `F, T ∈ L²(μ)`.
2. `Var F = 2 Cov(F,T) - Var T + Var(F - T)`.
3. `Cov(F,T) = (K^s/2) (σ_ℓ²(ξ) + σ_ℓ²(ξ_h) - σ_ℓ²(ξ - ξ_h))`, with `σ_ℓ²(ξ - ξ_h)` finite.
4. `2 Cov(F,T) - Var T = K^s σ_ℓ²(ξ) - K^s σ_ℓ²(ξ - ξ_h) - βK^{2s-2} E dB_ℓ[ψ_h] - K^{2s-1}‖ψ_h'‖²`,

where `dB_ℓ[ψ] = N^{-s} E[hessFluctExpansion]` and `‖ψ_h'‖² = ∫_0^{ℓ⁻¹} (ψ_h')²`. The
Prékopa–Leindler inequality `External.PrekopaLeindler` is an explicit hypothesis. -/
theorem mixed_mean_field_variance (hPL : External.PrekopaLeindler) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (_hK : 1 ≤ cltK N ℓ) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))})
    (hσ : scaledVariance P ℓ ξ ≠ ⊤)
    (ψh : Circle (loopMasterLength ℓ) → ℝ)
    (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength ℓ))))
    (htr : ∀ k : ℤ, coeff (loopMasterLength ℓ)
      ⟨(fun z => (ψh z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψh hψh).property⟩ k =
      transportCoeffs P (loopMasterLength ℓ)
        (loopMasterLengthTest _ (mixedRegCircle hρ N ℓ ξ) (mixedRegCircle_contDiff hρ N ℓ ξ)) k) :
    (MemLp (mixedStat P N ℓ ξ) 2 (gibbsMeasure P N) ∧
      MemLp (mixedOp P N ℓ ψh hψh) 2 (gibbsMeasure P N)) ∧
    gibbsCov (gibbsMeasure P N) (mixedStat P N ℓ ξ) (mixedStat P N ℓ ξ) =
      2 * gibbsCov (gibbsMeasure P N) (mixedStat P N ℓ ξ) (mixedOp P N ℓ ψh hψh) -
        gibbsCov (gibbsMeasure P N) (mixedOp P N ℓ ψh hψh) (mixedOp P N ℓ ψh hψh) +
        gibbsCov (gibbsMeasure P N) (fun X => mixedStat P N ℓ ξ X - mixedOp P N ℓ ψh hψh X)
          (fun X => mixedStat P N ℓ ξ X - mixedOp P N ℓ ψh hψh X) ∧
    (scaledVariance P ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ)) ≠ ⊤ ∧
      gibbsCov (gibbsMeasure P N) (mixedStat P N ℓ ξ) (mixedOp P N ℓ ψh hψh) =
        (cltK N ℓ ^ P.val.2 / 2) * ((scaledVariance P ℓ ξ).toReal +
          (scaledVariance P ℓ (mixedReg hρ N ℓ ξ)).toReal -
          (scaledVariance P ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ))).toReal)) ∧
    2 * gibbsCov (gibbsMeasure P N) (mixedStat P N ℓ ξ) (mixedOp P N ℓ ψh hψh) -
        gibbsCov (gibbsMeasure P N) (mixedOp P N ℓ ψh hψh) (mixedOp P N ℓ ψh hψh) =
      cltK N ℓ ^ P.val.2 * (scaledVariance P ℓ ξ).toReal -
        cltK N ℓ ^ P.val.2 * (scaledVariance P ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ))).toReal -
        P.val.1 * cltK N ℓ ^ (2 * P.val.2 - 2) *
          ((N : ℝ) ^ (-P.val.2) * ∫ X : Configuration N,
            hessFluctExpansion P.val.2 (N : ℕ)
              (loopScaleField ℓ.val (loopMasterProfile ℓ ψh hψh).val) X.val ∂(gibbsMeasure P N)) -
        cltK N ℓ ^ (2 * P.val.2 - 1) * ∫ v in (0 : ℝ)..ℓ.val⁻¹,
          deriv (loopMasterProfile ℓ ψh hψh).val v ^ 2 := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, (loopMasterProfile ℓ ψh hψh).val t = 0 :=
    loopMaster_transport_mean_zero P (loopMasterLength ℓ) (mixedRegCircle hρ N ℓ ξ) ψh
      (mixedRegCircle_contDiff hρ N ℓ ξ) hψh htr
  have hFL2 : MemLp (mixedStat P N ℓ ξ) 2 (gibbsMeasure P N) := by
    unfold mixedStat
    exact memLp_fluctuation P N (memLp_real_of_complex (loopMasterPullback_memLp (loopMasterLength ℓ) ξ))
  have hTL2 : MemLp (mixedOp P N ℓ ψh hψh) 2 (gibbsMeasure P N) := by
    unfold mixedOp
    exact (loop_equations_ibp P hPL N ℓ (cltK N ℓ ^ (P.val.2 - 1)) (loopMasterProfile ℓ ψh hψh)
      hψh hmean).2.1.1.1
  refine ⟨⟨hFL2, hTL2⟩, ?_, ?_, ?_⟩
  · have hsplit := variance_split_of_memLp (gibbsMeasure P N) hFL2 hTL2
    unfold gibbsCov
    simpa only [sq] using hsplit
  · exact gibbsCov_mixed_eq hPL P N ℓ hρ ξ hσ ψh hψh htr
  · obtain ⟨_, hcov⟩ := gibbsCov_mixed_eq hPL P N ℓ hρ ξ hσ ψh hψh htr
    rw [hcov, gibbsCov_mixedOp_eq hPL P N ℓ hρ ξ ψh hψh htr]
    ring

end Riesz1

end
