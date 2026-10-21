/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.Identity
public import Riesz1.Kernel.MeanFieldEnergy
public import Riesz1.Variance.LoopMasterScaling
public import Riesz1.Gibbs.UniformMarginals
public import Riesz1.ToMathlib.CircleBasics
public import Riesz1.ToMathlib.CircleFourierPairing
import all Riesz1.Variance.LoopMaster
import all Riesz1.CLT.IdentityDefs

/-!
# The centering identity of the Stein error

The pairing sum `Σ_k ψ(X_k/ℓ) ξ_reg'(X_k/ℓ)` in Theorem 3 has Gibbs mean `K σ²`,
where `K = Nℓ` and `σ²` is the variance `cltVariance` of the scaled regularized profile.

The proof has three steps. The uniform marginals of the Gibbs law reduce the mean to `N` times one
period integral. The energy identity `mean_field_energy_identity` on the unit circle, applied to
the pulled back profile and transport, identifies that integral with the variance. The final step
is a real algebra identity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ContDiff ENNReal

namespace Riesz1.Internal

/-- The derivative of `t ↦ R (t c)` at `x` is `c R'(x c)`. -/
lemma cltCentering_deriv_scale (R : ℝ → ℝ) (hR : Differentiable ℝ R) (c x : ℝ) :
    deriv (fun t => R (t * c)) x = deriv R (x * c) * c := by
  have h1 : HasDerivAt (fun t : ℝ => t * c) c x := hasDerivAt_mul_const c
  have h2 : HasDerivAt R (deriv R (x * c)) (x * c) := (hR (x * c)).hasDerivAt
  exact (h2.comp x h1).deriv

/-- The profile `x ↦ Ψ(x/c) R'(x/c)` is one-periodic when `Ψ` and `R` have period `c⁻¹`. -/
lemma cltCentering_periodic {c : ℝ} {Ψ R : ℝ → ℝ} (hΨp : Function.Periodic Ψ c⁻¹)
    (hRp : Function.Periodic R c⁻¹) :
    Function.Periodic (fun x => Ψ (x / c) * deriv R (x / c)) 1 := by
  intro x
  have hshift : (x + 1) / c = x / c + c⁻¹ := by rw [add_div, one_div]
  show Ψ ((x + 1) / c) * deriv R ((x + 1) / c) = Ψ (x / c) * deriv R (x / c)
  rw [hshift, hΨp (x / c), deriv_periodic_of hRp (x / c)]

/-- The integral over the unit circle of a one-periodic lift is the integral over one period. -/
lemma cltCentering_integral_lift {f : ℝ → ℝ} (hfp : Function.Periodic f 1) :
    ∫ z : UnitAddCircle, hfp.lift z = ∫ x in (0 : ℝ)..1, f x := by
  rw [← UnitAddCircle.intervalIntegral_preimage 0 hfp.lift, zero_add]
  simp only [Function.Periodic.lift_coe]

/-- A continuous function of one circle coordinate of the Gibbs law is integrable. -/
lemma cltCentering_integrable_coord (P : Parameters) (N : ℕ+) (i : Fin (N : ℕ))
    {G : UnitAddCircle → ℝ} (hG : Continuous G) :
    Integrable (fun X : Configuration N => G ((X.val i : ℝ) : UnitAddCircle))
      (gibbsMeasure P N) := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hG.continuousOn
  exact Integrable.of_bound (hG.measurable.comp (measurable_coord N i)).aestronglyMeasurable C
    (Eventually.of_forall fun X => hC _ (mem_univ _))

/-- Uniform marginals: the Gibbs mean of a continuous function of one circle coordinate is its
integral over the circle. -/
lemma cltCentering_integral_coord (P : Parameters) (N : ℕ+) (i : Fin (N : ℕ))
    {G : UnitAddCircle → ℝ} (hG : Continuous G) :
    ∫ X, G ((X.val i : ℝ) : UnitAddCircle) ∂(gibbsMeasure P N) = ∫ z, G z := by
  have hm : AEMeasurable (fun X : Configuration N => ((X.val i : ℝ) : UnitAddCircle))
      (gibbsMeasure P N) := (measurable_coord N i).aemeasurable
  rw [← integral_map hm hG.aestronglyMeasurable, map_coord_gibbsMeasure P N i]

/-- The Gibbs mean of the pairing sum `Σ_k Ψ(X_k/c) R'(X_k/c)` is `N` times the integral of
`Ψ(x/c) R'(x/c)` over one period `[0, 1]`. -/
lemma cltCentering_gibbs_sum (P : Parameters) (N : ℕ+) {c : ℝ} {Ψ R : ℝ → ℝ}
    (hΨc : Continuous Ψ) (hRd : Continuous (deriv R))
    (hΨp : Function.Periodic Ψ c⁻¹) (hRp : Function.Periodic R c⁻¹) :
    ∫ X, ∑ k : Fin (N : ℕ), Ψ (X.val k / c) * deriv R (X.val k / c) ∂(gibbsMeasure P N)
      = (N : ℝ) * ∫ x in (0 : ℝ)..1, Ψ (x / c) * deriv R (x / c) := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hqp : Function.Periodic (fun x => Ψ (x / c) * deriv R (x / c)) 1 :=
    cltCentering_periodic hΨp hRp
  have hqc : Continuous (fun x => Ψ (x / c) * deriv R (x / c)) :=
    (hΨc.comp (continuous_id.div_const c)).mul (hRd.comp (continuous_id.div_const c))
  have hGc : Continuous hqp.lift := continuous_lift_periodic hqc hqp
  have hGq : ∀ x : ℝ, hqp.lift (x : UnitAddCircle) = Ψ (x / c) * deriv R (x / c) :=
    fun x => Function.Periodic.lift_coe hqp x
  have hsum : ∀ X : Configuration N, ∑ k : Fin (N : ℕ), Ψ (X.val k / c) * deriv R (X.val k / c)
      = ∑ k : Fin (N : ℕ), hqp.lift ((X.val k : ℝ) : UnitAddCircle) := fun X =>
    Finset.sum_congr rfl fun k _ => (hGq _).symm
  simp only [hsum]
  rw [integral_finsetSum _ fun k _ => cltCentering_integrable_coord P N k hGc]
  have hk : ∀ k : Fin (N : ℕ), ∫ X, hqp.lift ((X.val k : ℝ) : UnitAddCircle) ∂(gibbsMeasure P N)
      = ∫ z, hqp.lift z := fun k => cltCentering_integral_coord P N k hGc
  simp only [hk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [cltCentering_integral_lift hqp]

/-- The integrand of the energy identity. If `η(t) = R(t L)` on the unit circle and `R` is
differentiable, then `η'(x) φ(x) = L L^{-s} ψ(xL) R'(xL)` for the transport
`φ = L^{-s} ψ(· L)`. -/
lemma cltCentering_integrand (P : Parameters) (L : Length) (ψ : Circle L → ℝ)
    (η : UnitAddCircle → ℝ) (R : ℝ → ℝ) (hR : Differentiable ℝ R)
    (hη : ∀ t : ℝ, η (t : UnitAddCircle) = R (t * L.val)) (x : ℝ) :
    deriv (fun t : ℝ => η (t : UnitAddCircle)) x * loopMasterTransportPullback P L ψ (x : UnitAddCircle)
      = L.val * L.val ^ (-P.val.2) * (ψ ((x * L.val : ℝ) : Circle L) * deriv R (x * L.val)) := by
  have h : (fun t : ℝ => η (t : UnitAddCircle)) = fun t => R (t * L.val) := funext hη
  rw [h, cltCentering_deriv_scale R hR]
  simp only [loopMasterTransportPullback, loopMasterPullback_coe]
  ring

/-- The variance hypothesis, read as a real identity:
`σ² = (2π)^{1-s} / (2β R_s) · ℓ^{-s} · ‖g‖²` with `‖g‖² = circleSobolevSq ((1-s)/2) g`. -/
lemma cltCentering_variance_real (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (σ : ℝ)
    (g : {f : UnitAddCircle → ℂ // MemLp f 2 volume})
    (hσV : ENNReal.ofReal (σ ^ 2) = cltVariance P ℓ g) :
    σ ^ 2 = ((2 * Real.pi) ^ (1 - (parametersExponent P).val) /
        (2 * P.val.1 * rieszConstant (parametersExponent P)) * ℓ.val ^ (-P.val.2)) *
      (circleSobolevSq ((1 - (parametersExponent P).val) / 2) g).toReal := by
  have hβ : 0 < P.val.1 := P.property.1
  have hc : 0 < rieszConstant (parametersExponent P) := rieszConstant_pos _
  have hpos : 0 ≤ (2 * Real.pi) ^ (1 - P.val.2) /
        (2 * P.val.1 * rieszConstant (parametersExponent P)) * ℓ.val ^ (-P.val.2) := by
    refine mul_nonneg (div_nonneg (Real.rpow_nonneg (by positivity) _) ?_)
      (Real.rpow_nonneg ℓ.property.1.le _)
    exact (mul_pos (mul_pos two_pos hβ) hc).le
  have h1 : (ENNReal.ofReal (σ ^ 2)).toReal = (cltVariance P ℓ g).toReal := by rw [hσV]
  unfold cltVariance at h1
  rw [ENNReal.toReal_ofReal (sq_nonneg σ), ENNReal.toReal_mul, ENNReal.toReal_ofReal hpos] at h1
  exact h1

/-- The real algebra closing the centering: from `σ² = c a⁻¹ s`, `c s = ℓ⁻¹ a I` and `a > 0`,
the period integral is `I = ℓ σ²`. -/
lemma cltCentering_algebra (ℓ a c s σ I : ℝ) (hℓ : 0 < ℓ) (ha : 0 < a)
    (hσ : σ ^ 2 = c * a⁻¹ * s) (hE : c * s = ℓ⁻¹ * a * I) : I = ℓ * σ ^ 2 := by
  have hinv : a * a⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
  have hlinv : ℓ * ℓ⁻¹ = 1 := mul_inv_cancel₀ hℓ.ne'
  have h5 : a * (σ ^ 2 - ℓ⁻¹ * I) = 0 := by
    linear_combination a * hσ + (c * s) * hinv + hE
  have h6 : σ ^ 2 - ℓ⁻¹ * I = 0 := (mul_eq_zero.mp h5).resolve_left ha.ne'
  linear_combination (-ℓ) * h6 + (-I) * hlinv

/-- **The centering identity of the Stein error** (in Theorem 3, the mean of the pairing
sum `Σ_k ψ(X_k/ℓ) ξ_reg'(X_k/ℓ)`). Let `P` be a parameter value, `ρ` a mollifier, `N ≥ 1`, and
`ℓ ∈ (0, 1]`. Let `ξ` be a square integrable profile on the circle of length `ℓ⁻¹`, and let `ψ`
be a smooth transport of `ξ_reg` with the transport coefficients `htr`. Let `σ` satisfy
`σ² = σ_ℓ²(ξ_reg)`, the variance `cltVariance`. Then the Gibbs mean of `Σ_k ψ(X_k/ℓ) ξ_reg'(X_k/ℓ)`
equals `K σ²` with `K = Nℓ`. -/
theorem clt_pairing_centering (P : Parameters) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength ℓ))})
    (ψ : Circle (loopMasterLength ℓ) → ℝ)
    (hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle (loopMasterLength ℓ))))
    (htr : ∀ k : ℤ, coeff (loopMasterLength ℓ)
      ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
      transportCoeffs P (loopMasterLength ℓ)
        (loopMasterLengthTest _ (cltReg hρ P N ℓ ξ) (cltReg_contDiff hρ P N ℓ ξ)) k)
    (σ : ℝ) (hσV : ENNReal.ofReal (σ ^ 2) = cltVariance P ℓ
      ⟨fun x => (cltScaledLift hρ ℓ (cltDelta_pos P N ℓ) ξ x : ℂ),
        cltScaledLift_memLp hρ ℓ (cltDelta_pos P N ℓ) ξ⟩) :
    ∫ X, cltPairingSum ℓ (loopMasterProfile ℓ ψ hψ) (cltRegLine hρ P N ℓ ξ) X
      ∂(gibbsMeasure P N) = cltK N ℓ * σ ^ 2 := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hℓ : 0 < ℓ.val := ℓ.property.1
  -- The line profile `R = ξ_reg` is `C¹` and `ℓ⁻¹`-periodic.
  have hRC1 : ContDiff ℝ 1 (cltRegLine hρ P N ℓ ξ) :=
    (cltRegLine_contDiff hρ P N ℓ ξ).of_le (by exact_mod_cast le_top)
  have hRdiff : Differentiable ℝ (cltRegLine hρ P N ℓ ξ) := hRC1.differentiable (by norm_num)
  have hRd : Continuous (deriv (cltRegLine hρ P N ℓ ξ)) := hRC1.continuous_deriv (by norm_num)
  have hΨc : Continuous (loopMasterProfile ℓ ψ hψ).val := hψ.continuous
  have hΨp : Function.Periodic (loopMasterProfile ℓ ψ hψ).val ℓ.val⁻¹ :=
    (loopMasterProfile ℓ ψ hψ).property.1
  have hRp : Function.Periodic (cltRegLine hρ P N ℓ ξ) ℓ.val⁻¹ := cltRegLine_periodic hρ P N ℓ ξ
  -- Step 1: the Gibbs mean is `N` times one period integral (uniform marginals).
  unfold cltPairingSum
  rw [cltCentering_gibbs_sum P N hΨc hRd hΨp hRp]
  -- Step 2: the unit-circle profile `η` and transport `φ`, and their coefficient identity.
  have hL : (loopMasterLength ℓ).val = ℓ.val⁻¹ := rfl
  have hxL : ∀ x : ℝ, x * (loopMasterLength ℓ).val = x / ℓ.val := fun x => by
    rw [hL, div_eq_mul_inv]
  have hpow : (loopMasterLength ℓ).val ^ (-P.val.2) = ℓ.val ^ P.val.2 := by
    rw [hL, Real.inv_rpow hℓ.le, Real.rpow_neg hℓ.le, inv_inv]
  set η : UnitAddCircle → ℝ := loopMasterPullback (loopMasterLength ℓ) (cltReg hρ P N ℓ ξ)
    with hηdef
  set φ : UnitAddCircle → ℝ := loopMasterTransportPullback P (loopMasterLength ℓ) ψ with hφdef
  have hηs : IsSmoothCircle η := loopMasterPullback_smooth _ _ (cltReg_contDiff hρ P N ℓ ξ)
  have hφs : IsSmoothCircle φ := contDiff_const.mul (loopMasterPullback_smooth _ ψ hψ)
  have hφL2 : MemLp (fun x : UnitAddCircle => (φ x : ℂ)) 2 volume :=
    memLp_unitCircle_of_isSmoothCircle hφs
  have hcoeff : ∀ k : ℤ, circleCoeff φ k = transportCoeffs P unitLength (loopMasterTest η hηs) k :=
    fun k => loopMaster_transport_pullback P (loopMasterLength ℓ) (cltReg hρ P N ℓ ξ) ψ
      (cltReg_contDiff hρ P N ℓ ξ) hψ htr k
  -- Step 3: the energy identity on the unit circle, in its first-order form.
  obtain ⟨-, -, h3, h4⟩ := mean_field_energy_identity P ⟨η, memLp_unitCircle_of_isSmoothCircle hηs⟩
    hηs φ hφL2 hcoeff
  dsimp only at h3 h4
  have hEn := h3.trans h4
  -- The period integral of the unit-circle derivative pairing.
  have hpt : ∀ x : ℝ, deriv (fun t : ℝ => η (t : UnitAddCircle)) x * φ (x : UnitAddCircle)
      = ℓ.val⁻¹ * ℓ.val ^ P.val.2 * ((loopMasterProfile ℓ ψ hψ).val (x / ℓ.val) *
          deriv (cltRegLine hρ P N ℓ ξ) (x / ℓ.val)) := by
    intro x
    have key : deriv (fun t : ℝ => η (t : UnitAddCircle)) x * φ (x : UnitAddCircle)
        = (loopMasterLength ℓ).val * (loopMasterLength ℓ).val ^ (-P.val.2) *
          (ψ ((x * (loopMasterLength ℓ).val : ℝ) : Circle (loopMasterLength ℓ)) *
            deriv (cltRegLine hρ P N ℓ ξ) (x * (loopMasterLength ℓ).val)) :=
      cltCentering_integrand P (loopMasterLength ℓ) ψ η (cltRegLine hρ P N ℓ ξ) hRdiff
        (fun t => loopMasterPullback_coe (loopMasterLength ℓ) (cltReg hρ P N ℓ ξ) t) x
    rw [key, hxL x, hpow]
    rfl
  have hJ : ∫ x in (0 : ℝ)..1, deriv (fun t : ℝ => η (t : UnitAddCircle)) x * φ (x : UnitAddCircle)
      = ℓ.val⁻¹ * ℓ.val ^ P.val.2 * ∫ x in (0 : ℝ)..1,
          (loopMasterProfile ℓ ψ hψ).val (x / ℓ.val) * deriv (cltRegLine hρ P N ℓ ξ) (x / ℓ.val) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => hpt x
  have hE := hEn.trans hJ
  -- Step 4: the unit-circle profile `η` is the scaled regularized profile, so the variance
  -- hypothesis reads as a real identity.
  have hg : cltScaledLift hρ ℓ (cltDelta_pos P N ℓ) ξ = η := by
    funext z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [hηdef, loopMasterPullback_coe, hxL x]
    exact Function.Periodic.lift_coe (cltScaledFun_periodic hρ ℓ (cltDelta_pos P N ℓ) ξ) x
  have hgsub : (⟨fun x => (cltScaledLift hρ ℓ (cltDelta_pos P N ℓ) ξ x : ℂ),
        cltScaledLift_memLp hρ ℓ (cltDelta_pos P N ℓ) ξ⟩ :
          {f : UnitAddCircle → ℂ // MemLp f 2 volume}) =
      ⟨fun x => (η x : ℂ), memLp_unitCircle_of_isSmoothCircle hηs⟩ :=
    Subtype.ext (by simp only [hg])
  rw [hgsub] at hσV
  have hσ := cltCentering_variance_real P ℓ σ _ hσV
  -- Step 5: the real algebra. The period integral is `ℓ σ²`, so the Gibbs mean is `N ℓ σ²`.
  have hneg : ℓ.val ^ (-P.val.2) = (ℓ.val ^ P.val.2)⁻¹ := Real.rpow_neg hℓ.le _
  have ha : 0 < ℓ.val ^ P.val.2 := Real.rpow_pos_of_pos hℓ _
  rw [hneg] at hσ
  have hfinal := cltCentering_algebra ℓ.val (ℓ.val ^ P.val.2) _ _ σ _ hℓ ha hσ hE
  unfold cltK
  rw [hfinal]
  ring
