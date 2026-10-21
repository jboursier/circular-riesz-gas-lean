/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Stein.Expectation
public import Riesz1.CLT.IdentityIBP
public import Riesz1.CLT.IdentityMaster
public import Riesz1.CLT.IdentityStatistic
public import Riesz1.Variance.LoopIBPProposition
import all Riesz1.Variance.LoopMaster
import all Riesz1.Variance.LoopIBPMoments
import all Riesz1.Variance.LoopIBPUniform
import all Riesz1.Variance.LoopScale
import all Riesz1.Variance.LoopForce
import all Riesz1.Variance.LoopForceEnergy
import all Riesz1.CLT.IdentityDefs

/-!
# The exact approximate Gaussian identity

Part of the proof of Theorem 3: the exact approximate Gaussian identity for the regularized
statistic `G_N`, the potential `Φ_N` and the remainder `B_N`. The objects are those of the
definitions, with `ξ_reg = ξ ⋆ ρ_δ` of `IdentityDefs` and the smooth transport `ψ_reg` of `ξ_reg`.

Four assertions:

* (ii) `𝓛Φ_N - G_N = K^{-1+s/2} B_N` pointwise on configurations, and `E B_N = 0`.
* (iii) `E[u(G_N) G_N] = σ_reg² E u'(G_N) + Error¹_N(u) + Error²_N(u)` for every `C¹` function `u`
  with bounded `u` and `u'`.
* (iv) the expectation of the Stein equation (6.4), for every `C¹` test `f` with bounded
  `f` and `f'`, and `σ_reg > 0`.

It takes the Prékopa–Leindler inequality `External.PrekopaLeindler` as an explicit hypothesis.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The regularized test profile `ξ_reg` on the circle of length `ℓ⁻¹` at the smoothing radius
`δ_N`. -/
noncomputable def cltReg {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength ℓ))}) :
    Circle (loopMasterLength ℓ) → ℝ :=
  cltRegCircle hρ (loopMasterLength ℓ) (cltDelta_pos P N ℓ) ξ

/-- The regularized profile `ξ_reg` is smooth, as a function on the line. -/
lemma cltReg_contDiff {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength ℓ))}) :
    ContDiff ℝ ∞ (fun u : ℝ => cltReg hρ P N ℓ ξ (u : Circle (loopMasterLength ℓ))) :=
  cltRegCircle_contDiff hρ (loopMasterLength ℓ) (cltDelta_pos P N ℓ) ξ

/-- The statistic `G_N = K^{-s/2} Fluct_N[f]` on configurations, for the profile `f` at scale `ℓ`.
`f = u ↦ ξ_reg(u/ℓ)` gives the regularized statistic. -/
noncomputable def cltStat (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) (f : ℝ → ℝ) :
    Configuration N → ℝ :=
  fun X => cltK N ℓ ^ (-(P.val.2 / 2)) * fluctIntegral f N X.val

/-- The remainder `B_N = β Loop_ℓ[ψ_reg] - Fluct_N[ψ_reg'(·/ℓ)]`. -/
noncomputable def cltRemainder (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (Ψ : LoopScaleProfile ℓ.val) : Configuration N → ℝ :=
  fun X => P.val.1 * loopOnConfiguration (parametersExponent P) N ℓ Ψ X
    - fluctIntegral (fun u => deriv Ψ.val (u / ℓ.val)) N X.val

/-- The regularized profile `ξ_reg` as a function on the line, `v ↦ ξ_reg(v)`. -/
noncomputable def cltRegLine {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength ℓ))}) : ℝ → ℝ :=
  fun v => cltReg hρ P N ℓ ξ (v : Circle (loopMasterLength ℓ))

/-- The sum `Σᵢ q_N(xᵢ/ℓ)`, with `q_N = ψ_reg · ξ_reg'`, where `R` is the line
profile `ξ_reg` and `ξ_reg'` its derivative. -/
noncomputable def cltPairingSum {N : ℕ+} (ℓ : Ioc (0 : ℝ) 1) (Ψ : LoopScaleProfile ℓ.val)
    (R : ℝ → ℝ) (X : Configuration N) : ℝ :=
  ∑ k : Fin (N : ℕ), Ψ.val (X.val k / ℓ.val) * deriv R (X.val k / ℓ.val)

/-- The statistic `G_N` is continuous on configurations. -/
lemma continuous_cltStat (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) {f : ℝ → ℝ}
    (hf : Continuous f) : Continuous (cltStat P N ℓ f) := by
  unfold cltStat fluctIntegral
  refine continuous_const.mul (Continuous.sub ?_ continuous_const)
  refine continuous_finsetSum _ fun i _ => hf.comp ?_
  exact (continuous_apply i).comp continuous_subtype_val

/-- The scaled regularized profile `u ↦ ξ_reg(u/ℓ)` is smooth. -/
lemma cltScaledFun_contDiff {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength ℓ))}) :
    ContDiff ℝ ∞ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) :=
  (cltReg_contDiff hρ P N ℓ ξ).comp (contDiff_id.div_const ℓ.val)

/-- **Algebra of the Stein error decomposition** (assertion (iii) of the exact approximate
Gaussian identity).
Suppose `G = H - a B` pointwise, where `E H = E B = 0`, and suppose the integration by parts
`E[u(G) H] = E[u'(G) Pair]` holds. Then `E[u(G) G] = σ² E u'(G) + E[u'(G)(Pair - σ²)] - a Cov(u(G), B)`. -/
lemma clt_error_decomposition {N : ℕ+} (μ : Measure (Configuration N))
    [IsProbabilityMeasure μ] (u : ℝ → ℝ) {G H B Pair : Configuration N → ℝ} (a σ : ℝ)
    {M0 M1 : ℝ}
    (hGH : ∀ X, G X = H X - a * B X) (hHi : Integrable H μ) (hBi : Integrable B μ)
    (hBm : ∫ X, B X ∂μ = 0)
    (huG : AEStronglyMeasurable (fun X => u (G X)) μ) (hu0 : ∀ y, |u y| ≤ M0)
    (hu'G : AEStronglyMeasurable (fun X => deriv u (G X)) μ) (hu1 : ∀ y, |deriv u y| ≤ M1)
    (hPi : Integrable Pair μ)
    (hIBP : ∫ X, u (G X) * H X ∂μ = ∫ X, deriv u (G X) * Pair X ∂μ) :
    ∫ X, u (G X) * G X ∂μ = σ ^ 2 * ∫ X, deriv u (G X) ∂μ
      + ∫ X, deriv u (G X) * (Pair X - σ ^ 2) ∂μ
      + (-a) * gibbsCov μ (fun X => u (G X)) B := by
  have hA : Integrable (fun X => u (G X) * H X) μ :=
    integrable_mul_of_abs_le hHi huG (fun X => hu0 _)
  have hB : Integrable (fun X => u (G X) * B X) μ :=
    integrable_mul_of_abs_le hBi huG (fun X => hu0 _)
  have hD : Integrable (fun X => deriv u (G X) * (Pair X - σ ^ 2)) μ :=
    integrable_mul_of_abs_le (hPi.sub (integrable_const _)) hu'G (fun X => hu1 _)
  have hE : Integrable (fun X => deriv u (G X)) μ :=
    Integrable.of_bound hu'G M1 (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs]; exact hu1 _)
  have hcov : gibbsCov μ (fun X => u (G X)) B = ∫ X, u (G X) * B X ∂μ :=
    gibbsCov_eq_integral_mul_of_mean_zero μ hBi hB hBm
  have h1 : ∫ X, u (G X) * G X ∂μ = ∫ X, u (G X) * H X ∂μ - a * ∫ X, u (G X) * B X ∂μ := by
    rw [← integral_const_mul, ← integral_sub hA (hB.const_mul a)]
    congr 1
    funext X
    rw [hGH X]
    ring
  have h2 : ∫ X, deriv u (G X) * Pair X ∂μ = σ ^ 2 * ∫ X, deriv u (G X) ∂μ
      + ∫ X, deriv u (G X) * (Pair X - σ ^ 2) ∂μ := by
    rw [← integral_const_mul, ← integral_add (hE.const_mul _) hD]
    congr 1
    funext X
    ring
  rw [h1, hIBP, h2, hcov]
  ring

/-- The line profile `ξ_reg` is smooth. -/
lemma cltRegLine_contDiff {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength ℓ))}) :
    ContDiff ℝ ∞ (cltRegLine hρ P N ℓ ξ) :=
  cltReg_contDiff hρ P N ℓ ξ

/-- The line profile `ξ_reg` is `ℓ⁻¹`-periodic. -/
lemma cltRegLine_periodic {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength ℓ))}) :
    Function.Periodic (cltRegLine hρ P N ℓ ξ) ℓ.val⁻¹ := by
  intro v
  show cltReg hρ P N ℓ ξ ((v + (loopMasterLength ℓ).val : ℝ) : Circle (loopMasterLength ℓ)) =
    cltReg hρ P N ℓ ξ (v : Circle (loopMasterLength ℓ))
  rw [AddCircle.coe_add_period]

/-- The continuity of the pairing sum on configurations. -/
lemma continuous_cltPairingSum {N : ℕ+} (ℓ : Ioc (0 : ℝ) 1) (Ψ : LoopScaleProfile ℓ.val)
    {R : ℝ → ℝ} (hΨ : Continuous Ψ.val) (hR : Continuous (deriv R)) :
    Continuous (cltPairingSum (N := N) ℓ Ψ R) := by
  unfold cltPairingSum
  refine continuous_finsetSum _ fun k _ => ?_
  have hk : Continuous (fun X : Configuration N => X.val k) :=
    (continuous_apply k).comp continuous_subtype_val
  exact ((hΨ.comp ((hk).div_const _)).mul (hR.comp ((hk).div_const _)))

/-- **Exact approximate Gaussian identity** (part of the proof of Theorem 3). Let `P` be the
parameters with `β = P.1 > 0` and `0 < s < 1`, let `N ≥ 1` and `0 < ℓ ≤ 1` with `K = Nℓ ≥ 1`, and
let `ρ` be a mollifier. Let `ξ` be a square-integrable profile on the circle of length
`ℓ⁻¹`, and let `ψ` be the smooth mean-zero transport of `ξ_reg = ξ ⋆ ρ_δ` (written `ψ_reg`).
Let `σ > 0` satisfy `σ² = σ_ℓ²(ξ_reg)`. Then, with `E` the Gibbs expectation:

* (ii) `𝓛Φ_N - G_N = K^{-1+s/2} B_N` on every configuration, and `E B_N = 0`.
* (iii) for every `C¹` function `u` with bounded `u` and `u'`,
  `E[u(G_N) G_N] = σ² E u'(G_N) + Error¹_N(u) + Error²_N(u)`.
* (iv) for every `C¹` function `f` with `|f| ≤ 1` and `|f'| ≤ 1`,
  `E f(G_N) - E f(σ Z₀) = E[σ² u'_{f,σ}(G_N) - G_N u_{f,σ}(G_N)]`.

The smooth transport `ψ` is unique among smooth transports of `ξ_reg` (`loopMaster_transport_iff`),
so the statement determines `ψ_reg`. The theorem takes the Prékopa–Leindler inequality
`External.PrekopaLeindler` as a hypothesis. -/
theorem clt_identity (hPL : External.PrekopaLeindler) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (hK : 1 ≤ cltK N ℓ) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength ℓ))})
    (ψ : Circle (loopMasterLength ℓ) → ℝ)
    (hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle (loopMasterLength ℓ))))
    (htr : ∀ k : ℤ, coeff (loopMasterLength ℓ)
      ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
      transportCoeffs P (loopMasterLength ℓ)
        (loopMasterLengthTest _ (cltReg hρ P N ℓ ξ) (cltReg_contDiff hρ P N ℓ ξ)) k)
    (σ : ℝ) (hσ : 0 < σ)
    (_hσV : ENNReal.ofReal (σ ^ 2) = cltVariance P ℓ
      ⟨fun x => (cltScaledLift hρ ℓ (cltDelta_pos P N ℓ) ξ x : ℂ),
        cltScaledLift_memLp hρ ℓ (cltDelta_pos P N ℓ) ξ⟩) :
    (∃ hΦ : hsSobolevOfSmooth (rieszProb P N : Measure (HsConfiguration N))
        (loopCore ℓ (cltK N ℓ ^ (-1 + P.val.2 / 2)) (loopMasterProfile ℓ ψ hψ) hψ
          (loopMaster_transport_mean_zero P (loopMasterLength ℓ) (cltReg hρ P N ℓ ξ) ψ
            (cltReg_contDiff hρ P N ℓ ξ) hψ htr) N)
        ∈ hsNeumannDomain (rieszProb P N : Measure (HsConfiguration N)),
      hsNeumannOperator (rieszPairs P N)
          (hsRieszPairPotentials_curvature_pos N P.property.1 (parametersExponent P)) ⟨_, hΦ⟩ =
        (memLp_loopLHS P hPL ℓ (cltK N ℓ ^ (-1 + P.val.2 / 2)) (loopMasterProfile ℓ ψ hψ) hψ N).toLp
          (fun x : HsConfiguration N =>
            loopLHS P N ℓ (cltK N ℓ ^ (-1 + P.val.2 / 2)) (loopMasterProfile ℓ ψ hψ) (hsLiftPoint N x))) ∧
    (∀ X : Configuration N,
        loopOperatorPotential P N ℓ (cltK N ℓ ^ (-1 + P.val.2 / 2)) (loopMasterProfile ℓ ψ hψ) X
          - cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X
        = cltK N ℓ ^ (-1 + P.val.2 / 2) * cltRemainder P N ℓ (loopMasterProfile ℓ ψ hψ) X) ∧
    ∫ X, cltRemainder P N ℓ (loopMasterProfile ℓ ψ hψ) X ∂(gibbsMeasure P N) = 0 ∧
    (∀ u : ℝ → ℝ, ContDiff ℝ 1 u → (∃ M0, ∀ y, |u y| ≤ M0) → (∃ M1, ∀ y, |deriv u y| ≤ M1) →
      ∫ X, u (cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X)
          * cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X ∂(gibbsMeasure P N)
        = σ ^ 2 * ∫ X, deriv u (cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X)
            ∂(gibbsMeasure P N)
          + ∫ X, deriv u (cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X)
              * ((cltK N ℓ)⁻¹ * cltPairingSum ℓ (loopMasterProfile ℓ ψ hψ)
                  (cltRegLine hρ P N ℓ ξ) X - σ ^ 2) ∂(gibbsMeasure P N)
          + (-(cltK N ℓ ^ (-1 + P.val.2 / 2))) * gibbsCov (gibbsMeasure P N)
              (fun X => u (cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X))
              (cltRemainder P N ℓ (loopMasterProfile ℓ ψ hψ))) ∧
    (∀ f : ℝ → ℝ, ContDiff ℝ 1 f → (∀ x, |f x| ≤ 1) → (∀ x, |deriv f x| ≤ 1) →
      ∫ X, f (cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X) ∂(gibbsMeasure P N)
        - ∫ z, f (σ * z) ∂(gaussianReal 0 1)
        = ∫ X, (σ ^ 2 * deriv (steinSolution σ f)
                (cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X)
              - cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X
                * steinSolution σ f
                  (cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X))
            ∂(gibbsMeasure P N)) := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hK0 : 0 < cltK N ℓ := cltK_pos N ℓ
  have hℓ : 0 < ℓ.val := ℓ.property.1
  have ha : cltK N ℓ ^ (-1 + P.val.2 / 2) ≠ 0 := (Real.rpow_pos_of_pos hK0 _).ne'
  -- The smooth transport and its mean zero, and the loop equations of Proposition 5.5.
  have hΨc : Continuous (loopMasterProfile ℓ ψ hψ).val := hψ.continuous
  have hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, (loopMasterProfile ℓ ψ hψ).val t = 0 :=
    loopMaster_transport_mean_zero P (loopMasterLength ℓ) (cltReg hρ P N ℓ ξ) ψ
      (cltReg_contDiff hρ P N ℓ ξ) hψ htr
  have hloop := loop_equations_ibp P hPL N ℓ (cltK N ℓ ^ (-1 + P.val.2 / 2))
    (loopMasterProfile ℓ ψ hψ) hψ hmean
  have hHint : Integrable (loopOperatorPotential P N ℓ (cltK N ℓ ^ (-1 + P.val.2 / 2))
      (loopMasterProfile ℓ ψ hψ)) (gibbsMeasure P N) := hloop.2.1.1.1.integrable one_le_two
  have hHm := hloop.2.1.1.2
  have hcov := hloop.2.1.2
  -- The statistic and its mean zero.
  have hfc : Continuous (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) :=
    (cltScaledFun_contDiff hρ P N ℓ ξ).continuous
  have hfp := cltScaledFun_periodic hρ ℓ (cltDelta_pos P N ℓ) ξ
  have hGint : Integrable (cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ))
      (gibbsMeasure P N) :=
    (integrable_fluctIntegral P N hfc hfp).const_mul _
  have hGm : ∫ X, cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X ∂(gibbsMeasure P N)
      = 0 := by
    unfold cltStat
    rw [integral_const_mul, integral_fluctIntegral_eq_zero P N hfc hfp, mul_zero]
  -- Part (ii).
  have hpt : ∀ X : Configuration N,
      loopOperatorPotential P N ℓ (cltK N ℓ ^ (-1 + P.val.2 / 2)) (loopMasterProfile ℓ ψ hψ) X
        - cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X
      = cltK N ℓ ^ (-1 + P.val.2 / 2) * cltRemainder P N ℓ (loopMasterProfile ℓ ψ hψ) X :=
    fun X => cltPointwise P N ℓ (cltReg hρ P N ℓ ξ) (cltReg_contDiff hρ P N ℓ ξ) ψ hψ htr X
  have hBm : ∫ X, cltRemainder P N ℓ (loopMasterProfile ℓ ψ hψ) X ∂(gibbsMeasure P N) = 0 := by
    have h1 : ∫ X, cltK N ℓ ^ (-1 + P.val.2 / 2) * cltRemainder P N ℓ (loopMasterProfile ℓ ψ hψ) X
        ∂(gibbsMeasure P N) = 0 := by
      rw [← integral_congr_ae (Eventually.of_forall fun X => (hpt X))]
      rw [integral_sub hHint hGint, hHm, hGm, sub_zero]
    rw [integral_const_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left ha
  have hBint : Integrable (cltRemainder P N ℓ (loopMasterProfile ℓ ψ hψ)) (gibbsMeasure P N) := by
    refine ((hHint.sub hGint).const_mul (cltK N ℓ ^ (-1 + P.val.2 / 2))⁻¹).congr
      (Eventually.of_forall fun X => ?_)
    simp only [Pi.sub_apply]
    rw [hpt X]
    field_simp
  refine ⟨hloop.1, fun X => hpt X, hBm, ?_, ?_⟩
  · intro u hu hu0 hu1
    obtain ⟨M0, hM0⟩ := hu0
    obtain ⟨M1, hM1⟩ := hu1
    have hRC1 : ContDiff ℝ 1 (cltRegLine hρ P N ℓ ξ) := (cltRegLine_contDiff hρ P N ℓ ξ).of_le (by exact_mod_cast le_top)
    have hRdc : Continuous (deriv (cltRegLine hρ P N ℓ ξ)) :=
      hRC1.continuous_deriv (by norm_num)
    have hΨp : Function.Periodic (loopMasterProfile ℓ ψ hψ).val ℓ.val⁻¹ :=
      (loopMasterProfile ℓ ψ hψ).property.1
    -- The gradient pairing of the statistic with the potential.
    have hsc : cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ
        = fun u => cltRegLine hρ P N ℓ ξ (u / ℓ.val) := rfl
    have hpair : ∀ x : Fin N → ℝ,
        gradDotPotential (fun y => cltK N ℓ ^ (-(P.val.2 / 2))
            * fluctIntegral (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) N y)
          (loopScalePotential ℓ (cltK N ℓ ^ (-1 + P.val.2 / 2)) (loopMasterProfile ℓ ψ hψ) N) x
        = (cltK N ℓ)⁻¹ * ∑ k : Fin N, (loopMasterProfile ℓ ψ hψ).val (x k / ℓ.val)
            * deriv (cltRegLine hρ P N ℓ ξ) (x k / ℓ.val) :=
      fun x => by
        rw [hsc]
        exact gradDotPotential_loopScale (R := cltRegLine hρ P N ℓ ξ)
          (hRC1.differentiable (by norm_num)) (loopMasterProfile ℓ ψ hψ) hΨc hK0 x
    have hSc : Continuous (fun x : Fin N → ℝ => ∑ k : Fin N,
        (loopMasterProfile ℓ ψ hψ).val (x k / ℓ.val) * deriv (cltRegLine hρ P N ℓ ξ) (x k / ℓ.val)) :=
      continuous_finsetSum _ fun k _ =>
        (hΨc.comp ((continuous_apply k).div_const _)).mul
          (hRdc.comp ((continuous_apply k).div_const _))
    obtain ⟨C0, hC0⟩ := abs_sum_pairing_le (N := N) hRC1 hΨc hℓ (cltRegLine_periodic hρ P N ℓ ξ) hΨp
    have hPc : Continuous (gradDotPotential (fun x : Fin N → ℝ => cltK N ℓ ^ (-(P.val.2 / 2))
        * fluctIntegral (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) N x)
        (loopScalePotential ℓ (cltK N ℓ ^ (-1 + P.val.2 / 2)) (loopMasterProfile ℓ ψ hψ) N)) := by
      rw [show gradDotPotential (fun x : Fin N → ℝ => cltK N ℓ ^ (-(P.val.2 / 2))
          * fluctIntegral (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) N x)
          (loopScalePotential ℓ (cltK N ℓ ^ (-1 + P.val.2 / 2)) (loopMasterProfile ℓ ψ hψ) N)
          = fun x => (cltK N ℓ)⁻¹ * ∑ k : Fin N, (loopMasterProfile ℓ ψ hψ).val (x k / ℓ.val)
            * deriv (cltRegLine hρ P N ℓ ξ) (x k / ℓ.val) from funext hpair]
      exact continuous_const.mul hSc
    have hPb : ∀ x : Fin N → ℝ, |gradDotPotential (fun x : Fin N → ℝ => cltK N ℓ ^ (-(P.val.2 / 2))
        * fluctIntegral (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) N x)
        (loopScalePotential ℓ (cltK N ℓ ^ (-1 + P.val.2 / 2)) (loopMasterProfile ℓ ψ hψ) N) x|
        ≤ (cltK N ℓ)⁻¹ * C0 := fun x => by
      rw [hpair x, abs_mul, abs_of_pos (inv_pos.mpr hK0)]
      exact mul_le_mul_of_nonneg_left (hC0 x) (inv_nonneg.mpr hK0.le)
    -- The integration by parts for `u(G_N)`, with the potential of Proposition 5.5.
    have hIBP := clt_ibp_of_torus (gibbsMeasure P N) hρ _ hHint hHm _ hcov
      (fun x : Fin N → ℝ => cltK N ℓ ^ (-(P.val.2 / 2))
        * fluctIntegral (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) N x)
      (isTorusSmooth_scaled_fluctIntegral _ (cltScaledFun_contDiff hρ P N ℓ ξ) hfp)
      u hu hM0 hM1 hPc hPb
    have hIBP' : ∫ X, u (cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X)
          * loopOperatorPotential P N ℓ (cltK N ℓ ^ (-1 + P.val.2 / 2))
              (loopMasterProfile ℓ ψ hψ) X ∂(gibbsMeasure P N)
        = ∫ X, deriv u (cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X)
            * ((cltK N ℓ)⁻¹ * cltPairingSum ℓ (loopMasterProfile ℓ ψ hψ)
                (cltRegLine hρ P N ℓ ξ) X) ∂(gibbsMeasure P N) := by
      refine hIBP.trans (integral_congr_ae (Eventually.of_forall fun X => ?_))
      dsimp only
      rw [hpair X.val]
      rfl
    have hGH : ∀ X : Configuration N,
        cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X
          = loopOperatorPotential P N ℓ (cltK N ℓ ^ (-1 + P.val.2 / 2))
              (loopMasterProfile ℓ ψ hψ) X
            - cltK N ℓ ^ (-1 + P.val.2 / 2) * cltRemainder P N ℓ (loopMasterProfile ℓ ψ hψ) X :=
      fun X => by linarith [hpt X]
    have hPi : Integrable (fun X : Configuration N => (cltK N ℓ)⁻¹
        * cltPairingSum ℓ (loopMasterProfile ℓ ψ hψ) (cltRegLine hρ P N ℓ ξ) X)
        (gibbsMeasure P N) := by
      refine Integrable.of_bound ?_ ((cltK N ℓ)⁻¹ * C0) (Eventually.of_forall fun X => ?_)
      · exact ((continuous_cltPairingSum ℓ (loopMasterProfile ℓ ψ hψ) hΨc hRdc).const_mul _)
          |>.aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hK0)]
        exact mul_le_mul_of_nonneg_left (hC0 X.val) (inv_nonneg.mpr hK0.le)
    have huG : AEStronglyMeasurable
        (fun X => u (cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X)) (gibbsMeasure P N) :=
      (hu.continuous.comp (continuous_cltStat P N ℓ hfc)).aestronglyMeasurable
    have hu'G : AEStronglyMeasurable
        (fun X => deriv u (cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X))
        (gibbsMeasure P N) :=
      ((hu.continuous_deriv (by norm_num)).comp (continuous_cltStat P N ℓ hfc)).aestronglyMeasurable
    exact clt_error_decomposition (gibbsMeasure P N) u (cltK N ℓ ^ (-1 + P.val.2 / 2)) σ hGH
      hHint hBint hBm huG hM0 hu'G hM1 hPi hIBP'
  · intro f hf hfb hf'
    exact stein_expectation_identity (gibbsMeasure P N) σ hσ f hf hfb hf'
      (cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ))
      (continuous_cltStat P N ℓ hfc).aestronglyMeasurable

end Riesz1

end
