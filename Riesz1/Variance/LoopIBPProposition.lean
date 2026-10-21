/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopIBPClauses
public import Riesz1.Variance.LoopIBPVariance
public import Riesz1.Variance.LoopIBPDomain
public import Riesz1.Variance.LoopIBPDomainOne
public import Riesz1.Variance.LoopIBPMoments
public import Riesz1.Variance.LoopIBPUniform

/-!
# The integration identities of Proposition 5.5

This file assembles the full statement of Proposition 5.5 as one
theorem, `Riesz1.loop_equations_ibp`, for every particle number `N ≥ 1`. The conjunction has five
parts, in the order of the paper:

* the domain clause: `Φ_{ψ,a}` lies in the scalar Neumann domain of the quotient Gibbs law, and
  the Neumann operator at `Φ_{ψ,a}` is the `L²` class of `𝓛Φ_{ψ,a}`.
* clause 1: `𝓛Φ_{ψ,a}` is square integrable with mean zero.
* clause 2: `Cov(F, 𝓛Φ_{ψ,a}) = E[∇F · ∇Φ_{ψ,a}]` for every torus smooth `F`.
* clause 3: `Var(𝓛Φ_{ψ,a}) = a² E[β Ψ_ψ · ∇²H_N Ψ_ψ + ‖DΨ_ψ‖²]`.
* clause 4: the loop functional and the Hessian quadratic term have every finite moment.

The mean-zero hypothesis on `ψ` and the smoothness of `ψ` are those of the paper. The external
input is the Prékopa–Leindler inequality `External.PrekopaLeindler`, passed as an explicit
hypothesis.

The clauses for `N = 1` come from the one-particle files (`loop_ibp_one`,
`loopPhi_hsNeumannOperator_one`), and those for `N ≥ 2` from `loop_ibp_clauses_ge_two`,
`loop_variance_eq` and `loopPhi_hsNeumannOperator`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- **Proposition 5.5.** Let `P` be the parameters with `β > 0` and
`0 < s < 1`, let `N ≥ 1` be the number of particles, and let `0 < ℓ ≤ 1` and `a ∈ ℝ`. Let `ψ` be a
smooth real function on `ℓ⁻¹ 𝕋` with zero mean. Then the field potential `Φ_{ψ,a}` lies in the
scalar Neumann domain of the quotient Gibbs law, and the following identities hold:

* `𝓛Φ_{ψ,a}` is square integrable with mean zero.
* `Cov(F, 𝓛Φ_{ψ,a}) = E[∇F · ∇Φ_{ψ,a}]` for every torus smooth `F`.
* `Var(𝓛Φ_{ψ,a}) = a² E[β Ψ_ψ · ∇²H_N Ψ_ψ + ‖DΨ_ψ‖²]`.
* the loop functional and the Hessian quadratic term have every finite moment. -/
theorem loop_equations_ibp (P : Parameters) (hPL : External.PrekopaLeindler) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) :
    (∃ hΦ : hsSobolevOfSmooth (rieszProb P N : Measure (HsConfiguration N))
        (loopCore ℓ a ψ hψ hmean N) ∈
          hsNeumannDomain (rieszProb P N : Measure (HsConfiguration N)),
      hsNeumannOperator (rieszPairs P N)
          (hsRieszPairPotentials_curvature_pos N P.property.1 (parametersExponent P)) ⟨_, hΦ⟩ =
        (memLp_loopLHS P hPL ℓ a ψ hψ N).toLp
          (fun x : HsConfiguration N => loopLHS P N ℓ a ψ (hsLiftPoint N x))) ∧
    ((MemLp (loopOperatorPotential P N ℓ a ψ) 2 (gibbsMeasure P N) ∧
        ∫ X : Configuration N, loopOperatorPotential P N ℓ a ψ X ∂gibbsMeasure P N = 0) ∧
      (∀ F : (Fin (N : ℕ) → ℝ) → ℝ, IsTorusSmooth F →
        gibbsCov (gibbsMeasure P N) (fun X : Configuration N => F X.val)
            (loopOperatorPotential P N ℓ a ψ) =
          ∫ X : Configuration N, gradDotPotential F (loopScalePotential ℓ a ψ (N : ℕ)) X.val
            ∂gibbsMeasure P N)) ∧
    gibbsCov (gibbsMeasure P N) (loopOperatorPotential P N ℓ a ψ)
        (loopOperatorPotential P N ℓ a ψ) =
      a ^ 2 * ∫ X : Configuration N,
        (hessianQuadratic P N ℓ ψ X + frobeniusSqDiag ℓ ψ X) ∂gibbsMeasure P N ∧
    ((∀ p : ℝ, 0 < p → Integrable (fun X : Configuration N =>
        |loopOnConfiguration (parametersExponent P) N ℓ ψ X| ^ p) (gibbsMeasure P N)) ∧
      (∀ p : ℝ, 0 < p → Integrable (fun X : Configuration N =>
        |hessianQuadratic P N ℓ ψ X| ^ p) (gibbsMeasure P N))) := by
  by_cases hN1 : (N : ℕ) = 1
  · have h1 : N = 1 := PNat.coe_eq_one_iff.mp hN1
    subst h1
    obtain ⟨hc1, hc2, hc3⟩ := loop_ibp_one P ℓ a ψ hψ
    exact ⟨loopPhi_hsNeumannOperator_one P hPL ℓ a ψ hψ hmean, ⟨hc1, hc2⟩, hc3,
      loop_moments P hPL 1 ℓ ψ⟩
  · have hN2 : 2 ≤ (N : ℕ) := by
      have := N.pos
      omega
    obtain ⟨hc1, hc2⟩ := loop_ibp_clauses_ge_two P hPL N hN2 ℓ a ψ hψ hmean
    exact ⟨loopPhi_hsNeumannOperator P hPL N hN2 ℓ a ψ hψ hmean, ⟨hc1, hc2⟩,
      loop_variance_eq P hPL N hN2 ℓ a ψ hψ hmean, loop_moments P hPL N ℓ ψ⟩

end Riesz1

end

end
