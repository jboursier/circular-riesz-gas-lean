/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.IdentityDefs
public import Riesz1.CLT.IdentityDerivatives
public import Riesz1.Variance.LoopIBPProposition
public import Riesz1.Variance.LoopScaleDifferential
public import Riesz1.Gibbs.FluctuationMoments
public import Riesz1.Variance.LoopIBPPairs
import all Riesz1.Variance.LoopIBPUniform
import all Riesz1.Variance.LoopScale
import all Riesz1.Variance.LoopForce
import all Riesz1.Variance.LoopIBPMoments
import all Riesz1.Variance.LoopForceEnergy
import all Riesz1.Variance.LoopScaleDifferential

/-!
# The equation `𝓛Φ_N - G_N = K^{-1+s/2} B_N` and the mean of `B_N`

First identity of Theorem 3. The loop master equation `loop_equations_master` holds
with the potential at amplitude `a₀ = K^{s-1}`. Multiplying by `K^{-s/2}` gives the potential
`Φ_N` at amplitude `K^{-1+s/2}` and the statistic `G_N`, which is the
content of the pointwise identity `cltPointwise`. The mean of `B_N` then follows from the mean
zero of the operator image in Proposition 5.5 and of the fluctuation.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The product `K = Nℓ`. -/
noncomputable def cltK (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) : ℝ := (N : ℝ) * ℓ.val

/-- The product `K = Nℓ` is positive. -/
lemma cltK_pos (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) : 0 < cltK N ℓ :=
  mul_pos (by exact_mod_cast N.pos) ℓ.property.1

/-- The scalar potential is linear in its amplitude. -/
lemma loopScalePotential_const_mul (ℓ : Ioc (0 : ℝ) 1) (c a : ℝ) (Ψ : LoopScaleProfile ℓ.val)
    (N : ℕ) : loopScalePotential ℓ (c * a) Ψ N = fun x => c * loopScalePotential ℓ a Ψ N x := by
  funext x
  unfold loopScalePotential
  ring

/-- The scalar operator `𝓛Φ` is linear in the amplitude of the potential. -/
lemma loopOperatorPotential_const_mul (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) (c a : ℝ)
    (Ψ : LoopScaleProfile ℓ.val) (X : Configuration N) :
    loopOperatorPotential P N ℓ (c * a) Ψ X = c * loopOperatorPotential P N ℓ a Ψ X := by
  unfold loopOperatorPotential
  rw [loopScalePotential_const_mul]
  simp only [partialDeriv_const_mul, laplacian_const_mul]
  have key : ∑ k : Fin (N : ℕ), partialDeriv (energyLift (parametersExponent P) (N : ℕ)) k X.val *
      (c * partialDeriv (loopScalePotential ℓ a Ψ (N : ℕ)) k X.val) =
      c * ∑ k : Fin (N : ℕ), partialDeriv (energyLift (parametersExponent P) (N : ℕ)) k X.val *
        partialDeriv (loopScalePotential ℓ a Ψ (N : ℕ)) k X.val := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [key]
  ring

/-- The rescaling of the amplitude: `K^{-s/2} K^{s-1} = K^{-1+s/2}`. -/
lemma rpow_cltK_scaling (K s : ℝ) (hK : 0 < K) :
    K ^ (-(s / 2)) * K ^ (s - 1) = K ^ (-1 + s / 2) := by
  rw [← Real.rpow_add hK]
  congr 1
  ring

/-- **Pointwise identity** (first assertion of Theorem 3). Let `ξ` be a smooth
profile on the circle of length `ℓ⁻¹` with smooth mean-zero transport `ψ`. Then,
for every configuration `X`, `𝓛Φ_N(X) - G_N(X) = K^{-1+s/2} B_N(X)`, where `Φ_N` is the potential
at amplitude `K^{-1+s/2}`, `G_N = K^{-s/2} Fluct_N[ξ(·/ℓ)]` and `B_N = β Loop_ℓ[ψ] -
Fluct_N[ψ'(·/ℓ)]`. The identity is the loop master equation of `loop_equations_master` multiplied
by `K^{-s/2}`. -/
theorem cltPointwise (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ξ : Circle (loopMasterLength ℓ) → ℝ) (hξ : ContDiff ℝ ∞ (fun u : ℝ => ξ (u : Circle (loopMasterLength ℓ))))
    (ψ : Circle (loopMasterLength ℓ) → ℝ)
    (hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle (loopMasterLength ℓ))))
    (hc : ∀ k : ℤ, coeff (loopMasterLength ℓ)
      ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
      transportCoeffs P (loopMasterLength ℓ) (loopMasterLengthTest _ ξ hξ) k)
    (X : Configuration N) :
    loopOperatorPotential P N ℓ (cltK N ℓ ^ (-1 + P.val.2 / 2)) (loopMasterProfile ℓ ψ hψ) X
        - cltK N ℓ ^ (-(P.val.2 / 2)) * fluctIntegral (fun u => ξ ((u / ℓ.val : ℝ) : Circle (loopMasterLength ℓ))) N X.val
      = cltK N ℓ ^ (-1 + P.val.2 / 2) *
          (P.val.1 * loopOnConfiguration (parametersExponent P) N ℓ (loopMasterProfile ℓ ψ hψ) X
            - fluctIntegral (fun u => deriv (loopMasterProfile ℓ ψ hψ).val (u / ℓ.val)) N X.val) := by
  have hK := cltK_pos N ℓ
  have hm : loopOperatorPotential P N ℓ (cltK N ℓ ^ (P.val.2 - 1)) (loopMasterProfile ℓ ψ hψ) X
      - fluctIntegral (fun u => ξ ((u / ℓ.val : ℝ) : Circle (loopMasterLength ℓ))) N X.val
      = cltK N ℓ ^ (P.val.2 - 1) * (P.val.1 * loopOnConfiguration (parametersExponent P) N ℓ
          (loopMasterProfile ℓ ψ hψ) X
        - fluctIntegral (fun u => deriv (loopMasterProfile ℓ ψ hψ).val (u / ℓ.val)) N X.val) :=
    loop_equations_master P N ℓ ξ ψ hξ hψ hc X.val (fun _ _ hij => coe_sub_ne_zero X hij)
  have hlin : loopOperatorPotential P N ℓ (cltK N ℓ ^ (-1 + P.val.2 / 2)) (loopMasterProfile ℓ ψ hψ) X
      = cltK N ℓ ^ (-(P.val.2 / 2)) * loopOperatorPotential P N ℓ
          (cltK N ℓ ^ (P.val.2 - 1)) (loopMasterProfile ℓ ψ hψ) X := by
    rw [← loopOperatorPotential_const_mul, rpow_cltK_scaling _ _ hK]
  have hrp := rpow_cltK_scaling (cltK N ℓ) P.val.2 hK
  rw [hlin]
  linear_combination (cltK N ℓ ^ (-(P.val.2 / 2))) * hm + (P.val.1 *
    loopOnConfiguration (parametersExponent P) N ℓ (loopMasterProfile ℓ ψ hψ) X
    - fluctIntegral (fun u => deriv (loopMasterProfile ℓ ψ hψ).val (u / ℓ.val)) N X.val) * hrp

end Riesz1

end
