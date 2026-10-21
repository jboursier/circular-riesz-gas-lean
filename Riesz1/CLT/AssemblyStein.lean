/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.Identity
public import Riesz1.ToMathlib.Stein.Solution
public import Riesz1.ToMathlib.Stein.Gaussian
public import Riesz1.CLT.BLDistance
public import Riesz1.Frozen.External.PrekopaLeindler

/-!
# Stein step of the central limit theorem assembly

For a bounded-Lipschitz test `f`, the Stein solution `u` of the regularized Gaussian comparison
turns the distance `E f(G_N) - E f(σ_reg Z)` into the two error terms of `clt_identity`:

`E f(G_N) - E f(σ Z) = -(Error¹(u) + Error²(u))`,

with the same integrands as the copies in `Riesz1/CLT/AssemblyInput.lean`. The bounds of `u` and
`u'` are those of the Stein existence theorem `exists_stein_solution`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ContDiff ENNReal

namespace Riesz1.Internal

/-- **Stein step.** Let `σ > 0` be the regularized standard deviation (`hσV`), let
`G = cltStat P N ℓ (ξ_reg)` be the regularized statistic with `G ∈ L²`, and let `f` be a
bounded-Lipschitz test (`BLTest f`). Then there is a `C¹` function `u` with `|u| ≤ 1` and
`|u'| ≤ √(2/π)/σ`, such that `E f(G) - E f(σ Z)` is the negative of the sum of the two error
integrals of `clt_identity`, evaluated at `u`. -/
theorem assembly_stein_identity (hPL : External.PrekopaLeindler) (P : Parameters) (N : ℕ+)
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
    (hσV : ENNReal.ofReal (σ ^ 2) = cltVariance P ℓ
      ⟨fun x => (cltScaledLift hρ ℓ (cltDelta_pos P N ℓ) ξ x : ℂ),
        cltScaledLift_memLp hρ ℓ (cltDelta_pos P N ℓ) ξ⟩)
    (hG2 : MemLp (cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ)) 2
      (gibbsMeasure P N))
    {f : ℝ → ℝ} (hf : BLTest f) :
    ∃ u : ℝ → ℝ, ContDiff ℝ 1 u ∧ (∀ x, |u x| ≤ 1) ∧
      (∀ x, |deriv u x| ≤ Real.sqrt (2 / Real.pi) / σ) ∧
      ∫ X, f (cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X) ∂(gibbsMeasure P N) -
          ∫ z, f (σ * z) ∂(ProbabilityTheory.gaussianReal 0 1) =
        -((∫ X, deriv u (cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X) *
            ((cltK N ℓ)⁻¹ * cltPairingSum ℓ (loopMasterProfile ℓ ψ hψ)
              (cltRegLine hρ P N ℓ ξ) X - σ ^ 2) ∂(gibbsMeasure P N)) +
          (-(cltK N ℓ ^ (-1 + P.val.2 / 2))) *
            gibbsCov (gibbsMeasure P N)
              (fun X => u (cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X))
              (cltRemainder P N ℓ (loopMasterProfile ℓ ψ hψ))) := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  obtain ⟨u, hu1, hode, hub, hu'b⟩ :=
    exists_stein_solution σ hσ f hf.1 hf.2.1 hf.2.2
  refine ⟨u, hu1, hub, hu'b, ?_⟩
  -- Notation for the regularized statistic and the Gaussian constant.
  set G := cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) with hGdef
  set c : ℝ := ∫ z, f (σ * z) ∂(ProbabilityTheory.gaussianReal 0 1) with hcdef
  have hc : ∫ y, f y ∂(ProbabilityTheory.gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) = c :=
    stein_integral_gaussian_scale σ hf.1.continuous
  -- The Stein equation holds pointwise at `G X`.
  have hpt : ∀ X, f (G X) = σ ^ 2 * deriv u (G X) - u (G X) * G X + c := by
    intro X
    have h := hode (G X)
    rw [hc] at h
    linarith [mul_comm (G X) (u (G X))]
  -- Integrability of the pieces.
  have hGm : AEStronglyMeasurable G (gibbsMeasure P N) := hG2.aestronglyMeasurable
  have hI1 : Integrable (fun X => deriv u (G X)) (gibbsMeasure P N) :=
    Integrable.of_bound ((hu1.continuous_deriv le_rfl).comp_aestronglyMeasurable hGm)
      (Real.sqrt (2 / Real.pi) / σ)
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]
        exact hu'b (G X))
  have hI2 : Integrable (fun X => u (G X) * G X) (gibbsMeasure P N) :=
    Integrable.mono' (hG2.integrable one_le_two).norm
      ((hu1.continuous.comp_aestronglyMeasurable hGm).mul hGm)
      (Eventually.of_forall fun X => by
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hub (G X)))
  have hI3 : Integrable (fun X => σ ^ 2 * deriv u (G X) - u (G X) * G X) (gibbsMeasure P N) :=
    (hI1.const_mul _).sub hI2
  -- The integral of `f(G)` splits into the Stein terms.
  have hsplit : ∫ X, f (G X) ∂(gibbsMeasure P N) =
      σ ^ 2 * ∫ X, deriv u (G X) ∂(gibbsMeasure P N) -
        ∫ X, u (G X) * G X ∂(gibbsMeasure P N) + c := by
    have h1 : ∫ X, f (G X) ∂(gibbsMeasure P N) =
        ∫ X, (σ ^ 2 * deriv u (G X) - u (G X) * G X + c) ∂(gibbsMeasure P N) :=
      integral_congr_ae (Eventually.of_forall hpt)
    rw [h1, integral_add hI3 (integrable_const c), integral_sub (hI1.const_mul _) hI2,
      integral_const_mul, integral_const]
    simp
  -- The identity `clt_identity` (iii) at the Stein solution.
  have hiii := (clt_identity hPL P N ℓ hK hρ ξ ψ hψ htr σ hσ hσV).2.2.2.1 u hu1
    ⟨1, hub⟩ ⟨Real.sqrt (2 / Real.pi) / σ, hu'b⟩
  rw [← hGdef] at hiii
  rw [hsplit]
  linarith [hiii]

end Riesz1.Internal

end
end
