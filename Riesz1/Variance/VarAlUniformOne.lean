/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlLoopOne
public import Riesz1.Variance.RegUniformTransport
public import Riesz1.ToMathlib.CircleMollifyAE
public import Riesz1.ToMathlib.CircleMollifySupDerivative

/-!
# The one-particle loop for regularized admissible transports

Proposition 5.9, the `N = 1` clause, with a coefficient chosen
before the profile and every representative of its transport. The
primitive bounds alone suffice, so the endpoint exponent is included.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Riesz1

/-- Proposition 5.9 at `N = 1`: the actual unit-radius convolution
of any representative of the transport has a bounded loop variance.
The coefficient depends only on `P`, the primitive data and the mollifier.
No second-derivative condition or strict singularity exponent is needed. -/
theorem varAl_loop_variance_one_uniform (P : Parameters) (η B : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    letI := (modelWellDefined P 1).2.2
    ∃ C : ℝ, 0 < C ∧
      ∀ f : {g : Circle unitLength → ℝ //
          MemLp (fun x => (g x : ℂ)) 2 (arclength unitLength)},
        PrimitiveRegularity unitLength η P.val.2 B f →
      ∀ ψ : {g : Circle unitLength → ℝ //
          MemLp (fun x => (g x : ℂ)) 2 (arclength unitLength)},
        (∀ k : ℤ, coeff unitLength ⟨(fun x => (ψ.val x : ℂ)),
          complexL2Integrable _ _ ψ.property⟩ k = transportCoeffs P unitLength f k) →
        let ψh := circleMollify ρ 1 1 (fun t : ℝ => ψ.val (t : Circle unitLength))
        ∃ hF : MemLp (fun X : Configuration 1 => loopFunctional P.val.2 1 ψh X.val)
            2 (gibbsMeasure P 1),
          variance (gibbsMeasure P 1) _ (hF.integrable one_le_two) ≤ ENNReal.ofReal C := by
  have := (modelWellDefined P 1).2.2
  obtain ⟨S, hS, hs⟩ := regUniform_transport_sup P η B hη hB
  obtain ⟨A, hA, hvar⟩ := varAlLoop_one_variance P
  let D := ∫ u, |deriv (scaledMollifier ρ 1) u|
  have hD : 0 ≤ D := integral_nonneg fun u => abs_nonneg _
  let M : NNReal := ⟨S * D + 1, by positivity⟩
  have hM : (0 : ℝ) < M := by change 0 < S * D + 1; positivity
  refine ⟨A * (M : ℝ) ^ 2, mul_pos hA (sq_pos_of_pos hM), ?_⟩
  intro f hf ψ hcoeff
  obtain ⟨ψ₀, hc, hψ₀, hcoeff₀, hb, -⟩ := hs unitLength f hf
  have hae : ψ.val =ᵐ[arclength unitLength] ψ₀ :=
    ae_eq_of_coeff_eq_real ψ.property hψ₀ (fun k => (hcoeff k).trans (hcoeff₀ k).symm)
  have heq := circleMollify_congr_circle ρ unitLength 1 hae
  change circleMollify ρ 1 1 (fun t : ℝ => ψ.val (t : Circle unitLength)) =
    circleMollify ρ 1 1 (fun t : ℝ => ψ₀ (t : Circle unitLength)) at heq
  dsimp only
  rw [heq]
  let F : ℝ → ℝ := fun t => ψ₀ (t : Circle unitLength)
  have hFc : Continuous F := hc.comp (AddCircle.continuous_mk' unitLength.val)
  have hp : Function.Periodic F 1 := by
    intro t
    change ψ₀ ((t + unitLength.val : ℝ) : Circle unitLength) = ψ₀ (t : Circle unitLength)
    rw [AddCircle.coe_add_period]
  have hsm := contDiff_circleMollify hρ zero_lt_one zero_lt_one hFc.locallyIntegrable hp
  have hlip : LipschitzWith M (circleMollify ρ 1 1 F) := by
    apply lipschitzWith_of_nnnorm_deriv_le (hsm.differentiable (by simp))
    intro x
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm, Real.norm_eq_abs]
    exact (circleMollify_deriv_le_sup hρ zero_lt_one zero_lt_one hFc hp
      (fun t => hb _) x).trans (by change S * D ≤ S * D + 1; linarith)
  exact hvar M _ hlip (Internal.circleMollify_periodic hρ zero_lt_one zero_lt_one
    hFc.locallyIntegrable hp)

end Riesz1

end
