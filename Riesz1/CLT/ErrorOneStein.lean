/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.Identity
public import Riesz1.Frozen.Variance
public import Riesz1.ToMathlib.Moments.CenteredProductBound

/-!
# The Stein error `Error¹_N(u)` and its Cauchy–Schwarz bound (first error bound in Theorem 3)

`errorOneStein` is `Error¹_N(u) = E[u'(G_N) (K⁻¹ Σ_i q_N(x_i/ℓ) - σ_reg²)]`, with
`G_N` the regularized statistic (`cltStat`), `Σ_i q_N(x_i/ℓ)` the pairing sum (`cltPairingSum`)
and `K = Nℓ` (`cltK`).

`abs_integral_stein_le` bounds it, for a pairing `F` whose Gibbs mean is `Kσ²` and whose variance
is at most `B`, by `K⁻¹ M √B` when `|u'| ≤ M`. This is the centering of the pairing followed by
the centered Cauchy–Schwarz bound of `ToMathlib/Moments/CenteredProductBound`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

namespace Riesz1.Internal

/-- `Error¹_N(u) = E[u'(G_N) (K⁻¹ Σ_i q_N(x_i/ℓ) - σ_reg²)]`. The regularized
statistic `G_N` and the pairing sum are those of the exact approximate Gaussian identity in the
proof of Theorem 3. -/
def errorOneStein {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1)
    (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength ℓ))})
    (ψ : Circle (loopMasterLength ℓ) → ℝ)
    (hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle (loopMasterLength ℓ))))
    (σ : ℝ) (u : ℝ → ℝ) : ℝ :=
  ∫ X, deriv u (cltStat P N ℓ (cltScaledFun hρ ℓ (cltDelta_pos P N ℓ) ξ) X) *
    ((cltK N ℓ)⁻¹ * cltPairingSum ℓ (loopMasterProfile ℓ ψ hψ) (cltRegLine hρ P N ℓ ξ) X - σ ^ 2)
    ∂(gibbsMeasure P N)

/-- The centered second moment is at most a bound on the variance (`variance` of
`Riesz1/Frozen/Variance.lean` is the lower integral of the centered square). -/
lemma integral_sq_centered_le_of_variance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : MemLp F 2 μ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : variance μ F (hF.integrable one_le_two) ≤ ENNReal.ofReal B) :
    ∫ X, (F X - ∫ Y, F Y ∂μ) ^ 2 ∂μ ≤ B := by
  unfold variance at hB
  have hint : Integrable (fun X => (F X - ∫ Y, F Y ∂μ) ^ 2) μ :=
    ((hF.sub (memLp_const _)).integrable_sq)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun X => sq_nonneg _)
    hint.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hB0 hB

/-- **Centered Cauchy–Schwarz for the Stein error.** For a probability measure `μ`, a pairing `F`
with `∫ F = K σ²` and `K > 0`, and a bounded `g` with `|g| ≤ M`, the integral
`∫ g (K⁻¹ F - σ²)` is at most `K⁻¹ M √B` in absolute value, when the variance of `F` is at most
`B`. -/
lemma abs_integral_stein_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F g : Ω → ℝ} {K σ M B : ℝ} (hK : 0 < K) (hM : 0 ≤ M)
    (hB0 : 0 ≤ B) (hF : MemLp F 2 μ) (hcent : ∫ X, F X ∂μ = K * σ ^ 2)
    (hg : ∀ X, |g X| ≤ M)
    (hB : variance μ F (hF.integrable one_le_two) ≤ ENNReal.ofReal B) :
    |∫ X, g X * (K⁻¹ * F X - σ ^ 2) ∂μ| ≤ K⁻¹ * M * Real.sqrt B := by
  have hinv : K⁻¹ * K = 1 := inv_mul_cancel₀ hK.ne'
  -- The integrand is `K⁻¹` times the centered product, since `∫ F = K σ²`.
  have hid : ∀ X, g X * (K⁻¹ * F X - σ ^ 2) =
      K⁻¹ * (g X * (F X - ∫ Y, F Y ∂μ)) := by
    intro X
    rw [hcent]
    linear_combination (g X * σ ^ 2) * hinv
  have hcen := abs_integral_mul_centred_le hF hM hg
  have hsq := integral_sq_centered_le_of_variance hF hB0 hB
  have hsqrt : Real.sqrt (∫ X, (F X - ∫ Y, F Y ∂μ) ^ 2 ∂μ) ≤ Real.sqrt B :=
    Real.sqrt_le_sqrt hsq
  simp_rw [hid]
  rw [integral_const_mul, abs_mul, abs_of_pos (inv_pos.2 hK)]
  have hK0 : 0 ≤ K⁻¹ := (inv_pos.2 hK).le
  calc K⁻¹ * |∫ X, g X * (F X - ∫ Y, F Y ∂μ) ∂μ|
      ≤ K⁻¹ * (M * Real.sqrt (∫ X, (F X - ∫ Y, F Y ∂μ) ^ 2 ∂μ)) :=
        mul_le_mul_of_nonneg_left hcen hK0
    _ ≤ K⁻¹ * (M * Real.sqrt B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqrt hM) hK0
    _ = K⁻¹ * M * Real.sqrt B := by ring

end Riesz1.Internal

end
end
