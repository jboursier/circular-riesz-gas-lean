/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Ball averages and Lebesgue differentiation

For a function `F` on a finite-dimensional real inner product space `E`, the ball average
`ballAvg F x r` is the mean of `F` over the closed ball of radius `r` centred at `x`, written over
the fixed ball `closedBall 0 r` after translation by `x`. This file proves the translation
identity, the Lebesgue differentiation statement for these averages, and the bound that transfers
an `L¹` approximation on a compact set to the averages.

These are internal analytic tools for the Lipschitz representative of `WeightedSobolev`
(`LipschitzVersion.lean`). No hypothesis is assumed.
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter Topology

namespace Riesz1.WeightedSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The mean of `F` over the closed ball of radius `r` centred at `x`, in translated form. -/
@[expose]
def ballAvg (F : E → ℝ) (x : E) (r : ℝ) : ℝ :=
  (volume (closedBall (0 : E) r)).toReal⁻¹ * ∫ q in closedBall (0 : E) r, F (x + q)

/-- Translating the integration domain: the integral over `closedBall 0 r` of `f (z + ·)` equals
the integral of `f` over `closedBall z r`. -/
theorem integral_closedBall_add_left (f : E → ℝ) (z : E) (r : ℝ) :
    ∫ q in closedBall (0 : E) r, f (z + q) = ∫ p in closedBall z r, f p := by
  have h1 : ∀ q : E, (closedBall z r).indicator f (z + q) =
      (closedBall (0 : E) r).indicator (fun q => f (z + q)) q := by
    intro q
    by_cases hq : q ∈ closedBall (0 : E) r
    · have hq' : z + q ∈ closedBall z r := by
        simpa [mem_closedBall, dist_self_add_left] using hq
      rw [indicator_of_mem hq, indicator_of_mem hq']
    · have hq' : z + q ∉ closedBall z r := by
        simpa [mem_closedBall, dist_self_add_left] using hq
      rw [indicator_of_notMem hq, indicator_of_notMem hq']
  rw [← integral_indicator measurableSet_closedBall, ← integral_indicator measurableSet_closedBall]
  simp_rw [← h1]
  exact integral_add_left_eq_self (fun p => (closedBall z r).indicator f p) z

/-- The volume of a closed ball does not depend on its centre. -/
theorem volume_closedBall_eq_zero (x : E) (r : ℝ) :
    volume (closedBall x r) = volume (closedBall (0 : E) r) :=
  Measure.addHaar_closedBall_center volume x r

/-- The average over `closedBall x r` written in the translated form of `ballAvg`. -/
theorem setAverage_closedBall_eq_ballAvg (F : E → ℝ) (x : E) (r : ℝ) :
    ⨍ y in closedBall x r, F y = ballAvg F x r := by
  have h : ∫ q in closedBall (0 : E) r, F (x + q) = ∫ p in closedBall x r, F p :=
    integral_closedBall_add_left F x r
  unfold ballAvg
  rw [h, setAverage_eq, measureReal_def, volume_closedBall_eq_zero]
  rfl

/-- **Lebesgue differentiation for ball averages.** If `F` is locally integrable, then almost
every point `x` has ball averages converging to `F x` as the radius decreases to zero. -/
theorem ae_tendsto_ballAvg {F : E → ℝ} (hF : LocallyIntegrable F volume) :
    ∀ᵐ x ∂(volume : Measure E), Tendsto (fun r => ballAvg F x r) (𝓝[>] (0 : ℝ)) (𝓝 (F x)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average (volume : Measure E) hF 1]
    with x hx
  have hlim := hx (ι := ℝ) (l := 𝓝[>] (0 : ℝ)) (fun _ => x) id tendsto_id ?_
  · refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r _
    simp only [id]
    rw [setAverage_closedBall_eq_ballAvg]
  · filter_upwards [self_mem_nhdsWithin] with r hr
    simpa using (mem_closedBall_self (le_of_lt hr) : x ∈ closedBall x r)

/-- **Approximation of ball averages.** If `closedBall x r ⊆ K` and both functions are integrable
on `K`, then the averages of `φ` and `F` over `closedBall x r` differ by at most the `L¹` distance
on `K`, multiplied by the reciprocal of the volume of the ball. -/
theorem abs_ballAvg_sub_le {φ F : E → ℝ} {K : Set E} {x : E} {r : ℝ}
    (hxK : closedBall x r ⊆ K) (hφ : IntegrableOn φ K volume) (hF : IntegrableOn F K volume) :
    |ballAvg φ x r - ballAvg F x r| ≤
      (volume (closedBall (0 : E) r)).toReal⁻¹ * ∫ p in K, |φ p - F p| := by
  have hmp : MeasurePreserving (fun q : E => x + q) volume volume :=
    measurePreserving_add_left volume x
  have hme : MeasurableEmbedding (fun q : E => x + q) :=
    (MeasurableEquiv.addLeft x).measurableEmbedding
  have hpre : (fun q : E => x + q) ⁻¹' closedBall x r = closedBall (0 : E) r := by
    ext q
    simp [mem_closedBall]
  have hBt : ∀ g : E → ℝ, IntegrableOn g K volume →
      IntegrableOn (fun q => g (x + q)) (closedBall (0 : E) r) volume := by
    intro g hg
    have h := (hmp.integrableOn_comp_preimage hme (f := g) (s := closedBall x r)).mpr
      (hg.mono_set hxK)
    rwa [hpre] at h
  have hdiff : ballAvg φ x r - ballAvg F x r =
      (volume (closedBall (0 : E) r)).toReal⁻¹ *
        ∫ q in closedBall (0 : E) r, (φ (x + q) - F (x + q)) := by
    rw [ballAvg, ballAvg, integral_sub (hBt φ hφ) (hBt F hF), mul_sub]
  have hc : 0 ≤ (volume (closedBall (0 : E) r)).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  rw [hdiff, abs_mul, abs_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  have hint : IntegrableOn (fun p => |φ p - F p|) K volume :=
    (hφ.sub hF).abs
  have hsub : ∫ q in closedBall (0 : E) r, (φ (x + q) - F (x + q)) =
      ∫ p in closedBall x r, (φ p - F p) :=
    integral_closedBall_add_left (fun p => φ p - F p) x r
  calc |∫ q in closedBall (0 : E) r, (φ (x + q) - F (x + q))|
      = |∫ p in closedBall x r, (φ p - F p)| := by rw [hsub]
    _ ≤ ∫ p in closedBall x r, |φ p - F p| := abs_integral_le_integral_abs
    _ ≤ ∫ p in K, |φ p - F p| :=
        setIntegral_mono_set hint (Eventually.of_forall fun p => abs_nonneg _)
          hxK.eventuallyLE

end Riesz1.WeightedSobolev

end

end
