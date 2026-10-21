/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.LipschitzVersionAverage
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Mean value estimate for ball averages of `C¹` functions

Let `φ` be `C¹` on an open set `W`, let `G` be a vector field integrable on a compact set
`K ⊆ W` with `‖G‖ ≤ L` almost everywhere on `K`, and let `e` be a vector such that every closed
ball of radius `r` centred at a point `x + s • e`, with `s ∈ [0, 1]`, lies in `K`. Then the
averages of `φ` over the balls centred at `x` and `x + e` differ by at most `‖e‖` times
`L` plus the `L¹` distance of `∇φ` from `G` on `K`, normalized by the volume of the ball.

The proof writes the difference of the averages as an integral over `s ∈ [0,1]` of the
directional derivative along `e`. This is an internal estimate. It assumes no hypothesis on the
Sobolev class.
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ContDiff

namespace Riesz1.WeightedSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The directional derivative of `φ` along `e` is the inner product of its gradient with `e`. -/
theorem fderiv_apply_eq_inner_gradient (φ : E → ℝ) (p e : E) :
    fderiv ℝ φ p e = inner ℝ (gradient φ p) e := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]

/-- **Mean value estimate for ball averages.** See the module docstring. -/
theorem abs_ballAvg_add_sub_le_gradient {W : Set E} (hW : IsOpen W) {φ : E → ℝ}
    (hφ : ContDiffOn ℝ 1 φ W) {G : E → E} {L : ℝ} {K : Set E} (hK : IsCompact K)
    (hKW : K ⊆ W) (hGi : IntegrableOn G K volume)
    (hGL : ∀ᵐ p ∂(volume : Measure E), p ∈ K → ‖G p‖ ≤ L)
    {x e : E} {r : ℝ} (hr : 0 < r) (hsub : ∀ s ∈ Icc (0 : ℝ) 1, closedBall (x + s • e) r ⊆ K) :
    |ballAvg φ (x + e) r - ballAvg φ x r| ≤
      ‖e‖ * (L + (volume (closedBall (0 : E) r)).toReal⁻¹ *
        ∫ p in K, ‖gradient φ p - G p‖) := by
  -- Positivity and finiteness of the volume of the ball.
  have hvol_pos : 0 < volume (closedBall (0 : E) r) := measure_closedBall_pos (μ := volume) (0 : E) hr
  have hvol_top : volume (closedBall (0 : E) r) < ⊤ := measure_closedBall_lt_top
  have hvt : 0 < (volume (closedBall (0 : E) r)).toReal :=
    ENNReal.toReal_pos hvol_pos.ne' hvol_top.ne
  have hc : 0 ≤ (volume (closedBall (0 : E) r)).toReal⁻¹ := inv_nonneg.mpr hvt.le
  have hcv : (volume (closedBall (0 : E) r)).toReal⁻¹ * (volume (closedBall (0 : E) r)).toReal
      = 1 := inv_mul_cancel₀ hvt.ne'
  -- Continuity of `φ`, its derivative, and its gradient on `W`.
  have hcontφ : ContinuousOn φ W := hφ.continuousOn
  have hcontD : ContinuousOn (fun p => fderiv ℝ φ p) W :=
    hφ.continuousOn_fderiv_of_isOpen hW le_rfl
  have hdiffφ : DifferentiableOn ℝ φ W := hφ.differentiableOn (by norm_num)
  have hcontgrad : ContinuousOn (fun p => gradient φ p) W :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn hcontD
  -- Every point `x + s • e + q` with `s ∈ [0,1]` and `q` in the ball lies in `K`.
  have hpt : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ closedBall (0 : E) r, x + s • e + q ∈ K := by
    intro s hs q hq
    apply hsub s hs
    simpa [mem_closedBall, dist_eq_norm] using hq
  -- Joint continuity of the directional derivative in `(q, s)`.
  have hD_cont : ContinuousOn (fun z : E × ℝ => fderiv ℝ φ (x + z.2 • e + z.1) e)
      (closedBall (0 : E) r ×ˢ Icc (0 : ℝ) 1) := by
    have hmaps : MapsTo (fun z : E × ℝ => x + z.2 • e + z.1)
        (closedBall (0 : E) r ×ˢ Icc (0 : ℝ) 1) W := fun z hz => hKW (hpt z.2 hz.2 z.1 hz.1)
    have hc1 : ContinuousOn (fun z : E × ℝ => fderiv ℝ φ (x + z.2 • e + z.1))
        (closedBall (0 : E) r ×ˢ Icc (0 : ℝ) 1) :=
      hcontD.comp (by fun_prop : Continuous fun z : E × ℝ => x + z.2 • e + z.1).continuousOn hmaps
    exact hc1.clm_apply continuousOn_const
  -- The fundamental theorem of calculus along the segment, for each point of the ball.
  have hFTC : ∀ q ∈ closedBall (0 : E) r,
      φ (x + e + q) - φ (x + q) = ∫ s in (0 : ℝ)..1, fderiv ℝ φ (x + s • e + q) e := by
    intro q hq
    have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => φ (x + s • e + q))
        (fderiv ℝ φ (x + s • e + q) e) s := by
      intro s hs
      rw [uIcc_of_le zero_le_one] at hs
      have hpW : x + s • e + q ∈ W := hKW (hpt s hs q hq)
      have hφd : HasFDerivAt φ (fderiv ℝ φ (x + s • e + q)) (x + s • e + q) :=
        ((hdiffφ _ hpW).differentiableAt (hW.mem_nhds hpW)).hasFDerivAt
      have hin : HasDerivAt (fun s : ℝ => x + s • e + q) e s := by
        have h1 : HasDerivAt (fun s : ℝ => s • e) e s := by
          simpa using (hasDerivAt_id s).smul_const e
        simpa using (h1.const_add x).add_const q
      exact hφd.comp_hasDerivAt s hin
    have hcont_s : ContinuousOn (fun s : ℝ => fderiv ℝ φ (x + s • e + q) e) (Icc (0 : ℝ) 1) := by
      have hcs : ContinuousOn (fun s : ℝ => x + s • e + q) (Icc (0 : ℝ) 1) :=
        (by fun_prop : Continuous fun s : ℝ => x + s • e + q).continuousOn
      have hmaps : MapsTo (fun s : ℝ => x + s • e + q) (Icc (0 : ℝ) 1) W :=
        fun s hs => hKW (hpt s hs q hq)
      exact (hcontD.comp hcs hmaps).clm_apply continuousOn_const
    have hint : IntervalIntegrable (fun s : ℝ => fderiv ℝ φ (x + s • e + q) e) volume 0 1 :=
      hcont_s.intervalIntegrable_of_Icc zero_le_one
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simp only [one_smul, zero_smul, add_zero] at h
    rw [h]
  -- Integrability of the two functions of `q` appearing in the difference of averages.
  have hcontq : ∀ z : E, (∀ q ∈ closedBall (0 : E) r, z + q ∈ K) →
      ContinuousOn (fun q : E => φ (z + q)) (closedBall (0 : E) r) := fun z hz =>
    hcontφ.comp (by fun_prop : Continuous fun q : E => z + q).continuousOn
      (fun q hq => hKW (hz q hq))
  have hiB1 : IntegrableOn (fun q => φ (x + e + q)) (closedBall (0 : E) r) volume :=
    (hcontq (x + e) fun q hq => by simpa using hpt 1 ⟨zero_le_one, le_rfl⟩ q hq).integrableOn_compact
      (isCompact_closedBall _ _)
  have hiB0 : IntegrableOn (fun q => φ (x + q)) (closedBall (0 : E) r) volume :=
    (hcontq x fun q hq => by simpa using hpt 0 ⟨le_rfl, zero_le_one⟩ q hq).integrableOn_compact
      (isCompact_closedBall _ _)
  -- The difference of the averages as an average of differences.
  have havg : ballAvg φ (x + e) r - ballAvg φ x r =
      (volume (closedBall (0 : E) r)).toReal⁻¹ *
        ∫ q in closedBall (0 : E) r, (φ (x + e + q) - φ (x + q)) := by
    unfold ballAvg
    rw [integral_sub hiB1 hiB0, mul_sub]
  -- Fubini: the average of the `s`-integral is the `s`-integral of the averages.
  have hswap : ∫ q in closedBall (0 : E) r, ∫ s in (0 : ℝ)..1, fderiv ℝ φ (x + s • e + q) e
      = ∫ s in (0 : ℝ)..1, ∫ q in closedBall (0 : E) r, fderiv ℝ φ (x + s • e + q) e := by
    simp_rw [intervalIntegral.integral_of_le zero_le_one]
    refine integral_integral_swap ?_
    rw [Measure.prod_restrict]
    exact (hD_cont.integrableOn_compact ((isCompact_closedBall _ _).prod isCompact_Icc)).mono_set
      (prod_mono subset_rfl Ioc_subset_Icc_self)
  -- The pointwise bound of the inner integral, for a fixed `s ∈ (0, 1]`.
  have hbound : ∀ s ∈ Ioc (0 : ℝ) 1,
      ‖(volume (closedBall (0 : E) r)).toReal⁻¹ * ∫ q in closedBall (0 : E) r,
        fderiv ℝ φ (x + s • e + q) e‖ ≤
        ‖e‖ * (L + (volume (closedBall (0 : E) r)).toReal⁻¹ * ∫ p in K, ‖gradient φ p - G p‖) := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
    have hzK : closedBall (x + s • e) r ⊆ K := hsub s hs'
    -- Translation of `G` and of `∇φ - G` to the ball centred at `x + s • e`.
    have hmp : MeasurePreserving (fun q : E => x + s • e + q) volume volume :=
      measurePreserving_add_left volume (x + s • e)
    have hme : MeasurableEmbedding (fun q : E => x + s • e + q) :=
      (MeasurableEquiv.addLeft (x + s • e)).measurableEmbedding
    have hpre : (fun q : E => x + s • e + q) ⁻¹' closedBall (x + s • e) r =
        closedBall (0 : E) r := by
      ext q
      simp [mem_closedBall]
    have hGz : IntegrableOn (fun q => G (x + s • e + q)) (closedBall (0 : E) r) volume := by
      have h := (hmp.integrableOn_comp_preimage hme (f := G) (s := closedBall (x + s • e) r)).mpr
        (hGi.mono_set hzK)
      rwa [hpre] at h
    have hgrad_cont : ContinuousOn (fun p => gradient φ p) K := hcontgrad.mono hKW
    have hgradz : IntegrableOn (fun q => gradient φ (x + s • e + q)) (closedBall (0 : E) r)
        volume :=
      (hgrad_cont.comp (by fun_prop : Continuous fun q : E => x + s • e + q).continuousOn
        (fun q hq => hpt s hs' q hq)).integrableOn_compact (isCompact_closedBall _ _)
    have hvK : IntegrableOn (fun p => gradient φ p - G p) K volume :=
      (hgrad_cont.integrableOn_compact hK).sub hGi
    have hvz : IntegrableOn (fun q => gradient φ (x + s • e + q) - G (x + s • e + q))
        (closedBall (0 : E) r) volume := hgradz.sub hGz
    -- Splitting the integrand into the `G` part and the remainder.
    have hsplit : ∫ q in closedBall (0 : E) r, fderiv ℝ φ (x + s • e + q) e =
        (∫ q in closedBall (0 : E) r, inner ℝ (G (x + s • e + q)) e) +
          ∫ q in closedBall (0 : E) r, inner ℝ (gradient φ (x + s • e + q) - G (x + s • e + q)) e := by
      rw [← integral_add (Integrable.inner_const hGz e) (Integrable.inner_const hvz e)]
      refine integral_congr_ae (Eventually.of_forall fun q => ?_)
      simp only
      rw [fderiv_apply_eq_inner_gradient, ← inner_add_left, add_sub_cancel]
    -- The `G` part is at most `L ‖e‖` times the volume.
    have hB1 : ‖∫ q in closedBall (0 : E) r, inner ℝ (G (x + s • e + q)) e‖ ≤
        L * ‖e‖ * (volume (closedBall (0 : E) r)).toReal := by
      have hGae : ∀ᵐ q ∂(volume : Measure E), x + s • e + q ∈ K → ‖G (x + s • e + q)‖ ≤ L :=
        (measurePreserving_add_left volume (x + s • e)).quasiMeasurePreserving.ae hGL
      have hbd : ∀ᵐ q ∂(volume : Measure E), q ∈ closedBall (0 : E) r →
          ‖inner ℝ (G (x + s • e + q)) e‖ ≤ L * ‖e‖ := by
        filter_upwards [hGae] with q hq hqB
        have hGle : ‖G (x + s • e + q)‖ ≤ L := hq (hpt s hs' q hqB)
        calc ‖inner ℝ (G (x + s • e + q)) e‖ ≤ ‖G (x + s • e + q)‖ * ‖e‖ := norm_inner_le_norm _ _
          _ ≤ L * ‖e‖ := mul_le_mul_of_nonneg_right hGle (norm_nonneg e)
      have h := norm_setIntegral_le_of_norm_le_const_ae' hvol_top hbd
      rw [measureReal_def] at h
      exact h
    -- The remainder is at most `‖e‖` times the `L¹` distance on `K`.
    have hB2 : ‖∫ q in closedBall (0 : E) r, inner ℝ (gradient φ (x + s • e + q) - G (x + s • e + q)) e‖
        ≤ ‖e‖ * ∫ p in K, ‖gradient φ p - G p‖ := by
      refine (norm_integral_le_integral_norm _).trans ?_
      have hpt' : ∀ q, ‖inner ℝ (gradient φ (x + s • e + q) - G (x + s • e + q)) e‖ ≤
          ‖gradient φ (x + s • e + q) - G (x + s • e + q)‖ * ‖e‖ := fun q => norm_inner_le_norm _ _
      calc ∫ q in closedBall (0 : E) r, ‖inner ℝ (gradient φ (x + s • e + q) - G (x + s • e + q)) e‖
          ≤ ∫ q in closedBall (0 : E) r,
              ‖gradient φ (x + s • e + q) - G (x + s • e + q)‖ * ‖e‖ :=
            integral_mono (Integrable.inner_const hvz e).norm (hvz.norm.mul_const _) hpt'
        _ = ‖e‖ * ∫ q in closedBall (0 : E) r, ‖gradient φ (x + s • e + q) - G (x + s • e + q)‖ := by
            rw [integral_mul_const, mul_comm]
        _ = ‖e‖ * ∫ p in closedBall (x + s • e) r, ‖gradient φ p - G p‖ := by
            rw [integral_closedBall_add_left (fun p => ‖gradient φ p - G p‖) (x + s • e) r]
        _ ≤ ‖e‖ * ∫ p in K, ‖gradient φ p - G p‖ := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg e)
            exact setIntegral_mono_set hvK.norm (Eventually.of_forall fun p => norm_nonneg _)
              hzK.eventuallyLE
    -- Combine the two parts, using that `c · vol(B) = 1`.
    rw [hsplit, norm_mul, Real.norm_of_nonneg hc]
    calc (volume (closedBall (0 : E) r)).toReal⁻¹ *
          ‖(∫ q in closedBall (0 : E) r, inner ℝ (G (x + s • e + q)) e) +
            ∫ q in closedBall (0 : E) r, inner ℝ (gradient φ (x + s • e + q) - G (x + s • e + q)) e‖
        ≤ (volume (closedBall (0 : E) r)).toReal⁻¹ *
          (L * ‖e‖ * (volume (closedBall (0 : E) r)).toReal + ‖e‖ * ∫ p in K, ‖gradient φ p - G p‖) :=
          mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hB1 hB2)) hc
      _ = ‖e‖ * (L + (volume (closedBall (0 : E) r)).toReal⁻¹ *
          ∫ p in K, ‖gradient φ p - G p‖) := by
          linear_combination (L * ‖e‖) * hcv
  -- Assemble: the difference is the `s`-integral of the averaged derivative.
  have hkey : (volume (closedBall (0 : E) r)).toReal⁻¹ *
      ∫ q in closedBall (0 : E) r, ∫ s in (0 : ℝ)..1, fderiv ℝ φ (x + s • e + q) e =
      ∫ s in (0 : ℝ)..1, (volume (closedBall (0 : E) r)).toReal⁻¹ *
        ∫ q in closedBall (0 : E) r, fderiv ℝ φ (x + s • e + q) e := by
    rw [hswap, intervalIntegral.integral_const_mul]
  rw [havg, setIntegral_congr_fun measurableSet_closedBall (fun q hq => hFTC q hq), hkey]
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun s : ℝ => (volume (closedBall (0 : E) r)).toReal⁻¹ *
      ∫ q in closedBall (0 : E) r, fderiv ℝ φ (x + s • e + q) e)
    (C := ‖e‖ * (L + (volume (closedBall (0 : E) r)).toReal⁻¹ * ∫ p in K, ‖gradient φ p - G p‖))
    (fun s hs => hbound s (by simpa [uIoc_of_le zero_le_one] using hs))
  rw [← Real.norm_eq_abs]
  simpa using hint

end Riesz1.WeightedSobolev

end

end
