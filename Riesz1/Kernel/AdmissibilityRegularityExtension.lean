/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityVariance

/-!
# Circle membership and zero extension for compact profiles

The extension step is an equivalence: membership on one rescaled
circle is equivalent to line membership of the fixed zero extension. This module applies
the scaling comparison to the profile representatives, including their endpoint
conventions. The conditional assembly remains internal: deriving circle membership from
admissibility still requires Fourier decay.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Riesz1

/-- For a compact profile, Sobolev membership of the zero extension is equivalent to
membership of the test on any one scale. The chosen representative of the line class does
not matter. This is the extension step, using the scaling comparison `seminorm_scaling_full`. -/
theorem compact_lineSobolev_iff_testAtScale {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (p : Profile) (hp : CompactProfile p) (a : Scale)
    (f0 : Lp ℂ 2 (volume : Measure ℝ)) (hf0 : RepresentsZeroExtension p f0) :
    LineSobolev ((1 - s) / 2) f0 ↔
      CircleSobolev ((1 - s) / 2) (fun x => (testAtScale p a x : ℂ)) := by
  obtain ⟨ρ, hρ0, hρ1, hsupp⟩ := hp
  have hd0 : (0 : ℝ) < 1 / 2 - ρ := by linarith
  have hd1 : (1 / 2 - ρ : ℝ) < 1 / 2 := by linarith
  obtain ⟨_, _, hcomp⟩ := seminorm_scaling_full hs0 hs1 hd0 hd1
  have hsupp' : ∀ᵐ x : ℝ, 1 / 2 - (1 / 2 - ρ) < |x| → zeroExtension p x = 0 := by
    filter_upwards [hsupp] with x hx h
    exact hx (by linarith)
  have heq : f0 = (zeroExtensionL2 p).toLp _ :=
    Lp.ext (hf0.trans (zeroExtensionL2 p).coeFn_toLp.symm)
  rw [heq]
  have hcomparison := hcomp a.val (zeroExtension p) (zeroExtensionL2 p)
    a.property.1 a.property.2 hsupp'
  have hae := testAtScale_ae_eq_pullback p a
  constructor
  · intro hline
    obtain ⟨hF, hfin, _⟩ := hcomparison.1 hline
    refine ⟨testAtScaleL2 p a, ?_⟩
    rw [circleSobolevSq_congr_ae (testAtScaleL2 p a) hF hae]
    exact hfin
  · rintro ⟨hT, hfin⟩
    have hF : MemLp (pullbackPeriodization (zeroExtension p) a.val) 2 volume :=
      hT.ae_eq hae
    apply (hcomparison.2 ⟨hF, ?_⟩).1
    rw [← circleSobolevSq_congr_ae hT hF hae]
    exact hfin

namespace Internal

/-- Once circle membership has been proved at a single scale, line membership and all the
variance finiteness and comparison conclusions follow without a separate
line-membership input. Circle membership is still an analytic premise, so this assembly is
an internal helper. -/
theorem compact_variance_of_circle_membership (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (a₀ : Scale)
    (hcircle : CircleSobolev ((1 - P.val.2) / 2) (fun x => (testAtScale p a₀ x : ℂ)))
    (f0 : Lp ℂ 2 (volume : Measure ℝ)) (hf0 : RepresentsZeroExtension p f0) :
    LineSobolev ((1 - P.val.2) / 2) f0 ∧
      lineVariance P f0 < ⊤ ∧ ∃ C1 : ℝ, 0 < C1 ∧ ∀ a : Scale,
        CircleSobolev ((1 - P.val.2) / 2) (fun x => (testAtScale p a x : ℂ)) ∧
          circleVariance P p a < ⊤ ∧
          |(circleVariance P p a).toReal - (lineVariance P f0).toReal| ≤
            C1 * a.val ^ (2 - P.val.2) := by
  have hline := (compact_lineSobolev_iff_testAtScale P.property.2.1 P.property.2.2
    p hp a₀ f0 hf0).mpr hcircle
  exact ⟨hline, compact_variance_of_line_membership P p hp f0 hf0 hline⟩

/-- The variance comparison implies the limit along every scale sequence tending to zero.
The filter is arbitrary, so this includes the right-hand limit. -/
theorem compact_variance_tendsto_of_circle_membership (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (a₀ : Scale)
    (hcircle : CircleSobolev ((1 - P.val.2) / 2) (fun x => (testAtScale p a₀ x : ℂ)))
    (f0 : Lp ℂ 2 (volume : Measure ℝ)) (hf0 : RepresentsZeroExtension p f0)
    {ι : Type*} {l : Filter ι} (a : ι → Scale)
    (ha : Tendsto (fun i => (a i).val) l (𝓝 0)) :
    Tendsto (fun i => (circleVariance P p (a i)).toReal) l (𝓝 (lineVariance P f0).toReal) := by
  obtain ⟨_, _, C, _, hbound⟩ := compact_variance_of_circle_membership P p hp a₀ hcircle f0 hf0
  have hpow : Tendsto (fun i => (a i).val ^ (2 - P.val.2)) l (𝓝 0) := by
    have hpos : 0 < 2 - P.val.2 := by linarith [P.property.2.2]
    simpa only [Function.comp_def, Real.zero_rpow hpos.ne'] using
      (Real.continuousAt_rpow_const 0 (2 - P.val.2) (Or.inr hpos.le)).tendsto.comp ha
  have hlim : Tendsto (fun i => C * (a i).val ^ (2 - P.val.2)) l (𝓝 0) := by
    simpa only [mul_zero] using hpow.const_mul C
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun i => by simpa only [Real.norm_eq_abs] using (hbound (a i)).2.2) hlim

end Internal

end Riesz1
