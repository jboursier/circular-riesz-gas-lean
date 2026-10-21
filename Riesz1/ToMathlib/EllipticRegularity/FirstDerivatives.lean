/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.Localization
public import Riesz1.ToMathlib.EllipticRegularity.Representatives
public import Riesz1.ToMathlib.EllipticRegularity.GlobalBridge
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# First weak derivatives from the local equation

This proves the initial gradient step of the interior H² regularity argument for
complex Hilbert valued solutions. The L² assumption is on the original
open domain, and the conclusion is an actual weak derivative for every
smooth interior cutoff, in the part 1 encoding.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap Laplacian LineDeriv ContDiff

namespace Riesz1.Internal

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A smooth interior cutoff of an L² distributional solution has a
global L² weak derivative in every direction. No initial gradient or
pointwise regularity of the solution is assumed. -/
theorem schrodinger_cutoff_weak_derivative {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ) {u : E → F}
    (huL : MemLp u 2 (volume.restrict U))
    (hu : IsDistributionalSchrodingerSolution U W lam u)
    {b : E → ℝ} (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ U) (v : E) :
    ∃ g : Lp F 2 (volume : Measure E),
      HasWeakDirectionalDerivativeOn univ (fun x => b x • u x) (g : E → F) v := by
  have hz : MemLp (U.indicator u) 2 volume :=
    (memLp_indicator_iff_restrict hU.measurableSet.nullMeasurableSet).mpr huL
  let w : Lp F 2 (volume : Measure E) := hz.toLp (U.indicator u)
  have hwu : (w : E → F) =ᵐ[volume.restrict U] u := by
    filter_upwards [ae_restrict_of_ae hz.coeFn_toLp,
      ae_restrict_mem hU.measurableSet] with x hx hxU
    exact hx.trans (indicator_of_mem hxU u)
  have hw := hu.congr hU hwu.symm
  have hBc : HasCompactSupport (fun x => (b x : ℂ)) :=
    hbc.comp_left (map_zero Complex.ofRealCLM)
  have hBs : ContDiff ℝ ∞ (fun x => (b x : ℂ)) := Complex.ofRealCLM.contDiff.comp hb
  have hB : Function.HasTemperateGrowth (fun x => (b x : ℂ)) :=
    (hBc.toSchwartzMap hBs).hasTemperateGrowth
  have h1 := schrodinger_cutoff_memSobolev_one hU hW lam w hw hb hbc hbU
  have hd : MemSobolev 0 2
      (∂_{v} (smulLeftCLM F (fun x => (b x : ℂ)) (w : 𝓢'(E, F)))) := by
    simpa using h1.lineDerivOp (m := v)
  obtain ⟨g, hg⟩ := memSobolev_zero_iff.mp hd
  have hbL : MemLp b ⊤ volume := hb.continuous.memLp_top_of_hasCompactSupport hbc volume
  have haL : MemLp (fun x => b x • w x) 2 volume := hbL.smul (Lp.memLp w)
  let a : Lp F 2 (volume : Measure E) := haL.toLp (fun x => b x • w x)
  have hTa : smulLeftCLM F (fun x => (b x : ℂ)) (w : 𝓢'(E, F)) =
      (a : 𝓢'(E, F)) := by
    ext ψ
    rw [smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
      Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [haL.coeFn_toLp] with x hx
    rw [hx, SchwartzMap.smulLeftCLM_apply_apply hB]
    module
  have hag : HasWeakDirectionalDerivativeOn univ (a : E → F) (g : E → F) v :=
    hasWeakDirectionalDerivativeOn_of_tempered (by rwa [hTa] at hg) univ
  have hae : (a : E → F) =ᵐ[volume] (fun x => b x • u x) := by
    filter_upwards [haL.coeFn_toLp, (ae_restrict_iff' hU.measurableSet).mp hwu] with x hx hwx
    rw [hx]
    by_cases hxU : x ∈ U
    · rw [hwx hxU]
    · have hb0 := image_eq_zero_of_notMem_tsupport (fun h => hxU (hbU h))
      simp only [hb0, zero_smul]
  exact ⟨g, hag.congr isOpen_univ (ae_restrict_of_ae hae) Filter.EventuallyEq.rfl⟩

/-- On any open region where the cutoff is one, the same L² representative
is a weak derivative of the original solution. This is the smaller-ball
conclusion used before the second localization in the interior H² regularity argument. -/
theorem schrodinger_local_weak_derivative {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ) {u : E → F}
    (huL : MemLp u 2 (volume.restrict U))
    (hu : IsDistributionalSchrodingerSolution U W lam u)
    {b : E → ℝ} (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ U) {V : Set E} (hV : IsOpen V)
    (hbV : ∀ x ∈ V, b x = 1) (v : E) :
    ∃ g : Lp F 2 (volume : Measure E), HasWeakDirectionalDerivativeOn V u (g : E → F) v := by
  obtain ⟨g, hg⟩ := schrodinger_cutoff_weak_derivative hU hW lam huL hu hb hbc hbU v
  have hlocal : HasWeakDirectionalDerivativeOn V (fun x => b x • u x) (g : E → F) v :=
    ⟨hg.1.mono_set (subset_univ V), hg.2.1.mono_set (subset_univ V),
      fun φ hφ hφc _ => hg.2.2 φ hφ hφc (subset_univ _)⟩
  have hae : (fun x => b x • u x) =ᵐ[volume.restrict V] u := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    simp only [hbV x hx, one_smul]
  exact ⟨g, hlocal.congr hV hae Filter.EventuallyEq.rfl⟩

end Riesz1.Internal
