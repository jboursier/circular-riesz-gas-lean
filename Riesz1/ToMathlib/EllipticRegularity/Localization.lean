/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.LocalTesting
public import Riesz1.ToMathlib.EllipticRegularity.TemperedProduct

/-!
# Localizing the distributional Schrödinger equation

The first gradient step of the interior H² regularity argument is obtained by a
negative-order Fourier estimate. The equation is precisely the real
compact-test predicate from part 1, including for complex solutions.
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

/-- The local compact-test equation identifies the localized tempered
Laplacian. This is valid even though the potential is unbounded globally. -/
theorem schrodinger_cutoff_laplacian {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ)
    (u : Lp F 2 (volume : Measure E))
    (hu : IsDistributionalSchrodingerSolution U W lam (u : E → F))
    {b : E → ℝ} (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ U) :
    smulLeftCLM F (fun x => (b x : ℂ)) (Δ (u : 𝓢'(E, F))) =
      smulLeftCLM F (fun x => ((b x * (W x + lam) : ℝ) : ℂ)) (u : 𝓢'(E, F)) := by
  have hBc : HasCompactSupport (fun x => (b x : ℂ)) :=
    hbc.comp_left (map_zero Complex.ofRealCLM)
  have hBs : ContDiff ℝ ∞ (fun x => (b x : ℂ)) := Complex.ofRealCLM.contDiff.comp hb
  have hB : Function.HasTemperateGrowth (fun x => (b x : ℂ)) :=
    (hBc.toSchwartzMap hBs).hasTemperateGrowth
  have hqs : ContDiff ℝ ∞ (fun x => b x * (W x + lam)) :=
    WeightedSobolev.contDiff_cutoff_mul hU hb hbU (hW.add contDiffOn_const)
  have hqc : HasCompactSupport (fun x => b x * (W x + lam)) := hbc.mul_right
  have hQc : HasCompactSupport (fun x => ((b x * (W x + lam) : ℝ) : ℂ)) :=
    hqc.comp_left (map_zero Complex.ofRealCLM)
  have hQs : ContDiff ℝ ∞ (fun x => ((b x * (W x + lam) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hqs
  have hQ : Function.HasTemperateGrowth
      (fun x => ((b x * (W x + lam) : ℝ) : ℂ)) :=
    (hQc.toSchwartzMap hQs).hasTemperateGrowth
  ext ψ
  let t : 𝓢(E, ℂ) := SchwartzMap.smulLeftCLM ℂ (fun x => (b x : ℂ)) ψ
  have ht : (t : E → ℂ) = fun x => (b x : ℂ) * ψ x :=
    SchwartzMap.smulLeftCLM_apply hB ψ
  have htc : HasCompactSupport (t : E → ℂ) := by
    rw [ht]
    exact hBc.mul_right
  have htU : tsupport (t : E → ℂ) ⊆ U := by
    rw [ht]
    exact tsupport_mul_subset_left.trans
      ((tsupport_comp_subset (map_zero Complex.ofRealCLM) b).trans hbU)
  have heq := hu.test_complex (t.smooth ⊤) htc htU
  rw [smulLeftCLM_apply_apply, laplacian_apply_apply]
  change (u : 𝓢'(E, F)) (Δ t) = _
  rw [Lp.toTemperedDistribution_apply, smulLeftCLM_apply_apply,
    Lp.toTemperedDistribution_apply]
  simp only [SchwartzMap.laplacian_apply]
  rw [← heq]
  apply integral_congr_ae
  filter_upwards with x
  rw [ht, SchwartzMap.smulLeftCLM_apply_apply hQ]
  simp only [Complex.ofReal_mul, Complex.ofReal_add]
  module

/-- Every compact smooth cutoff of a globally L² distributional
Schrödinger solution has H¹ regularity. No weak gradient is assumed.
This proves the initial gradient step of the interior H² regularity argument for
global L² representatives. -/
theorem schrodinger_cutoff_memSobolev_one {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ)
    (u : Lp F 2 (volume : Measure E))
    (hu : IsDistributionalSchrodingerSolution U W lam (u : E → F))
    {b : E → ℝ} (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ U) :
    MemSobolev 1 2 (smulLeftCLM F (fun x => (b x : ℂ)) (u : 𝓢'(E, F))) := by
  have hBc : HasCompactSupport (fun x => (b x : ℂ)) :=
    hbc.comp_left (map_zero Complex.ofRealCLM)
  have hBs : ContDiff ℝ ∞ (fun x => (b x : ℂ)) := Complex.ofRealCLM.contDiff.comp hb
  let B : 𝓢(E, ℂ) := hBc.toSchwartzMap hBs
  apply tempered_cutoff_memSobolev_one u B
  change MemSobolev 0 2 (smulLeftCLM F (fun x => (b x : ℂ)) (Δ (u : 𝓢'(E, F))))
  rw [schrodinger_cutoff_laplacian hU hW lam u hu hb hbc hbU]
  have hqs : ContDiff ℝ ∞ (fun x => b x * (W x + lam)) :=
    WeightedSobolev.contDiff_cutoff_mul hU hb hbU (hW.add contDiffOn_const)
  have hqc : HasCompactSupport (fun x => b x * (W x + lam)) := hbc.mul_right
  have hQc : HasCompactSupport (fun x => ((b x * (W x + lam) : ℝ) : ℂ)) :=
    hqc.comp_left (map_zero Complex.ofRealCLM)
  have hQs : ContDiff ℝ ∞ (fun x => ((b x * (W x + lam) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hqs
  exact memSobolev_zero_smul_schwartz (hQc.toSchwartzMap hQs) u

end Riesz1.Internal
