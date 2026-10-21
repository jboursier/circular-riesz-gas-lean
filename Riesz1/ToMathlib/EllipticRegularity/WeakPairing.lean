/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.GlobalBridge
public import Riesz1.ToMathlib.EllipticRegularity.WeakOperations

/-!
# L² integration by parts for distributional derivatives

These pairing results support the nonsmooth testing step. Plancherel moves
the derivative to its pointwise Fourier multiplier. No differentiability of an L²
representative is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution FourierTransform Set
open scoped SchwartzMap LineDeriv ContDiff ComplexInnerProductSpace

namespace Riesz1.Internal

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Equality of a smooth multiplier of an L² distribution with an L²
distribution identifies their pointwise representatives almost everywhere.
The multiplier need not be bounded. -/
theorem smul_ae_of_tempered_eq {m : E → ℂ} (hm : m.HasTemperateGrowth)
    {u g : Lp F 2 (volume : Measure E)}
    (h : smulLeftCLM F m (u : 𝓢'(E, F)) = (g : 𝓢'(E, F))) :
    (fun x => m x • u x) =ᵐ[volume] (g : E → F) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (((Lp.memLp u).locallyIntegrable (by norm_num)).continuous_smul hm.1.continuous)
    ((Lp.memLp g).locallyIntegrable (by norm_num))
  intro φ hφ hφc
  let ψ : 𝓢(E, ℂ) := (hφc.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hφ)
  have he := congrArg (fun T : 𝓢'(E, F) => T ψ) h
  simp only [smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply] at he
  calc
    (∫ x, φ x • (m x • u x)) = ∫ x, (SchwartzMap.smulLeftCLM ℂ m ψ) x • u x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [SchwartzMap.smulLeftCLM_apply_apply hm]
      change φ x • (m x • u x) = (m x * (φ x : ℂ)) • u x
      rw [mul_comm, mul_smul]
      rfl
    _ = ∫ x, φ x • g x := he

/-- The Fourier transform of an L² distributional derivative is its
usual unbounded imaginary multiplier, almost everywhere. -/
theorem fourier_derivative_ae {u g : Lp F 2 (volume : Measure E)} {v : E}
    (h : ∂_{v} (u : 𝓢'(E, F)) = (g : 𝓢'(E, F))) :
    (fun x => (2 * Real.pi * Complex.I * (inner ℝ x v : ℂ)) • (𝓕 u) x)
      =ᵐ[volume] ((𝓕 g : Lp F 2 (volume : Measure E)) : E → F) := by
  have hm : Function.HasTemperateGrowth (fun x : E => (inner ℝ x v : ℂ)) := by
    fun_prop
  have he := congrArg (fun T : 𝓢'(E, F) => 𝓕 T) h
  rw [TemperedDistribution.fourier_lineDerivOp_eq,
    Lp.fourier_toTemperedDistribution_eq, Lp.fourier_toTemperedDistribution_eq] at he
  have he' : smulLeftCLM F
      (fun x : E => 2 * Real.pi * Complex.I * (inner ℝ x v : ℂ))
      (𝓕 u : Lp F 2 (volume : Measure E)) = (𝓕 g : Lp F 2 (volume : Measure E)) := by
    convert he using 1
    ext ψ
    simp only [smulLeftCLM_apply_apply, smul_apply,
      Lp.toTemperedDistribution_apply]
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards with x
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop),
      SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
    simp only [smul_eq_mul, mul_smul]
  exact smul_ae_of_tempered_eq (by fun_prop) he'

/-- Skew integration by parts for two L² functions with L²
distributional derivatives. All inner products are L² pairings. -/
theorem inner_tempered_derivative {a g c k : Lp F 2 (volume : Measure E)} {v : E}
    (ha : ∂_{v} (a : 𝓢'(E, F)) = (g : 𝓢'(E, F)))
    (hc : ∂_{v} (c : 𝓢'(E, F)) = (k : 𝓢'(E, F))) :
    ⟪g, c⟫ = -⟪a, k⟫ := by
  rw [← Lp.inner_fourier_eq g c, ← Lp.inner_fourier_eq a k,
    L2.inner_def, L2.inner_def, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [fourier_derivative_ae ha, fourier_derivative_ae hc] with x hx hy
  rw [← hx, ← hy, inner_smul_left, inner_smul_right]
  have hm : (starRingEnd ℂ) (2 * Real.pi * Complex.I * (inner ℝ x v : ℂ)) =
      -(2 * Real.pi * Complex.I * (inner ℝ x v : ℂ)) := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  rw [hm, neg_mul]

end Riesz1.Internal
