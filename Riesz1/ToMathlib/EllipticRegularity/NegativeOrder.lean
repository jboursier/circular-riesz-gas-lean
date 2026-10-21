/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.Global

/-!
# Elliptic gain from negative Sobolev order

For the first localization in the interior H² regularity argument, one can write the
cutoff Laplacian as an L² function plus derivatives of L² functions.
The results here turn such an identity into H¹ control without assuming
an initial weak gradient or using a compactness argument.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv

namespace Riesz1

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The Fourier elliptic gain holds at every real Sobolev order,
including negative orders. -/
theorem memSobolev_add_two_of_laplacian {s : ℝ} {u : 𝓢'(E, F)}
    (hu : MemSobolev s 2 u) (hΔ : MemSobolev s 2 (Δ u)) :
    MemSobolev (s + 2) 2 u := by
  have h : MemSobolev s 2 (besselPotential E F 2 u) := by
    rw [besselPotential_two_eq]
    have h := hu.sub (hΔ.smul (RCLike.ofReal (K := ℂ) ((2 * Real.pi : ℝ) ^ 2)⁻¹))
    simpa only [← RCLike.real_smul_eq_coe_smul (K := ℂ)] using h
  simpa only [add_comm] using memSobolev_besselPotential_iff.mp h

/-- An L² distribution whose Laplacian is an L² forcing plus a finite
sum of derivatives of L² functions belongs to H¹. This is an internal
estimate: the displayed Laplacian identity must still be derived from
the local equation before this theorem can be used. -/
theorem memSobolev_one_of_laplacian_eq_divergence {ι : Type*} [Fintype ι]
    (u f : Lp F 2 (volume : Measure E)) (g : ι → Lp F 2 (volume : Measure E))
    (v : ι → E)
    (heq : Δ (u : 𝓢'(E, F)) = (f : 𝓢'(E, F)) +
      ∑ i, ∂_{v i} (g i : 𝓢'(E, F))) :
    MemSobolev 1 2 (u : 𝓢'(E, F)) := by
  have hzero (a : Lp F 2 (volume : Measure E)) : MemSobolev 0 2 (a : 𝓢'(E, F)) :=
    memSobolev_zero_iff.mpr ⟨a, rfl⟩
  have hsum : MemSobolev (-1) 2 (∑ i, ∂_{v i} (g i : 𝓢'(E, F))) := by
    classical
    apply Finset.sum_induction
    · intro a b ha hb
      exact ha.add hb
    · exact memSobolev_fun_zero E F (-1) 2
    · intro i _
      simpa using (hzero (g i)).lineDerivOp (m := v i)
  have hΔ : MemSobolev (-1) 2 (Δ (u : 𝓢'(E, F))) := by
    rw [heq]
    exact ((hzero f).mono (by norm_num)).add hsum
  convert memSobolev_add_two_of_laplacian ((hzero u).mono (by norm_num)) hΔ using 1
  norm_num

end Riesz1
