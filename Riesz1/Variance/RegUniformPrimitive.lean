/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleMollifyL2

/-!
# Uniform primitive data for the smoothed profile and its error

The (A1) part of the uniform-admissibility clause of Lemma 5.1.
The smoothed primitive has bound `B`, and the error primitive has bound `2 * B`.
These are the `PrimitiveRegularity` predicates on the original carriers.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace Riesz1.Internal

theorem coeff_sub_real_L2 (L : Length)
    (f g : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}) (k : ℤ) :
    coeff L ⟨(fun x => ((f.val x - g.val x : ℝ) : ℂ)),
      complexL2Integrable L _ (by
        exact (f.property.sub g.property).ae_eq
          (ae_of_all _ fun x => by simp only [Pi.sub_apply, Complex.ofReal_sub]))⟩ k =
    coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k -
      coeff L ⟨(fun x => (g.val x : ℂ)), complexL2Integrable L _ g.property⟩ k := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  change (∫ x : Circle L, fourier (-k) x • ((f.val x - g.val x : ℝ) : ℂ)
    ∂AddCircle.haarAddCircle) = _
  simp_rw [Complex.ofReal_sub, smul_sub]
  exact integral_sub ((f.property.haarAddCircle.integrable one_le_two).fourier_smul (-k))
    ((g.property.haarAddCircle.integrable one_le_two).fourier_smul (-k))

end Internal

/-- Smoothing preserves the full (A1) condition, with no loss in `B` or `η`.
The difference has the same exponent and bound `2 * B`. The constant bounds precede
all circle lengths and smoothing radii. This is the primitive part of the last
clause of Lemma 5.1. -/
theorem regUniform_primitive (ρ : ℝ → ℝ) (hρ : IsMollifier ρ)
    (L : Length) (η s B : ℝ)
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (hf : PrimitiveRegularity L η s B f) (h : ℝ) (hh : 0 < h) :
    ∃ g : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
      Continuous g.val ∧ ContDiff ℝ ∞ (fun x : ℝ => g.val (x : Circle L)) ∧
      (∀ x : ℝ, g.val (x : Circle L) =
        circleMollify ρ L.val h (fun t : ℝ => f.val (t : Circle L)) x) ∧
      PrimitiveRegularity L η s B g ∧
      PrimitiveRegularity L η s (2 * B)
        ⟨(fun x => f.val x - g.val x),
          by
            exact (f.property.sub g.property).ae_eq
              (ae_of_all _ fun x => by simp only [Pi.sub_apply, Complex.ofReal_sub])⟩ := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨g, hgc, hgs, hgv, hgf⟩ := Internal.exists_circleMollify_L2 hρ L hh f
  obtain ⟨Xi, hXi, hd⟩ := hf
  obtain ⟨Y, hY, hYv⟩ := Internal.holderBound_circleMollify hρ L hh hXi
  have hYm : MemLp (fun x => (Y x : ℂ)) 2 (arclength L) := by
    change MemLp (fun x => (Y x : ℂ)) 2 volume
    exact (Complex.continuous_ofReal.comp hY.1).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let Yi : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)} := ⟨Y, hYm⟩
  have hYf (k : ℤ) :
      coeff L ⟨(fun x => (Yi.val x : ℂ)), complexL2Integrable L _ Yi.property⟩ k =
        coeff L ⟨(fun x => (Xi.val x : ℂ)), complexL2Integrable L _ Xi.property⟩ k *
          (mollifierFT ρ (h * k / L.val) : ℂ) := by
    exact Internal.fourierCoeff_circleMollify hρ hh
      (hXi.1.comp (AddCircle.continuous_mk' L.val)).locallyIntegrable
      (by
        intro x
        change Xi.val ((x + L.val : ℝ) : Circle L) = Xi.val (x : Circle L)
        rw [AddCircle.coe_add_period]) Xi.val Y (fun _ => rfl) hYv k
  refine ⟨g, hgc, hgs, hgv, ⟨Yi, hY, ?_⟩, ?_⟩
  · intro k hk
    rw [hYf, hgf, ← mul_assoc, hd k hk]
  · let Z : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)} :=
      ⟨(fun x => Xi.val x - Yi.val x),
        by
          exact (Xi.property.sub Yi.property).ae_eq
            (ae_of_all _ fun x => by simp only [Pi.sub_apply, Complex.ofReal_sub])⟩
    have hZ : HolderBound L (1 - s + η) (2 * B) Z.val := by
      simpa only [two_mul] using Internal.holderBound_sub L hXi hY
    refine ⟨Z, hZ, fun k hk => ?_⟩
    rw [Internal.coeff_sub_real_L2 L Xi Yi, Internal.coeff_sub_real_L2 L f g,
      mul_sub, hd k hk, hYf, hgf, ← mul_assoc, hd k hk]

end Riesz1
