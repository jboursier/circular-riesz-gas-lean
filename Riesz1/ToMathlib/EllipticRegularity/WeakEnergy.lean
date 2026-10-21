/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.LipschitzMultipliers

/-!
# Compact Lipschitz energy calculation with L² weak derivatives

The directional energy calculation of the interior H² regularity argument, allowing
complex L² representatives and a compact real Lipschitz cutoff.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap LineDeriv ContDiff ComplexInnerProductSpace NNReal

namespace Riesz1.Internal

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The elementary real-part expansion in the cutoff energy identity. -/
theorem cutoff_energy_pointwise (b d : ℝ) (u g : ℂ) :
    ‖d • u + b • g‖ ^ 2 = d ^ 2 * ‖u‖ ^ 2 +
      RCLike.re (⟪(2 * b * d) • u + b ^ 2 • g, g⟫ : ℂ) := by
  rw [norm_add_sq (𝕜 := ℂ)]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_add_left,
    inner_smul_left, inner_smul_right, RCLike.conj_ofReal,
    inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
    map_add, RCLike.mul_re, RCLike.mul_im, RCLike.ofReal_re, RCLike.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero, norm_smul, RCLike.norm_ofReal,
    mul_pow, sq_abs]
  ring

/-- Directional cutoff energy for an L² function with two L²
distributional derivatives. This is an internal calculus result, with
no Schrödinger equation among its hypotheses. -/
theorem lipschitz_cutoff_directional_energy
    {u g h : Lp ℂ 2 (volume : Measure E)} {v : E}
    (hu : ∂_{v} (u : 𝓢'(E, ℂ)) = (g : 𝓢'(E, ℂ)))
    (hg : ∂_{v} (g : 𝓢'(E, ℂ)) = (h : 𝓢'(E, ℂ)))
    {b : E → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b) (hbc : HasCompactSupport b) :
    Integrable (fun x => ‖fderiv ℝ b x v • u x + b x • g x‖ ^ 2) ∧
    Integrable (fun x => RCLike.re (⟪b x ^ 2 • u x, h x⟫ : ℂ)) ∧
    Integrable (fun x => (fderiv ℝ b x v) ^ 2 * ‖u x‖ ^ 2) ∧
    (∫ x, ‖fderiv ℝ b x v • u x + b x • g x‖ ^ 2) +
      (∫ x, RCLike.re (⟪b x ^ 2 • u x, h x⟫ : ℂ)) =
      ∫ x, (fderiv ℝ b x v) ^ 2 * ‖u x‖ ^ 2 := by
  obtain ⟨B, hB⟩ := exists_lipschitzWith_mul_compact hb hb hbc hbc
  have hb2 : LipschitzWith B (fun x => b x ^ 2) := by simpa only [pow_two] using hB
  have hbc2 : HasCompactSupport (fun x => b x ^ 2) := by
    have hh : HasCompactSupport (fun x => b x * b x) := hbc.mul_right
    simpa only [pow_two] using hh
  obtain ⟨hqL, hrL, hqr⟩ := lipschitz_mul_tempered_weak hu hb2 hbc2
  have hqc : HasCompactSupport (fun x => b x ^ 2 • u x) := hbc2.smul_right
  have hrc : HasCompactSupport (fun x =>
      fderiv ℝ (fun y => b y ^ 2) x v • u x + b x ^ 2 • g x) :=
    ((hbc2.fderiv_apply ℝ v).smul_right).add hbc2.smul_right
  have hp := integral_inner_tempered_compact_weak hg hqL hrL hqr hqc hrc
  have hr : (fun x => fderiv ℝ (fun y => b y ^ 2) x v • u x + b x ^ 2 • g x)
      =ᵐ[volume] (fun x => (2 * b x * fderiv ℝ b x v) • u x + b x ^ 2 • g x) := by
    filter_upwards [hb.ae_differentiableAt (μ := volume)] with x hx
    rw [fderiv_fun_pow 2 hx]
    simp only [smul_apply, Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul]
  have hrL' := (memLp_congr_ae hr).mp hrL
  have hs := (lipschitz_mul_tempered_weak hu hb hbc).2.1
  have hk : Integrable (fun x => ‖fderiv ℝ b x v • u x + b x • g x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mp hs
  have hdiL : MemLp (fun x => fderiv ℝ b x v • u x) 2 volume :=
    (memLp_top_fderiv_lipschitz hb v).smul (Lp.memLp u)
  have hdi : Integrable (fun x => ‖fderiv ℝ b x v • u x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hdiL.aestronglyMeasurable).mp hdiL
  have hdn (x : E) : ‖fderiv ℝ b x v • u x‖ ^ 2 =
      (fderiv ℝ b x v) ^ 2 * ‖u x‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hd : Integrable (fun x => (fderiv ℝ b x v) ^ 2 * ‖u x‖ ^ 2) := by
    simpa only [hdn] using hdi
  have hpot := integrable_inner_of_memLp hqL (Lp.memLp h)
  have hcross := integrable_inner_of_memLp hrL' (Lp.memLp g)
  refine ⟨hk, hpot.re, hd, ?_⟩
  have hcrossEq : (∫ x, RCLike.re (⟪(2 * b x * fderiv ℝ b x v) • u x + b x ^ 2 • g x,
      g x⟫ : ℂ)) = -(∫ x, RCLike.re (⟪b x ^ 2 • u x, h x⟫ : ℂ)) := by
    have hri : (∫ x, ⟪fderiv ℝ (fun y => b y ^ 2) x v • u x + b x ^ 2 • g x, g x⟫) =
        ∫ x, ⟪(2 * b x * fderiv ℝ b x v) • u x + b x ^ 2 • g x, g x⟫ := by
      apply integral_congr_ae
      filter_upwards [hr] with x hx
      rw [hx]
    rw [hri] at hp
    rw [integral_re hcross, integral_re hpot]
    have he := congrArg (RCLike.re (K := ℂ)) hp
    simp only [map_neg] at he
    linarith
  have hpoint := integral_congr_ae (μ := volume) (Filter.Eventually.of_forall
    (fun x => cutoff_energy_pointwise (b x) (fderiv ℝ b x v) (u x) (g x)))
  rw [integral_add hd hcross.re, hcrossEq] at hpoint
  linarith

end Riesz1.Internal
