/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Variational.EuclideanCompletion
public import Riesz1.ToMathlib.WeightedSobolev.BoundedDomainComposition
public import Riesz1.ToMathlib.PeriodicMarkCutoff
public import Mathlib.Tactic.Module

/-!
# Algebra of bounded weighted Sobolev functions

The product rule is proved in the completion of the smooth graph.
Polarization reduces it to the bounded smooth scalar chain rule.
No inference from classical almost everywhere differentiability is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Riesz1.WeightedSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasure μ] {U : Set E}

/-- A smooth jet is an element of the weighted completion. -/
theorem isWeightedH1_of_smoothNearClosure (hU : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) {f : E → ℝ} (hf : SmoothNearClosure U f) :
    IsWeightedH1 μ U f (gradient f) :=
  IsGraphH1.of_test (value := id) hf (memLp_of_smoothNearClosure hU hμ hf).1
    (memLp_of_smoothNearClosure hU hμ hf).2

/-- Addition in the completed smooth graph. -/
theorem IsWeightedH1.add (hU : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {F H : E → ℝ} {G K : E → E} (hF : IsWeightedH1 μ U F G)
    (hH : IsWeightedH1 μ U H K) :
    IsWeightedH1 μ U (fun x => F x + H x) (fun x => G x + K x) := by
  have hf : IsWeightedH1 μ U (hF.1.toLp F) (hF.2.1.toLp G) :=
    hF.congr hF.1.coeFn_toLp.symm hF.2.1.coeFn_toLp.symm
  have hh : IsWeightedH1 μ U (hH.1.toLp H) (hH.2.1.toLp K) :=
    hH.congr hH.1.coeFn_toLp.symm hH.2.1.coeFn_toLp.symm
  have ha := (Variational.sobolevSubmodule μ U hU hμ).add_mem
    ((Variational.mem_iff μ U hU hμ _ _).mpr hf)
    ((Variational.mem_iff μ U hU hμ _ _).mpr hh)
  have hr := (Variational.mem_iff μ U hU hμ _ _).mp ha
  simp only [Equiv.toFun_as_coe, ← WithLp.equiv_symm_apply, Equiv.apply_symm_apply] at hr
  apply hr.congr
  · filter_upwards [Lp.coeFn_add (hF.1.toLp F) (hH.1.toLp H),
      hF.1.coeFn_toLp, hH.1.coeFn_toLp] with x hx hfx hhx
    simpa only [Pi.add_apply, hfx, hhx] using hx
  · filter_upwards [Lp.coeFn_add (hF.2.1.toLp G) (hH.2.1.toLp K),
      hF.2.1.coeFn_toLp, hH.2.1.coeFn_toLp] with x hx hgx hkx
    simpa only [Pi.add_apply, hgx, hkx] using hx

/-- Scalar multiplication in the completed smooth graph. -/
theorem IsWeightedH1.const_smul (hU : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) {F : E → ℝ} {G : E → E}
    (hF : IsWeightedH1 μ U F G) (a : ℝ) :
    IsWeightedH1 μ U (fun x => a * F x) (fun x => a • G x) := by
  have hf : IsWeightedH1 μ U (hF.1.toLp F) (hF.2.1.toLp G) :=
    hF.congr hF.1.coeFn_toLp.symm hF.2.1.coeFn_toLp.symm
  have ha := (Variational.sobolevSubmodule μ U hU hμ).smul_mem a
    ((Variational.mem_iff μ U hU hμ _ _).mpr hf)
  have hr := (Variational.mem_iff μ U hU hμ _ _).mp ha
  simp only [Equiv.toFun_as_coe, ← WithLp.equiv_symm_apply, Equiv.apply_symm_apply] at hr
  apply hr.congr
  · filter_upwards [Lp.coeFn_smul a (hF.1.toLp F), hF.1.coeFn_toLp] with x hx hfx
    simpa only [Pi.smul_apply, smul_eq_mul, hfx] using hx
  · filter_upwards [Lp.coeFn_smul a (hF.2.1.toLp G), hF.2.1.coeFn_toLp] with x hx hgx
    simpa only [Pi.smul_apply, hgx] using hx

/-- Squaring a bounded Sobolev function, with its actual product gradient.
The scalar square is extended smoothly outside the bounded range before
applying the bounded-derivative chain rule. -/
theorem IsWeightedH1.sq_of_bound (hU : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) {F : E → ℝ} {G : E → E}
    (hF : IsWeightedH1 μ U F G) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂μ, |F x| ≤ M) :
    IsWeightedH1 μ U (fun x => F x ^ 2) (fun x => (2 * F x) • G x) := by
  let T : ℝ → ℝ := fun r => cutoffBump (M + 1) r * r ^ 2
  have hT : ContDiff ℝ ∞ T := (contDiff_cutoffBump _).mul (contDiff_id.pow 2)
  have hTc : HasCompactSupport T := by
    apply HasCompactSupport.intro (K := Icc (-(2 * (M + 1))) (2 * (M + 1))) isCompact_Icc
    intro r hr
    have hfar : 2 * (M + 1) ≤ |r| := by
      simp only [mem_Icc, not_and_or, not_le] at hr
      rcases hr with hr | hr
      · linarith [neg_le_abs r]
      · linarith [le_abs_self r]
    simp only [T, cutoffBump_eq_zero (by linarith : 0 < M + 1) hfar, zero_mul]
  obtain ⟨D, hD⟩ := (hT.continuous_deriv (by simp)).bounded_above_of_compact_support hTc.deriv
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have hchain := hF.comp_smooth hU hμ hT (by simp [T])
    (C := ⟨D, hD0⟩) (fun r => by exact_mod_cast hD r)
  apply hchain.congr
  · filter_upwards [hb] with x hx
    simp only [T, cutoffBump_eq_one (hx.trans (by linarith : M ≤ M + 1)), one_mul]
  · filter_upwards [hb] with x hx
    have hev : T =ᶠ[𝓝 (F x)] fun r => r ^ 2 := by
      filter_upwards [Ioo_mem_nhds
        (by linarith [abs_le.mp hx] : -(M + 1) < F x)
        (by linarith [abs_le.mp hx] : F x < M + 1)] with r hr
      simp only [T, cutoffBump_eq_one (abs_le.mpr ⟨hr.1.le, hr.2.le⟩), one_mul]
    rw [hev.deriv_eq]
    simp only [deriv_pow_field, Nat.cast_ofNat, show 2 - 1 = (1 : ℕ) from rfl, pow_one]

/-- The bounded Sobolev algebra product rule, on any bounded domain
and for any finite measure carried by that domain. -/
theorem IsWeightedH1.mul_of_bound (hU : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) {F H : E → ℝ} {G K : E → E}
    (hF : IsWeightedH1 μ U F G) (hH : IsWeightedH1 μ U H K)
    {M D : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hbF : ∀ᵐ x ∂μ, |F x| ≤ M) (hbH : ∀ᵐ x ∂μ, |H x| ≤ D) :
    IsWeightedH1 μ U (fun x => F x * H x)
      (fun x => F x • K x + H x • G x) := by
  have hs := hF.add hU hμ hH
  have hbs : ∀ᵐ x ∂μ, |F x + H x| ≤ M + D := by
    filter_upwards [hbF, hbH] with x hx hy
    exact (abs_add_le _ _).trans (add_le_add hx hy)
  have hsq := hs.sq_of_bound hU hμ (add_nonneg hM hD) hbs
  have hf2 := hF.sq_of_bound hU hμ hM hbF
  have hh2 := hH.sq_of_bound hU hμ hD hbH
  have hr := ((hsq.add hU hμ (hf2.const_smul hU hμ (-1))).add hU hμ
    (hh2.const_smul hU hμ (-1))).const_smul hU hμ (1 / 2)
  apply hr.congr
  · exact Eventually.of_forall fun x => by dsimp only; ring
  · exact Eventually.of_forall fun x => by dsimp only; module

end Riesz1.WeightedSobolev

end
