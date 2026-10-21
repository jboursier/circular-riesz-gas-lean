/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.WeakDerivatives
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Multiplication and uniqueness for explicit weak derivatives

These are localization tools for the interior H² regularity argument. All derivatives
are expressed with the predicates introduced in `WeakDerivatives`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Local integrability suffices for integration against a continuous
compactly supported interior scalar multiplier. -/
theorem integrable_smul_of_compact_interior {U : Set E} {u : E → F}
    (hu : LocallyIntegrableOn u U) {b : E → ℝ} (hb : Continuous b)
    (hbc : HasCompactSupport b) (hbU : tsupport b ⊆ U) :
    Integrable (fun x => b x • u x) := by
  refine (integrableOn_iff_integrable_of_support_subset (s := tsupport b) ?_).mp ?_
  · intro x hx
    by_contra hxb
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hxb])
  exact (hu.integrableOn_compact_subset hbU hbc).continuousOn_smul hb.continuousOn hbc

omit [CompleteSpace F] in
/-- A smooth multiplier obeys the weak first derivative product rule.
No classical differentiability of either weak representative is assumed. -/
theorem HasWeakDirectionalDerivativeOn.smul_smooth {U : Set E} (hU : IsOpen U)
    {u g : E → F} {v : E} (hu : HasWeakDirectionalDerivativeOn U u g v)
    {b : E → ℝ} (hb : ContDiff ℝ ∞ b) :
    HasWeakDirectionalDerivativeOn U (fun x => b x • u x)
      (fun x => (fderiv ℝ b x v) • u x + b x • g x) v := by
  have hdb : Continuous (fun x => fderiv ℝ b x v) :=
    (hb.continuous_fderiv (by norm_num)).clm_apply continuous_const
  refine ⟨hu.1.continuousOn_smul hU.isLocallyClosed hb.continuous.continuousOn,
    (hu.1.continuousOn_smul hU.isLocallyClosed hdb.continuousOn).add
      (hu.2.1.continuousOn_smul hU.isLocallyClosed hb.continuous.continuousOn), ?_⟩
  intro φ hφ hφc hφU
  have heq := hu.2.2 (fun x => φ x * b x) (hφ.mul hb) hφc.mul_right
    (tsupport_mul_subset_left.trans hφU)
  have hA : Integrable (fun x => (φ x * fderiv ℝ b x v) • u x) :=
    integrable_smul_of_compact_interior hu.1 (hφ.continuous.mul hdb)
      hφc.mul_right (tsupport_mul_subset_left.trans hφU)
  have hB : Integrable (fun x => (φ x * b x) • g x) :=
    integrable_smul_of_compact_interior hu.2.1 (hφ.continuous.mul hb.continuous)
      hφc.mul_right (tsupport_mul_subset_left.trans hφU)
  have hC : Integrable (fun x => (fderiv ℝ φ x v * b x) • u x) :=
    integrable_smul_of_compact_interior hu.1
      (((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hb.continuous)
      (hφc.fderiv_apply ℝ v).mul_right
      (tsupport_mul_subset_left.trans ((tsupport_fderiv_apply_subset ℝ v).trans hφU))
  have hp (x : E) : (fderiv ℝ (fun y => φ y * b y) x v) • u x =
      (fderiv ℝ φ x v * b x) • u x + (φ x * fderiv ℝ b x v) • u x := by
    rw [fderiv_fun_mul (hφ.differentiable (by norm_num) x)
      (hb.differentiable (by norm_num) x)]
    simp only [add_apply, smul_apply, smul_eq_mul, add_smul]
    rw [mul_comm (b x)]
    exact add_comm _ _
  simp_rw [hp] at heq
  rw [integral_add hC hA] at heq
  simp only [smul_add, ← mul_smul]
  rw [integral_add hA hB, heq]
  abel

/-- Weak derivative representatives are unique almost everywhere in an
open domain, including for complex valued functions tested by real tests. -/
theorem HasWeakDirectionalDerivativeOn.unique {U : Set E} (hU : IsOpen U)
    {u g h : E → F} {v : E} (hg : HasWeakDirectionalDerivativeOn U u g v)
    (hh : HasWeakDirectionalDerivativeOn U u h v) :
    g =ᵐ[volume.restrict U] h := by
  have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hg.2.1.sub hh.2.1) (fun φ hφ hφc hφU => ?_)
  · exact (ae_restrict_iff' hU.measurableSet).mpr
      (hz.mono (fun x hx hxU => sub_eq_zero.mp (hx hxU)))
  · simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub
      (integrable_smul_of_compact_interior hg.2.1 hφ.continuous hφc hφU)
      (integrable_smul_of_compact_interior hh.2.1 hφ.continuous hφc hφU),
      hg.2.2 φ hφ hφc hφU, hh.2.2 φ hφ hφc hφU, sub_self]

end Riesz1
