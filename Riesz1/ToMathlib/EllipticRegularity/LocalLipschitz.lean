/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.LipschitzMultipliers

/-!
# Local Lipschitz multiplication of weak derivatives

Interior localization extends the global L² multiplier rule to local L²
representatives. All statements use the weak-derivative predicate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff NNReal

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace Internal

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- One compact factor suffices for a product of real Lipschitz functions
to be Lipschitz. The other factor may be unbounded. -/
theorem exists_lipschitzWith_mul_one_compact {b q : E → ℝ} {B Q : ℝ≥0}
    (hb : LipschitzWith B b) (hq : LipschitzWith Q q) (hbc : HasCompactSupport b) :
    ∃ C : ℝ≥0, LipschitzWith C (fun x => b x * q x) := by
  obtain ⟨M, hM⟩ := hbc.exists_bound_of_continuous hb.continuous
  obtain ⟨L, hL⟩ := hbc.exists_bound_of_continuousOn hq.continuous.continuousOn
  let m : ℝ≥0 := ⟨|M|, abs_nonneg M⟩
  let l : ℝ≥0 := ⟨|L|, abs_nonneg L⟩
  have hm (x : E) : ‖b x‖ ≤ (m : ℝ) := (hM x).trans (le_abs_self M)
  have hl (x : E) (hx : b x ≠ 0) : ‖q x‖ ≤ (l : ℝ) :=
    (hL x (subset_tsupport b hx)).trans (le_abs_self L)
  have hbound (x y : E) (hx : b x ≠ 0) :
      ‖b x * q x - b y * q y‖ ≤ ((m * Q + B * l : ℝ≥0) : ℝ) * ‖x - y‖ := by
    calc
      ‖b x * q x - b y * q y‖ =
          ‖(b x - b y) * q x + b y * (q x - q y)‖ := by congr 1; ring
      _ ≤ ‖(b x - b y) * q x‖ + ‖b y * (q x - q y)‖ := norm_add_le _ _
      _ = ‖b x - b y‖ * ‖q x‖ + ‖b y‖ * ‖q x - q y‖ := by rw [norm_mul, norm_mul]
      _ ≤ ((B : ℝ) * ‖x - y‖) * (l : ℝ) + (m : ℝ) * ((Q : ℝ) * ‖x - y‖) := by
        gcongr
        · exact hb.norm_sub_le x y
        · exact hl x hx
        · exact hm y
        · exact hq.norm_sub_le x y
      _ = ((m * Q + B * l : ℝ≥0) : ℝ) * ‖x - y‖ := by push_cast; ring
  refine ⟨m * Q + B * l, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  simp only [dist_eq_norm]
  by_cases hx : b x = 0
  · by_cases hy : b y = 0
    · simp only [hx, hy, zero_mul, sub_self, norm_zero]
      positivity
    · simpa only [norm_sub_rev] using hbound y x hy
  · exact hbound x y hx

/-- Local L² and compact interior support imply global L². -/
theorem memLp_of_local_compact_interior {F : Type*} [NormedAddCommGroup F]
    {U : Set E} {f : E → F} (hf : LocallySquareIntegrableOn U f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) : MemLp f 2 volume := by
  have h := (memLp_indicator_iff_restrict hfc.measurableSet.nullMeasurableSet).mpr
    (hf _ hfc hfU)
  rwa [indicator_eq_self.mpr (subset_tsupport f)] at h

/-- A weak derivative with compact interior support extends to the whole
ambient space. The zero extension is already the given representative. -/
theorem weakDerivative_univ_of_compact {U : Set E} (hU : IsOpen U)
    {u g : E → ℂ} {v : E} (hd : HasWeakDirectionalDerivativeOn U u g v)
    (huL : MemLp u 2 volume) (hgL : MemLp g 2 volume)
    (huc : HasCompactSupport u) (hgc : HasCompactSupport g)
    (huU : tsupport u ⊆ U) (hgU : tsupport g ⊆ U) :
    HasWeakDirectionalDerivativeOn univ u g v := by
  obtain ⟨V, b, hVo, hKV, _, hb, hbc, hbU, hb1⟩ :=
    exists_smooth_interior_cutoff hU (huc.union hgc) (union_subset huU hgU)
  refine ⟨(huL.locallyIntegrable (by norm_num)).locallyIntegrableOn univ,
    (hgL.locallyIntegrable (by norm_num)).locallyIntegrableOn univ, ?_⟩
  intro φ hφ hφc _
  have he := hd.2.2 (fun x => φ x * b x) (hφ.mul hb) hφc.mul_right
    (tsupport_mul_subset_right.trans hbU)
  have hval (x : E) : (φ x * b x) • g x = φ x • g x := by
    by_cases hx : x ∈ tsupport g
    · rw [hb1 x (hKV (Or.inr hx)), mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hx, smul_zero, smul_zero]
  have hder (x : E) : fderiv ℝ (fun y => φ y * b y) x v • u x =
      fderiv ℝ φ x v • u x := by
    by_cases hx : x ∈ tsupport u
    · have hv : x ∈ V := hKV (Or.inl hx)
      have hl : (fun y => φ y * b y) =ᶠ[nhds x] φ := by
        filter_upwards [hVo.mem_nhds hv] with y hy
        rw [hb1 y hy, mul_one]
      rw [hl.fderiv_eq]
    · rw [image_eq_zero_of_notMem_tsupport hx, smul_zero, smul_zero]
  simpa only [hval, hder] using he

/-- Multiplying a locally L² weak derivative by an interior smooth
cutoff gives global L² weak representatives, with their product rule. -/
theorem smooth_localization_weak {U : Set E} (hU : IsOpen U)
    {u g : E → ℂ} {v : E} (hd : HasWeakDirectionalDerivativeOn U u g v)
    (hu : LocallySquareIntegrableOn U u) (hg : LocallySquareIntegrableOn U g)
    {b : E → ℝ} (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ U) :
    MemLp (fun x => b x • u x) 2 volume ∧
      MemLp (fun x => fderiv ℝ b x v • u x + b x • g x) 2 volume ∧
      HasWeakDirectionalDerivativeOn univ (fun x => b x • u x)
        (fun x => fderiv ℝ b x v • u x + b x • g x) v := by
  have hdb : Continuous (fun x => fderiv ℝ b x v) :=
    (hb.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hqU : tsupport (fun x => b x • u x) ⊆ U :=
    (tsupport_smul_subset_left b u).trans hbU
  have hrU : tsupport (fun x => fderiv ℝ b x v • u x + b x • g x) ⊆ U :=
    (tsupport_add _ _).trans (union_subset
      ((tsupport_smul_subset_left _ u).trans ((tsupport_fderiv_apply_subset ℝ v).trans hbU))
      ((tsupport_smul_subset_left b g).trans hbU))
  have hqL := hu.smul_continuousOn hb.continuous.continuousOn
  have hrL : LocallySquareIntegrableOn U
      (fun x => fderiv ℝ b x v • u x + b x • g x) := by
    intro K hK hKU
    exact (hu.smul_continuousOn hdb.continuousOn K hK hKU).add
      (hg.smul_continuousOn hb.continuous.continuousOn K hK hKU)
  have hqc : HasCompactSupport (fun x => b x • u x) := hbc.smul_right
  have hrc : HasCompactSupport (fun x => fderiv ℝ b x v • u x + b x • g x) :=
    ((hbc.fderiv_apply ℝ v).smul_right).add hbc.smul_right
  have hq := memLp_of_local_compact_interior hqL hqc hqU
  have hr := memLp_of_local_compact_interior hrL hrc hrU
  exact ⟨hq, hr, weakDerivative_univ_of_compact hU (hd.smul_smooth hU hb)
    hq hr hqc hrc hqU hrU⟩

end Internal

/-- Local L² weak derivatives may be tested against compactly supported
interior Lipschitz functions. Both integrals are integrable. -/
theorem HasWeakDirectionalDerivativeOn.test_lipschitz {U : Set E} (hU : IsOpen U)
    {u g : E → ℂ} {v : E} (hd : HasWeakDirectionalDerivativeOn U u g v)
    (hu : LocallySquareIntegrableOn U u) (hg : LocallySquareIntegrableOn U g)
    {b : E → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ U) :
    Integrable (fun x => b x • g x) ∧
      Integrable (fun x => fderiv ℝ b x v • u x) ∧
      (∫ x, b x • g x) = -∫ x, fderiv ℝ b x v • u x := by
  obtain ⟨V, χ, hVo, hbV, _, hχ, hχc, hχU, hχ1⟩ :=
    Internal.exists_smooth_interior_cutoff hU hbc hbU
  obtain ⟨hqL, hrL, hqr⟩ := Internal.smooth_localization_weak hU hd hu hg hχ hχc hχU
  have hqc : HasCompactSupport (fun x => χ x • u x) := hχc.smul_right
  have hrc : HasCompactSupport (fun x => fderiv ℝ χ x v • u x + χ x • g x) :=
    ((hχc.fderiv_apply ℝ v).smul_right).add hχc.smul_right
  have ht := Internal.tempered_derivative_of_compact_weak hqL hrL hqr hqc hrc
  obtain ⟨hI, hJ, he⟩ := Internal.integral_lipschitz_test_tempered ht hb hbc
  have hder (x : E) (hx : x ∈ V) : fderiv ℝ χ x = 0 := by
    have heq : χ =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
      filter_upwards [hVo.mem_nhds hx] with y hy
      exact hχ1 y hy
    rw [heq.fderiv_eq, fderiv_const_apply]
  have hval : (fun x => b x • (hrL.toLp _ : E → ℂ) x) =ᵐ[volume]
      (fun x => b x • g x) := by
    filter_upwards [hrL.coeFn_toLp] with x hx
    rw [hx]
    by_cases hxb : x ∈ tsupport b
    · rw [hder x (hbV hxb), zero_apply, zero_smul, hχ1 x (hbV hxb), one_smul, zero_add]
    · rw [image_eq_zero_of_notMem_tsupport hxb, zero_smul, zero_smul]
  have hgrad : (fun x => fderiv ℝ b x v • (hqL.toLp _ : E → ℂ) x) =ᵐ[volume]
      (fun x => fderiv ℝ b x v • u x) := by
    filter_upwards [hqL.coeFn_toLp] with x hx
    rw [hx]
    by_cases hxb : x ∈ tsupport b
    · rw [hχ1 x (hbV hxb), one_smul]
    · rw [fderiv_of_notMem_tsupport ℝ hxb, zero_apply, zero_smul, zero_smul]
  exact ⟨hI.congr hval, hJ.congr hgrad,
    (integral_congr_ae hval).symm.trans (he.trans (congrArg Neg.neg (integral_congr_ae hgrad)))⟩

/-- A Lipschitz multiplier obeys the local L² weak product rule. The
multiplier need not have compact support on the Euclidean cover. -/
theorem HasWeakDirectionalDerivativeOn.smul_lipschitz {U : Set E} (hU : IsOpen U)
    {u g : E → ℂ} {v : E} (hd : HasWeakDirectionalDerivativeOn U u g v)
    (hu : LocallySquareIntegrableOn U u) (hg : LocallySquareIntegrableOn U g)
    {b : E → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b) :
    LocallySquareIntegrableOn U (fun x => b x • u x) ∧
      LocallySquareIntegrableOn U (fun x => fderiv ℝ b x v • u x + b x • g x) ∧
      HasWeakDirectionalDerivativeOn U (fun x => b x • u x)
        (fun x => fderiv ℝ b x v • u x + b x • g x) v := by
  have haL := hu.smul_continuousOn hb.continuous.continuousOn
  have hkL : LocallySquareIntegrableOn U (fun x => fderiv ℝ b x v • u x) := by
    intro K hK hKU
    exact ((Internal.memLp_top_fderiv_lipschitz hb v).restrict K).smul (hu K hK hKU)
  have hlL := hg.smul_continuousOn hb.continuous.continuousOn
  have hrL : LocallySquareIntegrableOn U
      (fun x => fderiv ℝ b x v • u x + b x • g x) := by
    intro K hK hKU
    exact (hkL K hK hKU).add (hlL K hK hKU)
  refine ⟨haL, hrL, ⟨haL.locallyIntegrableOn hU, hrL.locallyIntegrableOn hU, ?_⟩⟩
  intro φ hφ hφc hφU
  obtain ⟨D, hD⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by simp)
  obtain ⟨B, hB⟩ := Internal.exists_lipschitzWith_mul_one_compact hD hb hφc
  have hi := (hd.test_lipschitz hU hu hg hB hφc.mul_right
    (tsupport_mul_subset_left.trans hφU)).2.2
  have hA := integrable_smul_of_compact_interior (haL.locallyIntegrableOn hU)
    ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    (hφc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hφU)
  have hK := integrable_smul_of_compact_interior (hkL.locallyIntegrableOn hU)
    hφ.continuous hφc hφU
  have hL := integrable_smul_of_compact_interior (hlL.locallyIntegrableOn hU)
    hφ.continuous hφc hφU
  have he : (fun x => fderiv ℝ (fun y => φ y * b y) x v • u x) =ᵐ[volume]
      (fun x => fderiv ℝ φ x v • (b x • u x) + φ x • (fderiv ℝ b x v • u x)) := by
    filter_upwards [hb.ae_differentiableAt (μ := volume)] with x hx
    rw [fderiv_fun_mul (hφ.differentiable (by norm_num) x) hx]
    simp only [add_apply, smul_apply, smul_eq_mul]
    module
  rw [integral_congr_ae he, integral_add hA hK] at hi
  simp only [mul_smul] at hi
  simp only [smul_add]
  rw [integral_add hK hL, hi]
  abel

end Riesz1
