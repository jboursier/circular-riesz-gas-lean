/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.WeakTesting
public import Riesz1.ToMathlib.EllipticRegularity.LipschitzDerivatives
public import Riesz1.ToMathlib.EllipticRegularity.LinearMaps
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Lipschitz tests and multipliers for L² weak derivatives

Tools for the compact Lipschitz energy identity in the interior H² regularity argument.
All weak derivatives use the original part 1 predicate.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap LineDeriv ContDiff ComplexInnerProductSpace NNReal

namespace Riesz1.Internal

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A compactly supported locally L² function is globally L². -/
theorem memLp_of_local_compact {F : Type*} [NormedAddCommGroup F]
    {u : E → F} (hu : LocallySquareIntegrableOn univ u)
    (huc : HasCompactSupport u) : MemLp u 2 volume := by
  have h := (memLp_indicator_iff_restrict huc.measurableSet.nullMeasurableSet).mpr
    (hu _ huc (subset_univ _))
  rwa [indicator_eq_self.mpr (subset_tsupport u)] at h

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Compact Lipschitz real functions have a Lipschitz product. -/
theorem exists_lipschitzWith_mul_compact {b q : E → ℝ} {B Q : ℝ≥0}
    (hb : LipschitzWith B b) (hq : LipschitzWith Q q)
    (hbc : HasCompactSupport b) (hqc : HasCompactSupport q) :
    ∃ C : ℝ≥0, LipschitzWith C (fun x => b x * q x) := by
  obtain ⟨M, hM⟩ := hbc.exists_bound_of_continuous hb.continuous
  obtain ⟨L, hL⟩ := hqc.exists_bound_of_continuous hq.continuous
  let m : ℝ≥0 := ⟨|M|, abs_nonneg M⟩
  let l : ℝ≥0 := ⟨|L|, abs_nonneg L⟩
  refine ⟨m * Q + B * l, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hm (x : E) : ‖b x‖ ≤ (m : ℝ) := (hM x).trans (le_abs_self M)
  have hl (x : E) : ‖q x‖ ≤ (l : ℝ) := (hL x).trans (le_abs_self L)
  simp only [dist_eq_norm] at *
  calc
    ‖b x * q x - b y * q y‖ =
        ‖b x * (q x - q y) + (b x - b y) * q y‖ := by congr 1; ring
    _ ≤ ‖b x * (q x - q y)‖ + ‖(b x - b y) * q y‖ := norm_add_le _ _
    _ = ‖b x‖ * ‖q x - q y‖ + ‖b x - b y‖ * ‖q y‖ := by rw [norm_mul, norm_mul]
    _ ≤ (m : ℝ) * ((Q : ℝ) * ‖x - y‖) + ((B : ℝ) * ‖x - y‖) * (l : ℝ) := by
      gcongr
      · exact hm x
      · exact hq.norm_sub_le x y
      · exact hb.norm_sub_le x y
      · exact hl y
    _ = ((m * Q + B * l : ℝ≥0) : ℝ) * ‖x - y‖ := by push_cast; ring

/-- The almost everywhere derivative of a Lipschitz function is an
essentially bounded multiplier. -/
theorem memLp_top_fderiv_lipschitz {b : E → ℝ} {C : ℝ≥0}
    (hb : LipschitzWith C b) (v : E) :
    MemLp (fun x => fderiv ℝ b x v) ⊤ volume := by
  have he : (fun x => lineDeriv ℝ b x v) =ᵐ[volume] (fun x => fderiv ℝ b x v) := by
    filter_upwards [hb.ae_differentiableAt (μ := volume)] with x hx
    exact hx.lineDeriv_eq_fderiv
  exact (memLp_congr_ae he).mp (hb.memLp_lineDeriv (μ := volume) v)

/-- A real compact weak test defines an L² tempered derivative after
embedding its values in the complex numbers. -/
theorem tempered_derivative_of_compact_real_weak {q r : E → ℝ} {v : E}
    (hqL : MemLp q 2 volume) (hrL : MemLp r 2 volume)
    (hqr : HasWeakDirectionalDerivativeOn univ q r v)
    (hqc : HasCompactSupport q) (hrc : HasCompactSupport r) :
    ∂_{v} ((Complex.ofRealCLM.comp_memLp' hqL).toLp (fun x => (q x : ℂ)) : 𝓢'(E, ℂ)) =
      ((Complex.ofRealCLM.comp_memLp' hrL).toLp (fun x => (r x : ℂ)) : 𝓢'(E, ℂ)) := by
  have hweak : HasWeakDirectionalDerivativeOn univ
      (fun x => (q x : ℂ)) (fun x => (r x : ℂ)) v := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using hqr.map Complex.ofRealCLM
  have hqC : MemLp (fun x => (q x : ℂ)) 2 volume := Complex.ofRealCLM.comp_memLp' hqL
  have hrC : MemLp (fun x => (r x : ℂ)) 2 volume := Complex.ofRealCLM.comp_memLp' hrL
  exact tempered_derivative_of_compact_weak (u := fun x => (q x : ℂ))
    (g := fun x => (r x : ℂ)) hqC hrC hweak
    (hqc.comp_left (map_zero Complex.ofRealCLM))
    (hrc.comp_left (map_zero Complex.ofRealCLM))

/-- A real compact H¹ test may be paired with an L² tempered derivative.
Both displayed products are integrable. -/
theorem integral_real_test_tempered {u g : Lp ℂ 2 (volume : Measure E)} {v : E}
    (hu : ∂_{v} (u : 𝓢'(E, ℂ)) = (g : 𝓢'(E, ℂ)))
    {q r : E → ℝ} (hqL : MemLp q 2 volume) (hrL : MemLp r 2 volume)
    (hqr : HasWeakDirectionalDerivativeOn univ q r v)
    (hqc : HasCompactSupport q) (hrc : HasCompactSupport r) :
    Integrable (fun x => q x • g x) ∧ Integrable (fun x => r x • u x) ∧
    (∫ x, q x • g x) = -∫ x, r x • u x := by
  let a : Lp ℂ 2 (volume : Measure E) :=
    (Complex.ofRealCLM.comp_memLp' hqL).toLp (fun x => (q x : ℂ))
  let k : Lp ℂ 2 (volume : Measure E) :=
    (Complex.ofRealCLM.comp_memLp' hrL).toLp (fun x => (r x : ℂ))
  have ha : (a : E → ℂ) =ᵐ[volume] (fun x => (q x : ℂ)) := MemLp.coeFn_toLp _
  have hk : (k : E → ℂ) =ᵐ[volume] (fun x => (r x : ℂ)) := MemLp.coeFn_toLp _
  have hd : ∂_{v} (a : 𝓢'(E, ℂ)) = (k : 𝓢'(E, ℂ)) :=
    tempered_derivative_of_compact_real_weak hqL hrL hqr hqc hrc
  have hAg : (fun x => ⟪a x, g x⟫) =ᵐ[volume] (fun x => q x • g x) := by
    filter_upwards [ha] with x hx
    simp only [hx, RCLike.inner_apply, Complex.conj_ofReal, Complex.real_smul]
    ring
  have hKu : (fun x => ⟪k x, u x⟫) =ᵐ[volume] (fun x => r x • u x) := by
    filter_upwards [hk] with x hx
    simp only [hx, RCLike.inner_apply, Complex.conj_ofReal, Complex.real_smul]
    ring
  refine ⟨(L2.integrable_inner a g).congr hAg,
    (L2.integrable_inner k u).congr hKu, ?_⟩
  have hp := inner_tempered_derivative hd hu
  rw [L2.inner_def, L2.inner_def, integral_congr_ae hKu, integral_congr_ae hAg] at hp
  simpa only [neg_neg] using congrArg Neg.neg hp.symm

/-- Compact Lipschitz tests are valid against an L² weak derivative. -/
theorem integral_lipschitz_test_tempered {u g : Lp ℂ 2 (volume : Measure E)} {v : E}
    (hu : ∂_{v} (u : 𝓢'(E, ℂ)) = (g : 𝓢'(E, ℂ)))
    {q : E → ℝ} {C : ℝ≥0} (hq : LipschitzWith C q) (hqc : HasCompactSupport q) :
    Integrable (fun x => q x • g x) ∧
    Integrable (fun x => fderiv ℝ q x v • u x) ∧
    (∫ x, q x • g x) = -∫ x, fderiv ℝ q x v • u x := by
  have hqL : MemLp q 2 volume := hq.continuous.memLp_of_hasCompactSupport hqc
  have hrL : MemLp (fun x => fderiv ℝ q x v) 2 volume :=
    memLp_of_local_compact (locallySquareIntegrableOn_fderiv_of_lipschitz hq univ v)
      (hqc.fderiv_apply ℝ v)
  exact integral_real_test_tempered hu hqL hrL
    (hasWeakDirectionalDerivativeOn_of_lipschitz hq univ v) hqc (hqc.fderiv_apply ℝ v)

/-- A compact Lipschitz multiplier obeys the product rule for an L²
function with an L² distributional directional derivative. -/
theorem lipschitz_mul_tempered_weak {u g : Lp ℂ 2 (volume : Measure E)} {v : E}
    (hu : ∂_{v} (u : 𝓢'(E, ℂ)) = (g : 𝓢'(E, ℂ)))
    {b : E → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b) (hbc : HasCompactSupport b) :
    MemLp (fun x => b x • u x) 2 volume ∧
    MemLp (fun x => fderiv ℝ b x v • u x + b x • g x) 2 volume ∧
    HasWeakDirectionalDerivativeOn univ (fun x => b x • u x)
      (fun x => fderiv ℝ b x v • u x + b x • g x) v := by
  have hbL : MemLp b ⊤ volume := hb.continuous.memLp_top_of_hasCompactSupport hbc volume
  have hdL := memLp_top_fderiv_lipschitz hb v
  have haL : MemLp (fun x => b x • u x) 2 volume := hbL.smul (Lp.memLp u)
  have hkL : MemLp (fun x => fderiv ℝ b x v • u x) 2 volume := hdL.smul (Lp.memLp u)
  have hlL : MemLp (fun x => b x • g x) 2 volume := hbL.smul (Lp.memLp g)
  refine ⟨haL, hkL.add hlL, ⟨?_, ?_, ?_⟩⟩
  · exact (haL.locallyIntegrable (by norm_num)).locallyIntegrableOn univ
  · exact ((hkL.add hlL).locallyIntegrable (by norm_num)).locallyIntegrableOn univ
  · intro φ hφ hφc _
    obtain ⟨D, hD⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by simp)
    obtain ⟨B, hB⟩ := exists_lipschitzWith_mul_compact hD hb hφc hbc
    have hi := (integral_lipschitz_test_tempered hu hB hφc.mul_right).2.2
    have hA := integrable_smul_of_compact_interior
      ((haL.locallyIntegrable (by norm_num)).locallyIntegrableOn univ)
      ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      (hφc.fderiv_apply ℝ v) (subset_univ _)
    have hK := integrable_smul_of_compact_interior
      ((hkL.locallyIntegrable (by norm_num)).locallyIntegrableOn univ)
      hφ.continuous hφc (subset_univ _)
    have hL := integrable_smul_of_compact_interior
      ((hlL.locallyIntegrable (by norm_num)).locallyIntegrableOn univ)
      hφ.continuous hφc (subset_univ _)
    have he : (fun x => fderiv ℝ (fun y => φ y * b y) x v • u x) =ᵐ[volume]
        (fun x => fderiv ℝ φ x v • (b x • u x) + φ x • (fderiv ℝ b x v • u x)) := by
      filter_upwards [hb.ae_differentiableAt (μ := volume)] with x hx
      rw [fderiv_fun_mul (hφ.differentiable (by norm_num) x) hx]
      simp only [add_apply, smul_apply, smul_eq_mul]
      module
    rw [integral_congr_ae he, integral_add hA hK] at hi
    have hv : (∫ x, (φ x * b x) • g x) = ∫ x, φ x • (b x • g x) := by
      simp only [mul_smul]
    rw [hv] at hi
    simp only [smul_add]
    rw [integral_add hK hL, hi]
    abel

end Riesz1.Internal
