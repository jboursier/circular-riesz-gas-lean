/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.WeakPairing
public import Riesz1.ToMathlib.EllipticRegularity.LocalH2

/-!
# Compact weak derivatives as tempered derivatives

The real test predicate used for nonsmooth testing determines the
full complex derivative. For compactly supported representatives this
also gives the tempered derivative and hence the L² pairing identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap LineDeriv ContDiff ComplexInnerProductSpace

namespace Riesz1

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Real weak tests imply the complex compact test identity. -/
theorem HasWeakDirectionalDerivativeOn.test_complex {U : Set E}
    {u g : E → F} {v : E} (hu : HasWeakDirectionalDerivativeOn U u g v)
    {ψ : E → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) :
    (∫ x, ψ x • g x) = - ∫ x, fderiv ℝ ψ x v • u x := by
  let r := Complex.reCLM ∘ ψ
  let t := Complex.imCLM ∘ ψ
  have hr : ContDiff ℝ ∞ r := Complex.reCLM.contDiff.comp hψ
  have ht : ContDiff ℝ ∞ t := Complex.imCLM.contDiff.comp hψ
  have hrc : HasCompactSupport r := hψc.comp_left (map_zero _)
  have htc : HasCompactSupport t := hψc.comp_left (map_zero _)
  have hrU : tsupport r ⊆ U := (tsupport_comp_subset (map_zero _) ψ).trans hψU
  have htU : tsupport t ⊆ U := (tsupport_comp_subset (map_zero _) ψ).trans hψU
  have hA := integrable_smul_of_compact_interior hu.2.1 hr.continuous hrc hrU
  have hB := integrable_smul_of_compact_interior hu.2.1 ht.continuous htc htU
  have hC := integrable_smul_of_compact_interior hu.1
    ((hr.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    (hrc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hrU)
  have hD := integrable_smul_of_compact_interior hu.1
    ((ht.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    (htc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans htU)
  have hsplit (z : ℂ) (a : F) : z • a = z.re • a + Complex.I • (z.im • a) := by
    conv_lhs => rw [← Complex.re_add_im z]
    simp only [add_smul, mul_smul]
    rw [smul_comm (z.im : ℂ) Complex.I]
    rfl
  have hder (x : E) : fderiv ℝ ψ x v • u x =
      fderiv ℝ r x v • u x + Complex.I • (fderiv ℝ t x v • u x) := by
    have hr' : fderiv ℝ r x v = (fderiv ℝ ψ x v).re := by
      rw [show r = Complex.reCLM ∘ ψ from rfl,
        fderiv_comp x Complex.reCLM.differentiableAt
          (hψ.differentiable (by norm_num) x), Complex.reCLM.fderiv]
      rfl
    have ht' : fderiv ℝ t x v = (fderiv ℝ ψ x v).im := by
      rw [show t = Complex.imCLM ∘ ψ from rfl,
        fderiv_comp x Complex.imCLM.differentiableAt
          (hψ.differentiable (by norm_num) x), Complex.imCLM.fderiv]
      rfl
    rw [hr', ht']
    exact hsplit _ _
  have hval (x : E) : ψ x • g x = r x • g x + Complex.I • (t x • g x) :=
    hsplit _ _
  have hB' : Integrable (fun x => Complex.I • (t x • g x)) := hB.smul Complex.I
  have hD' : Integrable (fun x => Complex.I • (fderiv ℝ t x v • u x)) := hD.smul Complex.I
  simp_rw [hval, hder]
  rw [integral_add hA hB', integral_add hC hD',
    integral_smul, integral_smul, hu.2.2 r hr hrc hrU, hu.2.2 t ht htc htU,
    smul_neg, neg_add_rev]
  abel

namespace Internal

/-- Compact weak derivatives of L² representatives agree with the
tempered derivative. Compactness is used only to enlarge the test class. -/
theorem tempered_derivative_of_compact_weak {u g : E → F} {v : E}
    (huL : MemLp u 2 volume) (hgL : MemLp g 2 volume)
    (hu : HasWeakDirectionalDerivativeOn univ u g v)
    (huc : HasCompactSupport u) (hgc : HasCompactSupport g) :
    ∂_{v} (huL.toLp u : 𝓢'(E, F)) = (hgL.toLp g : 𝓢'(E, F)) := by
  obtain ⟨V, b, hVo, hKV, _, hb, hbc, _, hb1⟩ :=
    exists_smooth_interior_cutoff isOpen_univ (huc.union hgc) (subset_univ _)
  ext ψ
  let φ : E → ℂ := fun x => (b x : ℂ) * ψ x
  have hφ : ContDiff ℝ ∞ φ := (Complex.ofRealCLM.contDiff.comp hb).mul (ψ.smooth ⊤)
  have hφc : HasCompactSupport φ := (hbc.comp_left (map_zero Complex.ofRealCLM)).mul_right
  have he := hu.test_complex hφ hφc (subset_univ _)
  have hg (x : E) : φ x • g x = ψ x • g x := by
    by_cases hx : x ∈ tsupport g
    · simp only [φ, hb1 x (hKV (Or.inr hx)), Complex.ofReal_one, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, smul_zero, smul_zero]
  have hd (x : E) : fderiv ℝ φ x v • u x = (∂_{v} ψ) x • u x := by
    by_cases hx : x ∈ tsupport u
    · have hv : x ∈ V := hKV (Or.inl hx)
      have hl : φ =ᶠ[nhds x] (ψ : E → ℂ) := by
        filter_upwards [hVo.mem_nhds hv] with y hy
        simp only [φ, hb1 y hy, Complex.ofReal_one, one_mul]
      rw [hl.fderiv_eq, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    · rw [image_eq_zero_of_notMem_tsupport hx, smul_zero, smul_zero]
  simp_rw [hg, hd] at he
  rw [TemperedDistribution.lineDerivOp_apply_apply,
    Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
  have ha : (∫ x, (-∂_{v} ψ) x • (huL.toLp u) x) =
      -(∫ x, (∂_{v} ψ) x • u x) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [huL.coeFn_toLp] with x hx
    simp only [hx, neg_apply, neg_smul]
  rw [ha, ← he]
  apply integral_congr_ae
  filter_upwards [hgL.coeFn_toLp] with x hx
  rw [hx]

omit [CompleteSpace F] in
/-- L² representatives have integrable pointwise inner product. -/
theorem integrable_inner_of_memLp {a c : E → F}
    (ha : MemLp a 2 volume) (hc : MemLp c 2 volume) :
    Integrable (fun x => ⟪a x, c x⟫) := by
  refine (L2.integrable_inner (ha.toLp a) (hc.toLp c)).congr ?_
  filter_upwards [ha.coeFn_toLp, hc.coeFn_toLp] with x hx hy
  rw [hx, hy]

/-- Integration by parts with a compact H¹ weak test, with no smoothness
or Lipschitz assumption on either L² representative. -/
theorem integral_inner_tempered_compact_weak
    {u g : Lp F 2 (volume : Measure E)} {v : E}
    (hu : ∂_{v} (u : 𝓢'(E, F)) = (g : 𝓢'(E, F)))
    {q r : E → F} (hqL : MemLp q 2 volume) (hrL : MemLp r 2 volume)
    (hqr : HasWeakDirectionalDerivativeOn univ q r v)
    (hqc : HasCompactSupport q) (hrc : HasCompactSupport r) :
    (∫ x, ⟪q x, g x⟫) = -∫ x, ⟪r x, u x⟫ := by
  have hd := tempered_derivative_of_compact_weak hqL hrL hqr hqc hrc
  have hp := inner_tempered_derivative hd hu
  have hAg : (fun x => ⟪(hqL.toLp q) x, g x⟫) =ᵐ[volume]
      (fun x => ⟪q x, g x⟫) := by
    filter_upwards [hqL.coeFn_toLp] with x hx
    rw [hx]
  have hKu : (fun x => ⟪(hrL.toLp r) x, u x⟫) =ᵐ[volume]
      (fun x => ⟪r x, u x⟫) := by
    filter_upwards [hrL.coeFn_toLp] with x hx
    rw [hx]
  rw [L2.inner_def, L2.inner_def, integral_congr_ae hKu, integral_congr_ae hAg] at hp
  simpa only [neg_neg] using congrArg Neg.neg hp.symm

end Internal
end Riesz1
