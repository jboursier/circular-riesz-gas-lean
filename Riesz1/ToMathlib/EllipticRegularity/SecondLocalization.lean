/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.FirstDerivatives

/-!
# The second elliptic localization

For the interior H² regularity argument, the divergence terms in the cutoff Laplacian
are L²: apply the first localization to each derivative of the cutoff.
This avoids assuming a weak gradient in the input.
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

/-- The localized Laplacian is L², using the equation and the first
localization for the derivatives of the cutoff. -/
theorem schrodinger_cutoff_laplacian_memSobolev_zero {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ)
    (u : Lp F 2 (volume : Measure E))
    (hu : IsDistributionalSchrodingerSolution U W lam (u : E → F))
    {b : E → ℝ} (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ U) :
    MemSobolev 0 2 (Δ (smulLeftCLM F (fun x => (b x : ℂ)) (u : 𝓢'(E, F)))) := by
  classical
  have hBc := hbc.comp_left (map_zero Complex.ofRealCLM)
  have hBs := Complex.ofRealCLM.contDiff.comp hb
  let B : 𝓢(E, ℂ) := hBc.toSchwartzMap hBs
  have hd (v : E) :
      (∂_{v} B : 𝓢(E, ℂ)) = fun x => (fderiv ℝ b x v : ℂ) := by
    funext x
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change fderiv ℝ (Complex.ofRealCLM ∘ b) x v = _
    rw [fderiv_comp x Complex.ofRealCLM.differentiableAt
      (hb.differentiable (by norm_num) x), Complex.ofRealCLM.fderiv]
    rfl
  have hforce : MemSobolev 0 2 (smulLeftCLM F B (Δ (u : 𝓢'(E, F)))) := by
    change MemSobolev 0 2 (smulLeftCLM F (fun x => (b x : ℂ)) (Δ (u : 𝓢'(E, F))))
    rw [schrodinger_cutoff_laplacian hU hW lam u hu hb hbc hbU]
    have hqs := WeightedSobolev.contDiff_cutoff_mul hU hb hbU
      (hW.add (contDiffOn_const (c := lam)))
    have hqc := hbc.mul_right (f' := fun x => W x + lam)
    exact memSobolev_zero_smul_schwartz
      ((hqc.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
        (Complex.ofRealCLM.contDiff.comp hqs)) u
  have hsum : MemSobolev 0 2
      (∑ i, (∂_{stdOrthonormalBasis ℝ E i}
        (smulLeftCLM F (∂_{stdOrthonormalBasis ℝ E i} B : 𝓢(E, ℂ)) u) +
        ∂_{stdOrthonormalBasis ℝ E i}
        (smulLeftCLM F (∂_{stdOrthonormalBasis ℝ E i} B : 𝓢(E, ℂ)) u))) := by
    apply Finset.sum_induction
    · intro a b ha hb
      exact ha.add hb
    · exact memSobolev_fun_zero E F 0 2
    · intro i _
      let v := stdOrthonormalBasis ℝ E i
      have hs : ContDiff ℝ ∞ (fun x => fderiv ℝ b x v) :=
        (hb.fderiv_right (by simp)).clm_apply contDiff_const
      have h1 := schrodinger_cutoff_memSobolev_one hU hW lam u hu hs
        (hbc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hbU)
      have hz : MemSobolev 0 2
          (∂_{v} (smulLeftCLM F (∂_{v} B : 𝓢(E, ℂ)) u)) := by
        rw [hd]
        simpa using h1.lineDerivOp (m := v)
      exact hz.add hz
  change MemSobolev 0 2 (Δ (smulLeftCLM F B (u : 𝓢'(E, F))))
  rw [tempered_laplacian_smul_divergence]
  exact (hforce.add hsum).sub (memSobolev_zero_smul_schwartz (Δ B) u)

/-- Every smooth interior cutoff of a distributional solution is H² in
the global Fourier encoding. This is the second localization in L3232. -/
theorem schrodinger_cutoff_memSobolev_two {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ)
    (u : Lp F 2 (volume : Measure E))
    (hu : IsDistributionalSchrodingerSolution U W lam (u : E → F))
    {b : E → ℝ} (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ U) :
    MemSobolev 2 2 (smulLeftCLM F (fun x => (b x : ℂ)) (u : 𝓢'(E, F))) := by
  apply memSobolev_two_of_laplacian
  · exact (schrodinger_cutoff_memSobolev_one hU hW lam u hu hb hbc hbU).mono
      (by norm_num)
  · exact schrodinger_cutoff_laplacian_memSobolev_zero hU hW lam u hu hb hbc hbU

/-- In the original weak-derivative encoding, every smooth interior
cutoff has square integrable first and second weak derivatives. -/
theorem schrodinger_cutoff_isLocalH2 {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ) {u : E → F}
    (huL : MemLp u 2 (volume.restrict U))
    (hu : IsDistributionalSchrodingerSolution U W lam u)
    {b : E → ℝ} (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ U) :
    IsLocalH2 univ (fun x => b x • u x) := by
  have hz : MemLp (U.indicator u) 2 volume :=
    (memLp_indicator_iff_restrict hU.measurableSet.nullMeasurableSet).mpr huL
  let w : Lp F 2 (volume : Measure E) := hz.toLp (U.indicator u)
  have hwu : (w : E → F) =ᵐ[volume.restrict U] u := by
    filter_upwards [ae_restrict_of_ae hz.coeFn_toLp,
      ae_restrict_mem hU.measurableSet] with x hx hxU
    exact hx.trans (indicator_of_mem hxU u)
  have hw := hu.congr hU hwu.symm
  have hΔ := schrodinger_cutoff_laplacian_memSobolev_zero hU hW lam w hw hb hbc hbU
  have hbL : MemLp b ⊤ volume := hb.continuous.memLp_top_of_hasCompactSupport hbc volume
  have haL : MemLp (fun x => b x • w x) 2 volume := hbL.smul (Lp.memLp w)
  let a : Lp F 2 (volume : Measure E) := haL.toLp (fun x => b x • w x)
  have hB : Function.HasTemperateGrowth (fun x => (b x : ℂ)) :=
    ((hbc.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hb)).hasTemperateGrowth
  have hTa : smulLeftCLM F (fun x => (b x : ℂ)) (w : 𝓢'(E, F)) =
      (a : 𝓢'(E, F)) := by
    ext ψ
    rw [smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
      Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [haL.coeFn_toLp] with x hx
    rw [hx, SchwartzMap.smulLeftCLM_apply_apply hB]
    module
  obtain ⟨f, hf⟩ := memSobolev_zero_iff.mp hΔ
  have ha := isLocalH2_of_tempered_laplacian a f (by rwa [hTa] at hf) univ
  apply ha.congr isOpen_univ
  apply ae_restrict_of_ae
  filter_upwards [haL.coeFn_toLp, (ae_restrict_iff' hU.measurableSet).mp hwu] with x hx hwx
  rw [hx]
  by_cases hxU : x ∈ U
  · rw [hwx hxU]
  · have hb0 := image_eq_zero_of_notMem_tsupport (fun h => hxU (hbU h))
    simp only [hb0, zero_smul]

end Riesz1.Internal
