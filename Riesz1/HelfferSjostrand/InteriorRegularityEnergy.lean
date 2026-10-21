/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.InteriorRegularity
public import Riesz1.ToMathlib.EllipticRegularity.LaplacianEnergy

/-!
# Interior cutoff energy for distributional Schrödinger solutions

The Euclidean compact Lipschitz energy assertion.
Weak gradient coordinates use the predicate `HasWeakDirectionalDerivativeOn`.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap LineDeriv Laplacian ContDiff ComplexInnerProductSpace NNReal

namespace Riesz1

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace Internal

/-- A smooth interior cutoff of the original solution has an L²
representative and L² Laplacian, without global assumptions on the potential. -/
theorem schrodinger_cutoff_l2_data {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ) {u : E → ℂ}
    (huL : MemLp u 2 (volume.restrict U))
    (hu : IsDistributionalSchrodingerSolution U W lam u)
    {b : E → ℝ} (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ U) :
    ∃ a f : Lp ℂ 2 (volume : Measure E),
      Δ (a : 𝓢'(E, ℂ)) = (f : 𝓢'(E, ℂ)) ∧
      (a : E → ℂ) =ᵐ[volume] (fun x => b x • u x) := by
  have hz : MemLp (U.indicator u) 2 volume :=
    (memLp_indicator_iff_restrict hU.measurableSet.nullMeasurableSet).mpr huL
  let w : Lp ℂ 2 (volume : Measure E) := hz.toLp (U.indicator u)
  have hwu : (w : E → ℂ) =ᵐ[volume.restrict U] u := by
    filter_upwards [ae_restrict_of_ae hz.coeFn_toLp,
      ae_restrict_mem hU.measurableSet] with x hx hxU
    exact hx.trans (indicator_of_mem hxU u)
  have hw := hu.congr hU hwu.symm
  have hΔ := schrodinger_cutoff_laplacian_memSobolev_zero hU hW lam w hw hb hbc hbU
  have hbL : MemLp b ⊤ volume := hb.continuous.memLp_top_of_hasCompactSupport hbc volume
  have haL : MemLp (fun x => b x • w x) 2 volume := hbL.smul (Lp.memLp w)
  let a : Lp ℂ 2 (volume : Measure E) := haL.toLp (fun x => b x • w x)
  have hB : Function.HasTemperateGrowth (fun x => (b x : ℂ)) :=
    ((hbc.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hb)).hasTemperateGrowth
  have hTa : smulLeftCLM ℂ (fun x => (b x : ℂ)) (w : 𝓢'(E, ℂ)) =
      (a : 𝓢'(E, ℂ)) := by
    ext ψ
    rw [smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
      Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [haL.coeFn_toLp] with x hx
    rw [hx, SchwartzMap.smulLeftCLM_apply_apply hB]
    module
  obtain ⟨f, hf⟩ := memSobolev_zero_iff.mp hΔ
  refine ⟨a, f, by rwa [hTa] at hf, ?_⟩
  filter_upwards [haL.coeFn_toLp, (ae_restrict_iff' hU.measurableSet).mp hwu] with x hx hwx
  rw [hx]
  by_cases hxU : x ∈ U
  · rw [hwx hxU]
  · have hb0 := image_eq_zero_of_notMem_tsupport (fun h => hxU (hbU h))
    simp only [hb0, zero_smul]

/-- The L² Laplacian of a distributional solution equals its locally
integrable potential term in the original open domain. -/
theorem schrodinger_laplacian_ae {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} {lam : ℝ} {u f : Lp ℂ 2 (volume : Measure E)}
    (hΔ : Δ (u : 𝓢'(E, ℂ)) = (f : 𝓢'(E, ℂ)))
    (hu : IsDistributionalSchrodingerSolution U W lam (u : E → ℂ)) :
    (f : E → ℂ) =ᵐ[volume.restrict U] (fun x => (W x + lam) • u x) := by
  have hfL := ((Lp.memLp f).locallyIntegrable (by norm_num)).locallyIntegrableOn U
  have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hfL.sub hu.2.1)
    (fun φ hφ hφc hφU => ?_)
  · exact (ae_restrict_iff' hU.measurableSet).mpr
      (hz.mono (fun x hx hxU => sub_eq_zero.mp (hx hxU)))
  · let ψ : 𝓢(E, ℂ) := (hφc.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hφ)
    have he := congrArg (fun T : 𝓢'(E, ℂ) => T ψ) hΔ
    have hl (x : E) : (Δ ψ) x = ((Δ φ) x : ℂ) := by
      rw [SchwartzMap.laplacian_apply]
      change (Δ (Complex.ofRealCLM ∘ φ)) x = _
      exact (hφ.contDiffAt.of_le (by simp)).laplacian_CLM_comp_left
    simp only [TemperedDistribution.laplacian_apply_apply,
      Lp.toTemperedDistribution_apply, hl] at he
    have he' : (∫ x, (Δ φ) x • u x) = ∫ x, φ x • f x := he
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub
      (integrable_smul_of_compact_interior hfL hφ.continuous hφc hφU)
      (integrable_smul_of_compact_interior hu.2.1 hφ.continuous hφc hφU),
      hu.2.2 φ hφ hφc hφU, he', sub_self]

end Internal

/-- Euclidean interior regularity and compact Lipschitz cutoff energy
for a complex distributional solution.
The finite sum is the squared norm of the weak gradient in an orthonormal
basis. No lower bound on the potential is needed for this local assertion. -/
theorem interiorRegularity_complex_energy {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ) {u : E → ℂ}
    (huL : MemLp u 2 (volume.restrict U))
    (hu : IsDistributionalSchrodingerSolution U W lam u)
    {b : E → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ U) :
    IsLocalH2 U u ∧ ∃ g : Fin (Module.finrank ℝ E) → E → ℂ,
      (∀ i, MemLp (g i) 2 volume ∧
        HasWeakDirectionalDerivativeOn univ (fun x => b x • u x) (g i)
          (stdOrthonormalBasis ℝ E i)) ∧
      Integrable (fun x => ∑ i, ‖g i x‖ ^ 2) ∧
      Integrable (fun x => (W x + lam) * ‖b x • u x‖ ^ 2) ∧
      Integrable (fun x => (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) *
        ‖u x‖ ^ 2) ∧
      (∫ x, ∑ i, ‖g i x‖ ^ 2) + (∫ x, (W x + lam) * ‖b x • u x‖ ^ 2) =
        ∫ x, (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) * ‖u x‖ ^ 2 := by
  classical
  obtain ⟨V, χ, hVo, hbV, hVU, hχ, hχc, hχU, hχ1⟩ :=
    Internal.exists_smooth_interior_cutoff hU hbc hbU
  obtain ⟨a, f, hΔ, hae⟩ := Internal.schrodinger_cutoff_l2_data hU hW lam huL hu hχ hχc hχU
  have haeV : (a : E → ℂ) =ᵐ[volume.restrict V] u := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hVo.measurableSet] with x hx hxV
    simpa only [hχ1 x hxV, one_smul] using hx
  have haeq := (hu.mono hVU).congr hVo haeV.symm
  have hfV := (ae_restrict_iff' hVo.measurableSet).mp
    (Internal.schrodinger_laplacian_ae hVo hΔ haeq)
  have haV := (ae_restrict_iff' hVo.measurableSet).mp haeV
  have hba : (fun x => b x • a x) =ᵐ[volume] (fun x => b x • u x) := by
    filter_upwards [haV] with x hx
    by_cases hxV : x ∈ V
    · rw [hx hxV]
    · have hb0 := image_eq_zero_of_notMem_tsupport (fun h => hxV (hbV h))
      simp only [hb0, zero_smul]
  have hpot : (fun x => RCLike.re (⟪b x ^ 2 • a x, f x⟫ : ℂ)) =ᵐ[volume]
      (fun x => (W x + lam) * ‖b x • u x‖ ^ 2) := by
    filter_upwards [haV, hfV] with x hx hy
    by_cases hxV : x ∈ V
    · rw [hy hxV, hx hxV]
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left,
        inner_smul_right, RCLike.conj_ofReal, inner_self_eq_norm_sq_to_K,
        ← RCLike.ofReal_pow, RCLike.mul_re, RCLike.ofReal_re,
        RCLike.ofReal_im, zero_mul, sub_zero, norm_smul, RCLike.norm_ofReal, mul_pow, sq_abs]
    · have hb0 := image_eq_zero_of_notMem_tsupport (fun h => hxV (hbV h))
      simp only [hb0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_smul,
        inner_zero_left, map_zero, norm_zero, mul_zero]
  have hrhs : (fun x => (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) *
      ‖a x‖ ^ 2) =ᵐ[volume]
      (fun x => (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) * ‖u x‖ ^ 2) := by
    filter_upwards [haV] with x hx
    by_cases hxV : x ∈ V
    · rw [hx hxV]
    · have hb0 := fderiv_of_notMem_tsupport ℝ (f := b) (fun h => hxV (hbV h))
      simp only [hb0, zero_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        Finset.sum_const_zero, zero_mul]
  obtain ⟨g, hg, hkin, hpotI, hrhsI, henergy⟩ :=
    Internal.lipschitz_cutoff_laplacian_energy a f hΔ hb hbc
  refine ⟨interiorRegularity_complex_h2 hU hW lam huL hu,
    g, fun i => ⟨(hg i).1, ?_⟩, hkin, hpotI.congr hpot, hrhsI.congr hrhs, ?_⟩
  · exact (hg i).2.congr isOpen_univ (ae_restrict_of_ae hba) Filter.EventuallyEq.rfl
  · rwa [integral_congr_ae hpot, integral_congr_ae hrhs] at henergy

/-- The same Euclidean energy assertion only needs locally L² data.
This form can be applied to periodic lifts after local measure transport. -/
theorem interiorRegularity_complex_local_energy {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ) {u : E → ℂ}
    (huL : LocallySquareIntegrableOn U u)
    (hu : IsDistributionalSchrodingerSolution U W lam u)
    {b : E → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ U) :
    IsLocalH2 U u ∧ ∃ g : Fin (Module.finrank ℝ E) → E → ℂ,
      (∀ i, MemLp (g i) 2 volume ∧
        HasWeakDirectionalDerivativeOn univ (fun x => b x • u x) (g i)
          (stdOrthonormalBasis ℝ E i)) ∧
      Integrable (fun x => ∑ i, ‖g i x‖ ^ 2) ∧
      Integrable (fun x => (W x + lam) * ‖b x • u x‖ ^ 2) ∧
      Integrable (fun x => (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) *
        ‖u x‖ ^ 2) ∧
      (∫ x, ∑ i, ‖g i x‖ ^ 2) + (∫ x, (W x + lam) * ‖b x • u x‖ ^ 2) =
        ∫ x, (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) * ‖u x‖ ^ 2 := by
  obtain ⟨V, χ, hVo, hbV, hVU, _, hχc, hχU, hχ1⟩ :=
    Internal.exists_smooth_interior_cutoff hU hbc hbU
  have hVχ : V ⊆ tsupport χ := by
    intro x hx
    apply subset_tsupport χ
    simp only [Function.mem_support, hχ1 x hx, ne_eq, one_ne_zero, not_false_eq_true]
  have huLV : MemLp u 2 (volume.restrict V) :=
    (huL _ hχc hχU).mono_measure (Measure.restrict_mono hVχ le_rfl)
  exact ⟨isLocalH2_of_locallySquareIntegrable_schrodinger hU hW lam huL hu,
    (interiorRegularity_complex_energy hVo (hW.mono hVU) lam huLV (hu.mono hVU)
      hb hbc hbV).2⟩

end Riesz1
