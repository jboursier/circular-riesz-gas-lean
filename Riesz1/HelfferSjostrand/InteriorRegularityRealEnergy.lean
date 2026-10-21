/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.InteriorRegularityEnergy

/-!
# Real interior cutoff energy

The real Euclidean energy assertion of interior regularity, obtained
from the complex assertion by uniqueness of weak derivatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff NNReal

namespace Riesz1

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace Internal

/-- A weak derivative of a real function, embedded in the complex
numbers, is real almost everywhere. -/
theorem weak_derivative_ofReal_im_eq_zero {u : E → ℝ} {g : E → ℂ} {v : E}
    (hg : HasWeakDirectionalDerivativeOn univ (fun x => (u x : ℂ)) g v) :
    (fun x => (g x).im) =ᵐ[volume] (fun _ => (0 : ℝ)) := by
  have hi : HasWeakDirectionalDerivativeOn univ (fun _ : E => (0 : ℝ))
      (fun x => (g x).im) v := by
    simpa only [Function.comp_def, Complex.imCLM_apply, Complex.ofReal_im] using
      hg.map Complex.imCLM
  have hz : HasWeakDirectionalDerivativeOn univ (fun _ : E => (0 : ℝ))
      (fun _ => (0 : ℝ)) v := by
    have hh := hasWeakDirectionalDerivativeOn_of_smooth (E := E) isOpen_univ
      (contDiffOn_const (c := (0 : ℝ))) v
    have he : (fun x : E => fderiv ℝ (fun _ : E => (0 : ℝ)) x v) = fun _ => (0 : ℝ) := by
      funext x
      rw [fderiv_const_apply]
      rfl
    rwa [he] at hh
  simpa only [Measure.restrict_univ] using hi.unique isOpen_univ hz

end Internal

/-- Real Euclidean interior H² regularity and the full compact Lipschitz
cutoff energy identity. -/
theorem interiorRegularity_real_energy {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ) {u : E → ℝ}
    (huL : MemLp u 2 (volume.restrict U))
    (hu : IsDistributionalSchrodingerSolution U W lam u)
    {b : E → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ U) :
    IsLocalH2 U u ∧ ∃ g : Fin (Module.finrank ℝ E) → E → ℝ,
      (∀ i, MemLp (g i) 2 volume ∧
        HasWeakDirectionalDerivativeOn univ (fun x => b x * u x) (g i)
          (stdOrthonormalBasis ℝ E i)) ∧
      Integrable (fun x => ∑ i, (g i x) ^ 2) ∧
      Integrable (fun x => (W x + lam) * (b x * u x) ^ 2) ∧
      Integrable (fun x => (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) *
        (u x) ^ 2) ∧
      (∫ x, ∑ i, (g i x) ^ 2) + (∫ x, (W x + lam) * (b x * u x) ^ 2) =
        ∫ x, (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) * (u x) ^ 2 := by
  classical
  have huC : IsDistributionalSchrodingerSolution U W lam (fun x => (u x : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using hu.map Complex.ofRealCLM
  have huLC : MemLp (fun x => (u x : ℂ)) 2 (volume.restrict U) :=
    Complex.ofRealCLM.comp_memLp' huL
  obtain ⟨_, g, hg, hkin, hpot, hrhs, henergy⟩ := interiorRegularity_complex_energy
    hU hW lam huLC huC hb hbc hbU
  have hreal (x : E) : b x • (u x : ℂ) = ((b x * u x : ℝ) : ℂ) := by
    rw [Complex.real_smul, Complex.ofReal_mul]
  have hgR (i : Fin (Module.finrank ℝ E)) :
      HasWeakDirectionalDerivativeOn univ (fun x => b x * u x)
        (fun x => (g i x).re) (stdOrthonormalBasis ℝ E i) := by
    have hm := (hg i).2.map Complex.reCLM
    simpa only [Function.comp_def, hreal, Complex.reCLM_apply, Complex.ofReal_re] using hm
  have him (i : Fin (Module.finrank ℝ E)) :
      (fun x => (g i x).im) =ᵐ[volume] (fun _ => (0 : ℝ)) := by
    apply Internal.weak_derivative_ofReal_im_eq_zero (u := fun x => b x * u x)
      (v := stdOrthonormalBasis ℝ E i)
    simpa only [hreal] using (hg i).2
  have hnorm : (fun x => ∑ i, ‖g i x‖ ^ 2) =ᵐ[volume]
      (fun x => ∑ i, (g i x).re ^ 2) := by
    have ha := ae_all_iff.mpr him
    filter_upwards [ha] with x hx
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.sq_norm, Complex.normSq_apply, hx i]
    ring
  have hpotEq (x : E) : (W x + lam) * ‖b x • (u x : ℂ)‖ ^ 2 =
      (W x + lam) * (b x * u x) ^ 2 := by
    rw [hreal, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hrhsEq (x : E) :
      (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) * ‖(u x : ℂ)‖ ^ 2 =
      (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) * (u x) ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  refine ⟨interiorRegularity_real_h2 hU hW lam huL hu,
    (fun i x => (g i x).re), fun i => ⟨?_, hgR i⟩,
    hkin.congr hnorm, ?_, ?_, ?_⟩
  · exact Complex.reCLM.comp_memLp' (hg i).1
  · simpa only [hpotEq] using hpot
  · simpa only [hrhsEq] using hrhs
  · rw [integral_congr_ae hnorm] at henergy
    simpa only [hpotEq, hrhsEq] using henergy

/-- Local L² data suffice for the real Euclidean regularity and energy
assertions, including when a lift is not globally L². -/
theorem interiorRegularity_real_local_energy {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ) {u : E → ℝ}
    (huL : LocallySquareIntegrableOn U u)
    (hu : IsDistributionalSchrodingerSolution U W lam u)
    {b : E → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ U) :
    IsLocalH2 U u ∧ ∃ g : Fin (Module.finrank ℝ E) → E → ℝ,
      (∀ i, MemLp (g i) 2 volume ∧
        HasWeakDirectionalDerivativeOn univ (fun x => b x * u x) (g i)
          (stdOrthonormalBasis ℝ E i)) ∧
      Integrable (fun x => ∑ i, (g i x) ^ 2) ∧
      Integrable (fun x => (W x + lam) * (b x * u x) ^ 2) ∧
      Integrable (fun x => (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) *
        (u x) ^ 2) ∧
      (∫ x, ∑ i, (g i x) ^ 2) + (∫ x, (W x + lam) * (b x * u x) ^ 2) =
        ∫ x, (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) * (u x) ^ 2 := by
  obtain ⟨V, χ, hVo, hbV, hVU, _, hχc, hχU, hχ1⟩ :=
    Internal.exists_smooth_interior_cutoff hU hbc hbU
  have hVχ : V ⊆ tsupport χ := by
    intro x hx
    apply subset_tsupport χ
    simp only [Function.mem_support, hχ1 x hx, ne_eq, one_ne_zero, not_false_eq_true]
  have huLV : MemLp u 2 (volume.restrict V) :=
    (huL _ hχc hχU).mono_measure (Measure.restrict_mono hVχ le_rfl)
  have hC := isLocalH2_of_locallySquareIntegrable_schrodinger hU hW lam
    (huL.map Complex.ofRealCLM) (hu.map Complex.ofRealCLM)
  have hR : IsLocalH2 U u := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.reCLM_apply,
      Complex.ofReal_re] using hC.map Complex.reCLM
  exact ⟨hR, (interiorRegularity_real_energy hVo (hW.mono hVU) lam huLV (hu.mono hVU)
    hb hbc hbV).2⟩

end Riesz1
