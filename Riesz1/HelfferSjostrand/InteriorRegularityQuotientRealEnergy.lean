/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.InteriorRegularityQuotientEnergy

/-!
# Real quotient energy

The real form of interior regularity on the cyclic configuration
quotient, obtained by uniqueness of real weak derivatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff NNReal

namespace Riesz1

/-- Interior regularity, real quotient energy for periodic interior
cutoffs, with local H² and integrability of every energy integrand. -/
theorem interiorRegularity_quotient_real_energy {N : ℕ+}
    {W : HsCylinder N → ℝ}
    (hW : ContDiffOn ℝ ∞ (fun x : HsEuclidean N => W (QuotientAddGroup.mk x)) (hsChamber N))
    (lam : ℝ) {u : HsCylinder N → ℝ}
    (huL : MemLp (fun x : HsConfiguration N => u x.val) 2 (hsConfigurationVolume N))
    (hu : IsDistributionalSchrodingerSolution (hsChamber N)
      (fun x => W (QuotientAddGroup.mk x)) lam (fun x => u (QuotientAddGroup.mk x)))
    {b : HsEuclidean N → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b)
    (hbp : ∀ (k : ℤ) x, b (hsTranslate (k : ℝ) x) = b x)
    (hbU : tsupport b ⊆ hsChamber N) :
    IsLocalH2 (hsChamber N) (fun x => u (QuotientAddGroup.mk x)) ∧
    ∃ k : Fin (Module.finrank ℝ (HsEuclidean N)) → HsEuclidean N → ℝ,
      (∀ i, (∀ (j : ℤ) x, k i (hsTranslate (j : ℝ) x) = k i x) ∧
        MemLp (k i ∘ hsLiftPoint N) 2 (hsConfigurationVolume N) ∧
        HasWeakDirectionalDerivativeOn (hsChamber N)
          (fun x => b x * u (QuotientAddGroup.mk x)) (k i)
          (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ∧
      Integrable (fun x : HsConfiguration N => ∑ i, (k i (hsLiftPoint N x)) ^ 2)
        (hsConfigurationVolume N) ∧
      Integrable (fun x : HsConfiguration N => (W x.val + lam) *
        (b (hsLiftPoint N x) * u x.val) ^ 2) (hsConfigurationVolume N) ∧
      Integrable (fun x : HsConfiguration N =>
        (∑ i, (fderiv ℝ b (hsLiftPoint N x) (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ^ 2) *
          (u x.val) ^ 2) (hsConfigurationVolume N) ∧
      (∫ x : HsConfiguration N, ∑ i, (k i (hsLiftPoint N x)) ^ 2 ∂hsConfigurationVolume N) +
        (∫ x : HsConfiguration N, (W x.val + lam) *
          (b (hsLiftPoint N x) * u x.val) ^ 2 ∂hsConfigurationVolume N) =
        ∫ x : HsConfiguration N,
          (∑ i, (fderiv ℝ b (hsLiftPoint N x) (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ^ 2) *
            (u x.val) ^ 2 ∂hsConfigurationVolume N := by
  classical
  have huC : IsDistributionalSchrodingerSolution (hsChamber N)
      (fun x => W (QuotientAddGroup.mk x)) lam
      (fun x => (u (QuotientAddGroup.mk x) : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using hu.map Complex.ofRealCLM
  have huLC : MemLp (fun x : HsConfiguration N => (u x.val : ℂ)) 2
      (hsConfigurationVolume N) := Complex.ofRealCLM.comp_memLp' huL
  obtain ⟨_, k, hk, hkin, hpot, hrhs, he⟩ :=
    interiorRegularity_quotient_complex_energy (u := fun x => (u x : ℂ))
      hW lam huLC huC hb hbp hbU
  have hreal (x : HsEuclidean N) :
      b x • (u (QuotientAddGroup.mk x) : ℂ) = ((b x * u (QuotientAddGroup.mk x) : ℝ) : ℂ) := by
    rw [Complex.real_smul, Complex.ofReal_mul]
  have him (i : Fin (Module.finrank ℝ (HsEuclidean N))) :
      (fun x : HsConfiguration N => (k i (hsLiftPoint N x)).im) =ᵐ[hsConfigurationVolume N]
        (fun _ => (0 : ℝ)) := by
    have hz : (fun x => (k i x).im) =ᵐ[volume.restrict (hsChamber N)]
        (fun _ => (0 : ℝ)) := by
      apply Internal.weak_derivative_ofReal_im_eq_zero_on (isOpen_hsChamber N)
        (u := fun x => b x * u (QuotientAddGroup.mk x))
      simpa only [hreal] using (hk i).2.2
    exact ae_eq_comp_hsLiftPoint_volume hz
  have hnorm : (fun x : HsConfiguration N => ∑ i, ‖k i (hsLiftPoint N x)‖ ^ 2)
      =ᵐ[hsConfigurationVolume N] (fun x => ∑ i, (k i (hsLiftPoint N x)).re ^ 2) := by
    filter_upwards [ae_all_iff.mpr him] with x hx
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.sq_norm, Complex.normSq_apply, hx i]
    ring
  refine ⟨interiorRegularity_quotient_real_h2 hW lam huL hu,
    (fun i x => (k i x).re), fun i => ⟨?_, ?_, ?_⟩, hkin.congr hnorm, ?_, ?_, ?_⟩
  · intro j x
    exact congrArg Complex.re ((hk i).1 j x)
  · exact Complex.reCLM.comp_memLp' (hk i).2.1
  · have hm := (hk i).2.2.map Complex.reCLM
    simpa only [Function.comp_def, hreal, Complex.reCLM_apply, Complex.ofReal_re] using hm
  · simpa only [Complex.real_smul, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
      sq_abs] using hpot
  · simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hrhs
  · rw [integral_congr_ae hnorm] at he
    simpa only [Complex.real_smul, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
      sq_abs] using he

end Riesz1
