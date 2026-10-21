/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.QuotientChartEnergy
public import Riesz1.HelfferSjostrand.InteriorRegularityQuotientRealCutoffs

/-!
# The quotient cutoff energy identity

Interior regularity and the complete energy identity,
with all three integrands integrable on quotient volume.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff NNReal

namespace Riesz1

/-- Interior regularity and the energy identity for complex solutions and every periodic
Lipschitz interior zero extension. The quotient cutoff converse is proved
separately, so this form also covers cutoffs crossing the rotation seam. -/
theorem interiorRegularity_quotient_complex_energy {N : ℕ+}
    {W : HsCylinder N → ℝ}
    (hW : ContDiffOn ℝ ∞ (fun x : HsEuclidean N => W (QuotientAddGroup.mk x)) (hsChamber N))
    (lam : ℝ) {u : HsCylinder N → ℂ}
    (huL : MemLp (fun x : HsConfiguration N => u x.val) 2 (hsConfigurationVolume N))
    (hu : IsDistributionalSchrodingerSolution (hsChamber N)
      (fun x => W (QuotientAddGroup.mk x)) lam (fun x => u (QuotientAddGroup.mk x)))
    {b : HsEuclidean N → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b)
    (hbp : ∀ (k : ℤ) x, b (hsTranslate (k : ℝ) x) = b x)
    (hbU : tsupport b ⊆ hsChamber N) :
    IsLocalH2 (hsChamber N) (fun x => u (QuotientAddGroup.mk x)) ∧
    ∃ k : Fin (Module.finrank ℝ (HsEuclidean N)) → HsEuclidean N → ℂ,
      (∀ i, (∀ (j : ℤ) x, k i (hsTranslate (j : ℝ) x) = k i x) ∧
        MemLp (k i ∘ hsLiftPoint N) 2 (hsConfigurationVolume N) ∧
        HasWeakDirectionalDerivativeOn (hsChamber N)
          (fun x => b x • u (QuotientAddGroup.mk x)) (k i)
          (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ∧
      Integrable (fun x : HsConfiguration N => ∑ i, ‖k i (hsLiftPoint N x)‖ ^ 2)
        (hsConfigurationVolume N) ∧
      Integrable (fun x : HsConfiguration N => (W x.val + lam) *
        ‖b (hsLiftPoint N x) • u x.val‖ ^ 2) (hsConfigurationVolume N) ∧
      Integrable (fun x : HsConfiguration N =>
        (∑ i, (fderiv ℝ b (hsLiftPoint N x) (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ^ 2) *
          ‖u x.val‖ ^ 2) (hsConfigurationVolume N) ∧
      (∫ x : HsConfiguration N, ∑ i, ‖k i (hsLiftPoint N x)‖ ^ 2 ∂hsConfigurationVolume N) +
        (∫ x : HsConfiguration N, (W x.val + lam) *
          ‖b (hsLiftPoint N x) • u x.val‖ ^ 2 ∂hsConfigurationVolume N) =
        ∫ x : HsConfiguration N,
          (∑ i, (fderiv ℝ b (hsLiftPoint N x) (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ^ 2) *
            ‖u x.val‖ ^ 2 ∂hsConfigurationVolume N := by
  classical
  obtain ⟨hH2, k, hk, hkin, hpot, hrhs⟩ :=
    interiorRegularity_quotient_complex_cutoff_integrability hW lam huL hu hb hbp hbU
  obtain ⟨g, _, hgp, _, hd, _, _⟩ := Internal.isLocalH2_quotient_periodic_derivatives hH2
  have hres := Internal.quotient_cutoff_energy_residual hW lam hH2.1 hu
    (fun i => ⟨(hd i).1, (hd i).2.1⟩) hgp hb hbp hbU
  let e := stdOrthonormalBasis ℝ (HsEuclidean N)
  have hkeq (i) : k i ∘ hsLiftPoint N =ᵐ[hsConfigurationVolume N]
      (fun x => fderiv ℝ b x (e i) • u (QuotientAddGroup.mk x) + b x • g i x) ∘
        hsLiftPoint N := by
    exact quotient_weak_derivative_unique (hk i).2.2
      ((hd i).2.1.smul_lipschitz (isOpen_hsChamber N) hH2.1 (hd i).1 hb).2.2
  have hq (x : HsConfiguration N) : (QuotientAddGroup.mk (hsLiftPoint N x) : HsCylinder N) = x.val :=
    congrArg Subtype.val (hsChamberProjection_liftPoint x)
  have hnorm : (fun x : HsConfiguration N => ∑ i, ‖k i (hsLiftPoint N x)‖ ^ 2)
      =ᵐ[hsConfigurationVolume N] (fun x => ∑ i,
        ‖fderiv ℝ b (hsLiftPoint N x) (e i) • u x.val +
          b (hsLiftPoint N x) • g i (hsLiftPoint N x)‖ ^ 2) := by
    filter_upwards [ae_all_iff.mpr hkeq] with x hx
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Function.comp_def, hq] using congrArg (fun z : ℂ => ‖z‖ ^ 2) (hx i)
  have hres' : (∫ x : HsConfiguration N,
      (∑ i, ‖k i (hsLiftPoint N x)‖ ^ 2) +
        (W x.val + lam) * ‖b (hsLiftPoint N x) • u x.val‖ ^ 2 -
        (∑ i, (fderiv ℝ b (hsLiftPoint N x) (e i)) ^ 2) * ‖u x.val‖ ^ 2
        ∂hsConfigurationVolume N) = 0 := by
    rw [integral_congr_ae (hnorm.fun_add Filter.EventuallyEq.rfl |>.fun_sub Filter.EventuallyEq.rfl)]
    exact hres
  have hsplit := integral_sub (hkin.add hpot) hrhs
  simp only [Pi.add_apply] at hsplit
  rw [integral_add hkin hpot] at hsplit
  exact ⟨hH2, k, hk, hkin, hpot, hrhs, sub_eq_zero.mp (hsplit.symm.trans hres')⟩

end Riesz1
