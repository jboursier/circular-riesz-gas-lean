/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.QuotientChartCutoffs
public import Riesz1.HelfferSjostrand.QuotientChartWeakGradient
public import Riesz1.ToMathlib.EllipticRegularity.LocalLipschitz

/-!
# Quotient L² gradients and integrability of cutoff energies

For a periodic Lipschitz lift supported inside the chamber, local weak
gradients descend to L² of quotient volume. All three integrands in the
energy assertion of interior regularity are integrable.
The equality between their integrals is a separate assertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff NNReal

namespace Riesz1

namespace Internal

/-- A locally L² representative multiplied by an interior continuous
cutoff belongs to quotient L². -/
theorem quotient_memLp_cutoff_smul {N : ℕ+} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : HsEuclidean N → F} (hu : LocallySquareIntegrableOn (hsChamber N) u)
    {b : HsEuclidean N → ℝ} (hb : Continuous b) (hbU : tsupport b ⊆ hsChamber N) :
    MemLp ((fun x => b x • u x) ∘ hsLiftPoint N) 2 (hsConfigurationVolume N) := by
  apply memLp_quotient_of_local_support (hu.smul_continuousOn hb.continuousOn) hbU
  intro x hx
  apply subset_tsupport b
  intro hb0
  exact hx (by change b x • u x = 0; rw [hb0, zero_smul])

/-- The derivative of a Lipschitz interior cutoff, multiplied by locally
L² data, also belongs to quotient L². -/
theorem quotient_memLp_cutoff_fderiv_smul {N : ℕ+} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : HsEuclidean N → F} (hu : LocallySquareIntegrableOn (hsChamber N) u)
    {b : HsEuclidean N → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b)
    (hbU : tsupport b ⊆ hsChamber N) (v : HsEuclidean N) :
    MemLp ((fun x => fderiv ℝ b x v • u x) ∘ hsLiftPoint N) 2 (hsConfigurationVolume N) := by
  have hlocal : LocallySquareIntegrableOn (hsChamber N)
      (fun x => fderiv ℝ b x v • u x) := by
    intro K hK hKU
    exact ((memLp_top_fderiv_lipschitz hb v).restrict K).smul (hu K hK hKU)
  apply memLp_quotient_of_local_support hlocal hbU
  intro x hx
  by_contra hxb
  exact hx (by change fderiv ℝ b x v • u x = 0
               rw [fderiv_of_notMem_tsupport ℝ hxb, zero_apply, zero_smul])

/-- The potential term of an interior cutoff is integrable on the
quotient. Neither a lower bound nor a global bound on the potential is needed. -/
theorem quotient_integrable_cutoff_potential {N : ℕ+}
    {u : HsEuclidean N → ℂ} (hu : LocallySquareIntegrableOn (hsChamber N) u)
    {W : HsEuclidean N → ℝ} (hW : ContinuousOn W (hsChamber N))
    {b : HsEuclidean N → ℝ} (hb : Continuous b) (hbU : tsupport b ⊆ hsChamber N) :
    Integrable (fun x : HsConfiguration N =>
      W (hsLiftPoint N x) * ‖b (hsLiftPoint N x) • u (hsLiftPoint N x)‖ ^ 2)
      (hsConfigurationVolume N) := by
  have hbu := hu.smul_continuousOn hb.continuousOn
  have hnorm : LocallySquareIntegrableOn (hsChamber N) (fun x => ‖b x • u x‖) := by
    intro K hK hKU
    exact (hbu K hK hKU).norm
  have hwnorm := hnorm.smul_continuousOn hW
  have hn : MemLp ((fun x => ‖b x • u x‖) ∘ hsLiftPoint N) 2
      (hsConfigurationVolume N) := (quotient_memLp_cutoff_smul hu hb hbU).norm
  have hw : MemLp ((fun x => W x * ‖b x • u x‖) ∘ hsLiftPoint N) 2
      (hsConfigurationVolume N) := by
    apply memLp_quotient_of_local_support hwnorm hbU
    intro x hx
    apply subset_tsupport b
    intro hb0
    exact hx (by simp only [hb0, zero_smul, norm_zero, smul_eq_mul, mul_zero])
  apply (hw.integrable_mul hn).congr
  filter_upwards with x
  change (W (hsLiftPoint N x) * ‖b (hsLiftPoint N x) • u (hsLiftPoint N x)‖) *
    ‖b (hsLiftPoint N x) • u (hsLiftPoint N x)‖ = _
  ring

end Internal

/-- The quotient cutoff of a complex solution has an L² weak gradient,
with pointwise periodic representatives, and every energy integrand is
integrable. Cutoffs use the same periodic interior zero-extension
convention as the quotient test functions. This is the gradient
and integrability part of interior regularity. -/
theorem interiorRegularity_quotient_complex_cutoff_integrability {N : ℕ+}
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
          ‖u x.val‖ ^ 2) (hsConfigurationVolume N) := by
  classical
  let e := stdOrthonormalBasis ℝ (HsEuclidean N)
  let u₀ := fun x : HsEuclidean N => u (QuotientAddGroup.mk x)
  have hH2 := interiorRegularity_quotient_complex_h2 hW lam huL hu
  obtain ⟨g, _, hgp, _, hd, _, _⟩ := Internal.isLocalH2_quotient_periodic_derivatives hH2
  let k := fun i x => fderiv ℝ b x (e i) • u₀ x + b x • g i x
  have hku (i) := (hd i).2.1.smul_lipschitz (isOpen_hsChamber N) hH2.1 (hd i).1 hb
  have hkL (i) : MemLp (k i ∘ hsLiftPoint N) 2 (hsConfigurationVolume N) :=
    (Internal.quotient_memLp_cutoff_fderiv_smul hH2.1 hb hbU (e i)).add
      (Internal.quotient_memLp_cutoff_smul (hd i).1 hb.continuous hbU)
  have hkp (i) (j : ℤ) (x : HsEuclidean N) : k i (hsTranslate (j : ℝ) x) = k i x := by
    have hdb : fderiv ℝ b (hsTranslate (j : ℝ) x) = fderiv ℝ b x := by
      rw [hsTranslate_eq_add_rotation]
      exact fderiv_periodic_vector
        (fun j x => by rw [← hsTranslate_eq_add_rotation]; exact hbp j x) j x
    dsimp only [k, u₀]
    rw [hdb, hbp, hgp, Internal.hs_quotient_mk_translate]
  have hq (x : HsConfiguration N) :
      (QuotientAddGroup.mk (hsLiftPoint N x) : HsCylinder N) = x.val :=
    congrArg Subtype.val (hsChamberProjection_liftPoint x)
  have hpot := Internal.quotient_integrable_cutoff_potential hH2.1
    (hW.continuousOn.add (continuousOn_const (c := lam))) hb.continuous hbU
  have hrhs (i) : Integrable (fun x : HsConfiguration N =>
      (fderiv ℝ b (hsLiftPoint N x) (e i)) ^ 2 * ‖u x.val‖ ^ 2)
      (hsConfigurationVolume N) := by
    have hi := Internal.quotient_memLp_cutoff_fderiv_smul hH2.1 hb hbU (e i)
    have hi' := (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mp hi
    simpa only [Function.comp_def, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hq] using hi'
  refine ⟨hH2, k, fun i => ⟨hkp i, hkL i, (hku i).2.2⟩,
    integrable_finsetSum _ (fun i _ =>
      (memLp_two_iff_integrable_sq_norm (hkL i).aestronglyMeasurable).mp (hkL i)), ?_, ?_⟩
  · change Integrable (fun x : HsConfiguration N =>
      (W (QuotientAddGroup.mk (hsLiftPoint N x)) + lam) *
        ‖b (hsLiftPoint N x) • u (QuotientAddGroup.mk (hsLiftPoint N x))‖ ^ 2)
        (hsConfigurationVolume N) at hpot
    simpa only [hq] using hpot
  · simpa only [← Finset.sum_mul, e] using integrable_finsetSum Finset.univ (fun i _ => hrhs i)

end Riesz1
