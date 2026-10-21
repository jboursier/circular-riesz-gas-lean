/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BoundaryCoreBarrier
public import Riesz1.HelfferSjostrand.InteriorRegularityQuotientRealEnergy

/-!
# The inverse-square barrier on the cyclic quotient

The kernel-vanishing step, using periodic
positive-part distance cutoffs and the quotient energy identity.
The theorem concerns distributional solutions. The identification with
the adjoint of the scalar core operator is separate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace Riesz1.Internal

/-- Real `L²` solutions on the cyclic quotient vanish under the
inverse-square barrier. The common rotation seam introduces no boundary. -/
theorem quotient_schrodinger_eq_zero_of_boundary_barrier {N : ℕ+} (hN : 2 ≤ (N : ℕ))
    {W : HsCylinder N → ℝ}
    (hW : ContDiffOn ℝ ∞ (fun x : HsEuclidean N => W (QuotientAddGroup.mk x)) (hsChamber N))
    {C lam : ℝ} (hlam : C < lam)
    (hbar : ∀ x : HsConfiguration N,
      (hsQuotientBoundaryDistance N hN x)⁻¹ ^ 2 - C ≤ W x.val)
    {u : HsCylinder N → ℝ}
    (huL : MemLp (fun x : HsConfiguration N => u x.val) 2 (hsConfigurationVolume N))
    (hu : IsDistributionalSchrodingerSolution (hsChamber N)
      (fun x => W (QuotientAddGroup.mk x)) lam (fun x => u (QuotientAddGroup.mk x))) :
    (fun x : HsConfiguration N => u x.val) =ᵐ[hsConfigurationVolume N] 0 := by
  let d := hsQuotientBoundaryDistance N hN
  have hdm : Measurable d :=
    (hsBoundaryDistance_lipschitz N hN).continuous.measurable.comp (measurable_hsLiftPoint N)
  have hd : ∀ᵐ x ∂hsConfigurationVolume N, 0 < d x ∧ d x ≤ 1 :=
    Eventually.of_forall fun x => ⟨hsBoundaryDistance_pos hN (hsLiftPoint_mem_chamber N x),
      hsBoundaryDistance_le_one hN (hsLiftPoint_mem_chamber N x)⟩
  have hsq := huL.integrable_sq
  have hz : (fun x : HsConfiguration N => u x.val ^ 2) =ᵐ[hsConfigurationVolume N] 0 := by
    apply eq_zero_of_boundary_barrier_estimates hdm hd hsq
      (Eventually.of_forall fun x => sq_nonneg (u x.val)) (sub_pos.mpr hlam)
    intro ε hε
    let b := boundaryCoreCutoff (hsChamber N) ε
    have hb : LipschitzWith 1 b := boundaryCoreCutoff_lipschitz _ ε
    have hbp (j : ℤ) (x : HsEuclidean N) : b (hsTranslate (j : ℝ) x) = b x := by
      change max (hsBoundaryDistance N hN (hsTranslate (j : ℝ) x) - ε) 0 = _
      rw [hsBoundaryDistance_translate]
      rfl
    have hbU : tsupport b ⊆ hsChamber N := boundaryCoreCutoff_tsupport hε
    obtain ⟨_, g, _, hkin, hpot, hrhs, he⟩ :=
      interiorRegularity_quotient_real_energy hW lam huL hu hb hbp hbU
    let A : HsConfiguration N → ℝ := fun x =>
      ((max (d x - ε) 0 / d x) ^ 2 + (lam - C) * max (d x - ε) 0 ^ 2) * u x.val ^ 2
    have hAint : Integrable A (hsConfigurationVolume N) := by
      apply Integrable.mono' (hsq.const_mul (1 + (lam - C) * (1 : ℝ) ^ 2))
      · exact (((((hdm.sub_const ε).max measurable_const).div hdm).aestronglyMeasurable.pow 2).add
          (aestronglyMeasurable_const.mul
            (((hdm.sub_const ε).max measurable_const).aestronglyMeasurable.pow 2))).mul
              (huL.aestronglyMeasurable.pow 2)
      · filter_upwards [hd] with x hx
        have hh := boundary_barrier_cutoff_bound hx.1 hx.2 hε.le (sub_pos.mpr hlam).le
          (sq_nonneg (u x.val))
        change ‖A x‖ ≤ _
        rw [Real.norm_eq_abs, abs_of_nonneg hh.1]
        exact hh.2
    have hApot : ∀ x : HsConfiguration N,
        A x ≤ (W x.val + lam) * (b (hsLiftPoint N x) * u x.val) ^ 2 := by
      intro x
      have hh := mul_le_mul_of_nonneg_right (hbar x)
        (sq_nonneg (b (hsLiftPoint N x) * u x.val))
      change ((max (d x - ε) 0 / d x) ^ 2 + (lam - C) * max (d x - ε) 0 ^ 2) *
        u x.val ^ 2 ≤ (W x.val + lam) * (max (d x - ε) 0 * u x.val) ^ 2
      change ((d x)⁻¹ ^ 2 - C) * (max (d x - ε) 0 * u x.val) ^ 2 ≤
          W x.val * (max (d x - ε) 0 * u x.val) ^ 2 at hh
      simp only [div_eq_mul_inv] at *
      nlinarith
    calc
      (∫ x, A x ∂hsConfigurationVolume N) ≤ ∫ x : HsConfiguration N,
          (W x.val + lam) * (b (hsLiftPoint N x) * u x.val) ^ 2 ∂hsConfigurationVolume N :=
        integral_mono_ae hAint hpot (Eventually.of_forall hApot)
      _ ≤ ∫ x : HsConfiguration N,
          (∑ i, (fderiv ℝ b (hsLiftPoint N x) (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ^ 2) *
            u x.val ^ 2 ∂hsConfigurationVolume N := by
        have hkn : 0 ≤ ∫ x : HsConfiguration N, ∑ i, (g i (hsLiftPoint N x)) ^ 2
            ∂hsConfigurationVolume N :=
          integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
        linarith
      _ ≤ ∫ x : HsConfiguration N, u x.val ^ 2 ∂hsConfigurationVolume N := by
        apply integral_mono_ae hrhs hsq
        exact Eventually.of_forall fun x => mul_le_of_le_one_left (sq_nonneg _)
          (sum_sq_fderiv_le_one hb (hsLiftPoint N x))
  filter_upwards [hz] with x hx
  exact sq_eq_zero_iff.mp hx

/-- Complex quotient solutions vanish by applying the real argument to
their real and imaginary parts. -/
theorem quotient_schrodinger_complex_eq_zero_of_boundary_barrier {N : ℕ+} (hN : 2 ≤ (N : ℕ))
    {W : HsCylinder N → ℝ}
    (hW : ContDiffOn ℝ ∞ (fun x : HsEuclidean N => W (QuotientAddGroup.mk x)) (hsChamber N))
    {C lam : ℝ} (hlam : C < lam)
    (hbar : ∀ x : HsConfiguration N,
      (hsQuotientBoundaryDistance N hN x)⁻¹ ^ 2 - C ≤ W x.val)
    {u : HsCylinder N → ℂ}
    (huL : MemLp (fun x : HsConfiguration N => u x.val) 2 (hsConfigurationVolume N))
    (hu : IsDistributionalSchrodingerSolution (hsChamber N)
      (fun x => W (QuotientAddGroup.mk x)) lam (fun x => u (QuotientAddGroup.mk x))) :
    (fun x : HsConfiguration N => u x.val) =ᵐ[hsConfigurationVolume N] 0 := by
  have hre := quotient_schrodinger_eq_zero_of_boundary_barrier (u := fun x => (u x).re)
    hN hW hlam hbar
    (Complex.reCLM.comp_memLp' huL) (hu.map Complex.reCLM)
  have him := quotient_schrodinger_eq_zero_of_boundary_barrier (u := fun x => (u x).im)
    hN hW hlam hbar
    (Complex.imCLM.comp_memLp' huL) (hu.map Complex.imCLM)
  filter_upwards [hre, him] with x hx hy
  exact Complex.ext hx hy

end Riesz1.Internal
