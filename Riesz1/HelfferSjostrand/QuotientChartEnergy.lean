/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.InteriorRegularityQuotientCutoffs
public import Riesz1.ToMathlib.EllipticRegularity.PrescribedGradientEnergy
public import Riesz1.ToMathlib.Chamber.SquareCutoffVectorEnergy
public import Riesz1.ToMathlib.BoundedLipschitzProduct

/-!
# Unfolding the cutoff energy on the cyclic chamber

A smooth square partition in the rotation coordinate cancels the mixed
terms from compact localization on the cover. This connects the compact
Euclidean energy to the actual quotient volume.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff NNReal ComplexInnerProductSpace

namespace Riesz1.Internal

/-- The quotient residual has zero integral, for any prescribed coherent
periodic weak gradient of the solution. All inputs beyond the PDE and
cutoff are local calculus data. This is an internal assembly theorem. -/
theorem quotient_cutoff_energy_residual {N : ℕ+} {W : HsCylinder N → ℝ}
    (hW : ContDiffOn ℝ ∞ (fun x : HsEuclidean N => W (QuotientAddGroup.mk x)) (hsChamber N))
    (lam : ℝ) {u : HsCylinder N → ℂ}
    (huL : LocallySquareIntegrableOn (hsChamber N) (fun x => u (QuotientAddGroup.mk x)))
    (hu : IsDistributionalSchrodingerSolution (hsChamber N)
      (fun x => W (QuotientAddGroup.mk x)) lam (fun x => u (QuotientAddGroup.mk x)))
    {g : Fin (Module.finrank ℝ (HsEuclidean N)) → HsEuclidean N → ℂ}
    (hg : ∀ i, LocallySquareIntegrableOn (hsChamber N) (g i) ∧
      HasWeakDirectionalDerivativeOn (hsChamber N) (fun x => u (QuotientAddGroup.mk x))
        (g i) (stdOrthonormalBasis ℝ (HsEuclidean N) i))
    (hgp : ∀ i (j : ℤ) x, g i (hsTranslate (j : ℝ) x) = g i x)
    {b : HsEuclidean N → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b)
    (hbp : ∀ (k : ℤ) x, b (hsTranslate (k : ℝ) x) = b x)
    (hbU : tsupport b ⊆ hsChamber N) :
    (∫ x : HsConfiguration N,
      ((∑ i, ‖fderiv ℝ b (hsLiftPoint N x) (stdOrthonormalBasis ℝ (HsEuclidean N) i) •
          u x.val + b (hsLiftPoint N x) • g i (hsLiftPoint N x)‖ ^ 2) +
        (W x.val + lam) * ‖b (hsLiftPoint N x) • u x.val‖ ^ 2 -
        (∑ i, (fderiv ℝ b (hsLiftPoint N x) (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ^ 2) *
          ‖u x.val‖ ^ 2) ∂hsConfigurationVolume N) = 0 := by
  classical
  let E := HsEuclidean N
  let e := stdOrthonormalBasis ℝ E
  let ℓ := EuclideanSpace.proj (𝕜 := ℝ) (⟨0, N.pos⟩ : Fin (N : ℕ))
  let r := periodicSquareCutoff
  let u₀ := fun x : E => u (QuotientAddGroup.mk x)
  let V := fun x : E => W (QuotientAddGroup.mk x) + lam
  let A := fun x : E => (∑ i, ‖fderiv ℝ b x (e i) • u₀ x + b x • g i x‖ ^ 2) +
    V x * ‖b x • u₀ x‖ ^ 2 - (∑ i, (fderiv ℝ b x (e i)) ^ 2) * ‖u₀ x‖ ^ 2
  let B := fun x : E => ∑ i, 2 * b x ^ 2 * ℓ (e i) * RCLike.re (⟪u₀ x, g i x⟫ : ℂ)
  let c := fun x : E => r (ℓ x) * b x
  have hr : ContDiff ℝ ∞ r := contDiff_periodicSquareCutoff
  have hrc : HasCompactSupport r := hasCompactSupport_periodicSquareCutoff
  obtain ⟨R, hR⟩ := hr.lipschitzWith_of_hasCompactSupport hrc (by simp)
  obtain ⟨M, hM⟩ := bounded_hsPeriodic_cutoff hb.continuous hbp hbU
  obtain ⟨L, hL⟩ := hrc.exists_bound_of_continuous hr.continuous
  let l : ℝ≥0 := ⟨|L|, abs_nonneg L⟩
  have hcL : LipschitzWith (l * C + (R * ‖ℓ‖₊) * M) c :=
    lipschitzWith_mul_of_bounds (hR.comp ℓ.lipschitzWith)
      hb (fun x => (hL (ℓ x)).trans (le_abs_self L)) hM
  have hcc : HasCompactSupport c := hasCompactSupport_hsStrip_mul hbU hrc
  have hcU : tsupport c ⊆ hsChamber N := tsupport_mul_subset_right.trans hbU
  obtain ⟨hkin, hpot, hrhs, he⟩ := compact_cutoff_energy_prescribed_gradient
    (isOpen_hsChamber N) hW lam huL hu hg hcL hcc hcU
  let T := fun x : E => (∑ i, ‖fderiv ℝ c x (e i) • u₀ x + c x • g i x‖ ^ 2) +
    V x * ‖c x • u₀ x‖ ^ 2 - (∑ i, (fderiv ℝ c x (e i)) ^ 2) * ‖u₀ x‖ ^ 2
  let S := fun x : E => r (ℓ x) ^ 2 * A x + r (ℓ x) * fderiv ℝ r (ℓ x) 1 * B x
  have hTI : Integrable T := (hkin.add hpot).sub hrhs
  have hT0 : (∫ x, T x) = 0 := by
    have hz := integral_sub (hkin.add hpot) hrhs
    change (∫ x, T x) = _ at hz
    rw [hz]
    simp only [Pi.add_apply]
    rw [integral_add hkin hpot]
    exact sub_eq_zero.mpr he
  have hd (x : E) (hx : DifferentiableAt ℝ b x) (i) :
      fderiv ℝ c x (e i) = r (ℓ x) * fderiv ℝ b x (e i) +
        fderiv ℝ r (ℓ x) 1 * ℓ (e i) * b x := by
    have hrl : DifferentiableAt ℝ (fun x : E => r (ℓ x)) x :=
      (hr.differentiable (by simp) (ℓ x)).comp x ℓ.differentiableAt
    have hchain : fderiv ℝ (fun x : E => r (ℓ x)) x = (fderiv ℝ r (ℓ x)).comp ℓ :=
      by simpa only [ℓ.fderiv, Function.comp_def] using
        fderiv_comp x (hr.differentiable (by simp) (ℓ x)) ℓ.differentiableAt
    have hlin : fderiv ℝ r (ℓ x) (ℓ (e i)) = fderiv ℝ r (ℓ x) 1 * ℓ (e i) := by
      calc
        _ = fderiv ℝ r (ℓ x) (ℓ (e i) • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
        _ = _ := by rw [map_smul, smul_eq_mul, mul_comm]
    change fderiv ℝ (fun x => r (ℓ x) * b x) x (e i) = _
    rw [fderiv_fun_mul hrl hx, add_apply,
      smul_apply, smul_apply,
      hchain, ContinuousLinearMap.comp_apply, hlin]
    simp only [smul_eq_mul]
    ring
  have hTS : T =ᵐ[volume] S := by
    filter_upwards [hb.ae_differentiableAt (μ := volume)] with x hx
    dsimp only [T, S, A, B]
    simp only [hd x hx]
    dsimp only [c]
    exact square_cutoff_vector_energy_residual (r (ℓ x)) (fderiv ℝ r (ℓ x) 1)
      (b x) (V x) (fun i => fderiv ℝ b x (e i)) (fun i => ℓ (e i)) (u₀ x) (fun i => g i x)
  have hdbp (j : ℤ) (x : E) : fderiv ℝ b (hsTranslate (j : ℝ) x) = fderiv ℝ b x := by
    rw [hsTranslate_eq_add_rotation]
    exact fderiv_periodic_vector
      (fun j x => by rw [← hsTranslate_eq_add_rotation]; exact hbp j x) j x
  have hAp (j : ℤ) (x : E) : A (x + (j : ℝ) • hsRotationVector N) = A x := by
    rw [← hsTranslate_eq_add_rotation]
    dsimp only [A, V, u₀]
    simp only [hdbp, hbp, hgp, hs_quotient_mk_translate]
  have hBp (j : ℤ) (x : E) : B (x + (j : ℝ) • hsRotationVector N) = B x := by
    rw [← hsTranslate_eq_add_rotation]
    dsimp only [B, u₀]
    simp only [hbp, hgp, hs_quotient_mk_translate]
  have hAz (x : E) (hx : x ∉ tsupport b) : A x = 0 := by
    dsimp only [A]
    simp only [image_eq_zero_of_notMem_tsupport hx, fderiv_of_notMem_tsupport ℝ hx,
      zero_apply, zero_smul, add_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero, mul_zero, zero_mul, add_zero, sub_self]
  have hBz (x : E) (hx : x ∉ tsupport b) : B x = 0 := by
    dsimp only [B]
    simp only [image_eq_zero_of_notMem_tsupport hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero, zero_mul, Finset.sum_const_zero]
  have hAU : tsupport A ⊆ hsChamber N := by
    apply Subset.trans (closure_minimal ?_ (isClosed_tsupport b)) hbU
    intro x hx
    by_contra hxb
    exact hx (hAz x hxb)
  have hBU : tsupport B ⊆ hsChamber N := by
    apply Subset.trans (closure_minimal ?_ (isClosed_tsupport b)) hbU
    intro x hx
    by_contra hxb
    exact hx (hBz x hxb)
  have hSU : tsupport (fun x => r (ℓ x) * A x + fderiv ℝ r (ℓ x) 1 * B x) ⊆ hsChamber N :=
    (tsupport_add _ _).trans (union_subset
      (tsupport_mul_subset_right.trans hAU) (tsupport_mul_subset_right.trans hBU))
  have hSc : HasCompactSupport S := by
    have hh := hasCompactSupport_hsStrip_mul hSU hrc
    convert hh using 1
    funext x
    change r (ℓ x) ^ 2 * A x + r (ℓ x) * fderiv ℝ r (ℓ x) 1 * B x =
      r (ℓ x) * (r (ℓ x) * A x + fderiv ℝ r (ℓ x) 1 * B x)
    ring
  have hℓ : ℓ (hsRotationVector N) = 1 := by simp [ℓ, hsRotationVector]
  obtain ⟨_, hfold⟩ := integral_square_partition_residual (μ := volume)
    (hsRotationVector_ne_zero N) ℓ hℓ 1 hAp hBp hSc (hTI.congr hTS)
  have hstrip0 : (∫ x in ℓ ⁻¹' Ico (0 : ℝ) 1, A x) = 0 := by
    rw [hfold, ← integral_congr_ae hTS]
    exact hT0
  have hfund : (∫ x in hsFundamentalRegion N, A x) = 0 := by
    have hz : ∀ x ∈ ℓ ⁻¹' Ico (0 : ℝ) 1, x ∉ hsChamber N → A x = 0 := by
      intro x _ hx
      exact hAz x (fun h => hx (hbU h))
    change (∫ x in hsChamber N ∩ ℓ ⁻¹' Ico (0 : ℝ) 1, A x) = 0
    rw [inter_comm]
    rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_Ico.preimage ℓ.measurable) inter_subset_left
      (fun x hx => hz x hx.1 (fun h => hx.2 ⟨hx.1, h⟩))]
    exact hstrip0
  have hq (x : HsConfiguration N) : (QuotientAddGroup.mk (hsLiftPoint N x) : HsCylinder N) = x.val :=
    congrArg Subtype.val (hsChamberProjection_liftPoint x)
  have htransport := (measurePreserving_hsLiftPoint_volume N).integral_comp
    (measurableEmbedding_hsLiftPoint N) A
  simpa only [Function.comp_def, A, V, u₀, hq, e] using htransport.trans hfund

end Riesz1.Internal
