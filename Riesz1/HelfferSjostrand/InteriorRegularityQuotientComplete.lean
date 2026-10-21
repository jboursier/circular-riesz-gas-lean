/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.InteriorRegularityQuotientRealEnergy
public import Riesz1.HelfferSjostrand.QuotientChartZeroExtension
public import Riesz1.HelfferSjostrand.InteriorRegularityRealEnergy

/-!
# Interior regularity on the quotient and on Euclidean open sets

The interior regularity assertion, with every compactly supported Lipschitz cutoff
on the actual quotient. The returned lift is specified as its zero
extension, and all derivatives are the existing Euclidean chart derivatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff NNReal

namespace Riesz1

/-- Interior regularity, complex form on `D_N`. This quantifies
over quotient cutoffs, including support crossing any rotation seam.
No lower bound on the smooth potential is needed for this local identity. -/
theorem interiorRegularity_quotient_complex {N : ℕ+}
    {W : HsCylinder N → ℝ}
    (hW : ContDiffOn ℝ ∞ (fun x : HsEuclidean N => W (QuotientAddGroup.mk x)) (hsChamber N))
    (lam : ℝ) {u : HsCylinder N → ℂ}
    (huL : MemLp (fun x : HsConfiguration N => u x.val) 2 (hsConfigurationVolume N))
    (hu : IsDistributionalSchrodingerSolution (hsChamber N)
      (fun x => W (QuotientAddGroup.mk x)) lam (fun x => u (QuotientAddGroup.mk x)))
    {β : HsConfiguration N → ℝ} {C : ℝ≥0} (hβ : LipschitzWith C β)
    (hβc : HasCompactSupport β) :
    IsLocalH2 (hsChamber N) (fun x => u (QuotientAddGroup.mk x)) ∧
    ∃ (b : HsEuclidean N → ℝ) (D : ℝ≥0), LipschitzWith D b ∧
      (∀ (j : ℤ) x, b (hsTranslate (j : ℝ) x) = b x) ∧ tsupport b ⊆ hsChamber N ∧
      (∀ x : hsChamber N, b x.val = β (hsChamberProjection x)) ∧
      (∀ x : HsConfiguration N, b (hsLiftPoint N x) = β x) ∧
      (∀ x ∉ hsChamber N, b x = 0) ∧
      ∃ k : Fin (Module.finrank ℝ (HsEuclidean N)) → HsEuclidean N → ℂ,
      (∀ i, (∀ (j : ℤ) x, k i (hsTranslate (j : ℝ) x) = k i x) ∧
        MemLp (k i ∘ hsLiftPoint N) 2 (hsConfigurationVolume N) ∧
        HasWeakDirectionalDerivativeOn (hsChamber N)
          (fun x => b x • u (QuotientAddGroup.mk x)) (k i)
          (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ∧
      Integrable (fun x : HsConfiguration N => ∑ i, ‖k i (hsLiftPoint N x)‖ ^ 2)
        (hsConfigurationVolume N) ∧
      Integrable (fun x : HsConfiguration N => (W x.val + lam) *
        ‖β x • u x.val‖ ^ 2) (hsConfigurationVolume N) ∧
      Integrable (fun x : HsConfiguration N =>
        (∑ i, (fderiv ℝ b (hsLiftPoint N x) (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ^ 2) *
          ‖u x.val‖ ^ 2) (hsConfigurationVolume N) ∧
      (∫ x : HsConfiguration N, ∑ i, ‖k i (hsLiftPoint N x)‖ ^ 2 ∂hsConfigurationVolume N) +
        (∫ x : HsConfiguration N, (W x.val + lam) *
          ‖β x • u x.val‖ ^ 2 ∂hsConfigurationVolume N) =
        ∫ x : HsConfiguration N,
          (∑ i, (fderiv ℝ b (hsLiftPoint N x) (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ^ 2) *
            ‖u x.val‖ ^ 2 ∂hsConfigurationVolume N := by
  obtain ⟨b, D, hb, hbp, hbU, hbchart, hbq, hbz⟩ := exists_hsQuotient_cutoff_lift hβ hβc
  obtain ⟨hH2, k, hk, hkin, hpot, hrhs, he⟩ :=
    interiorRegularity_quotient_complex_energy hW lam huL hu hb hbp hbU
  refine ⟨hH2, b, D, hb, hbp, hbU, hbchart, hbq, hbz, k, hk, hkin, ?_, hrhs, ?_⟩
  · simpa only [hbq] using hpot
  · simpa only [hbq] using he

/-- Interior regularity, real form on `D_N`. This quantifies
over quotient cutoffs, including support crossing any rotation seam.
No lower bound on the smooth potential is needed for this local identity. -/
theorem interiorRegularity_quotient_real {N : ℕ+}
    {W : HsCylinder N → ℝ}
    (hW : ContDiffOn ℝ ∞ (fun x : HsEuclidean N => W (QuotientAddGroup.mk x)) (hsChamber N))
    (lam : ℝ) {u : HsCylinder N → ℝ}
    (huL : MemLp (fun x : HsConfiguration N => u x.val) 2 (hsConfigurationVolume N))
    (hu : IsDistributionalSchrodingerSolution (hsChamber N)
      (fun x => W (QuotientAddGroup.mk x)) lam (fun x => u (QuotientAddGroup.mk x)))
    {β : HsConfiguration N → ℝ} {C : ℝ≥0} (hβ : LipschitzWith C β)
    (hβc : HasCompactSupport β) :
    IsLocalH2 (hsChamber N) (fun x => u (QuotientAddGroup.mk x)) ∧
    ∃ (b : HsEuclidean N → ℝ) (D : ℝ≥0), LipschitzWith D b ∧
      (∀ (j : ℤ) x, b (hsTranslate (j : ℝ) x) = b x) ∧ tsupport b ⊆ hsChamber N ∧
      (∀ x : hsChamber N, b x.val = β (hsChamberProjection x)) ∧
      (∀ x : HsConfiguration N, b (hsLiftPoint N x) = β x) ∧
      (∀ x ∉ hsChamber N, b x = 0) ∧
      ∃ k : Fin (Module.finrank ℝ (HsEuclidean N)) → HsEuclidean N → ℝ,
      (∀ i, (∀ (j : ℤ) x, k i (hsTranslate (j : ℝ) x) = k i x) ∧
        MemLp (k i ∘ hsLiftPoint N) 2 (hsConfigurationVolume N) ∧
        HasWeakDirectionalDerivativeOn (hsChamber N)
          (fun x => b x * u (QuotientAddGroup.mk x)) (k i)
          (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ∧
      Integrable (fun x : HsConfiguration N => ∑ i, (k i (hsLiftPoint N x)) ^ 2)
        (hsConfigurationVolume N) ∧
      Integrable (fun x : HsConfiguration N => (W x.val + lam) *
        (β x * u x.val) ^ 2) (hsConfigurationVolume N) ∧
      Integrable (fun x : HsConfiguration N =>
        (∑ i, (fderiv ℝ b (hsLiftPoint N x) (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ^ 2) *
          (u x.val) ^ 2) (hsConfigurationVolume N) ∧
      (∫ x : HsConfiguration N, ∑ i, (k i (hsLiftPoint N x)) ^ 2 ∂hsConfigurationVolume N) +
        (∫ x : HsConfiguration N, (W x.val + lam) *
          (β x * u x.val) ^ 2 ∂hsConfigurationVolume N) =
        ∫ x : HsConfiguration N,
          (∑ i, (fderiv ℝ b (hsLiftPoint N x) (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ^ 2) *
            (u x.val) ^ 2 ∂hsConfigurationVolume N := by
  obtain ⟨b, D, hb, hbp, hbU, hbchart, hbq, hbz⟩ := exists_hsQuotient_cutoff_lift hβ hβc
  obtain ⟨hH2, k, hk, hkin, hpot, hrhs, he⟩ :=
    interiorRegularity_quotient_real_energy hW lam huL hu hb hbp hbU
  refine ⟨hH2, b, D, hb, hbp, hbU, hbchart, hbq, hbz, k, hk, hkin, ?_, hrhs, ?_⟩
  · simpa only [hbq] using hpot
  · simpa only [hbq] using he

/-- The complete complex interior regularity assertion, on the
quotient and on every finite-dimensional Euclidean open set. -/
theorem interiorRegularity_L3232_complex :
    (∀ {N : ℕ+}
    {W : HsCylinder N → ℝ}
    (hW : ContDiffOn ℝ ∞ (fun x : HsEuclidean N => W (QuotientAddGroup.mk x)) (hsChamber N))
    (lam : ℝ) {u : HsCylinder N → ℂ}
    (huL : MemLp (fun x : HsConfiguration N => u x.val) 2 (hsConfigurationVolume N))
    (hu : IsDistributionalSchrodingerSolution (hsChamber N)
      (fun x => W (QuotientAddGroup.mk x)) lam (fun x => u (QuotientAddGroup.mk x)))
    {β : HsConfiguration N → ℝ} {C : ℝ≥0} (hβ : LipschitzWith C β)
    (hβc : HasCompactSupport β),
    IsLocalH2 (hsChamber N) (fun x => u (QuotientAddGroup.mk x)) ∧
    ∃ (b : HsEuclidean N → ℝ) (D : ℝ≥0), LipschitzWith D b ∧
      (∀ (j : ℤ) x, b (hsTranslate (j : ℝ) x) = b x) ∧ tsupport b ⊆ hsChamber N ∧
      (∀ x : hsChamber N, b x.val = β (hsChamberProjection x)) ∧
      (∀ x : HsConfiguration N, b (hsLiftPoint N x) = β x) ∧
      (∀ x ∉ hsChamber N, b x = 0) ∧
      ∃ k : Fin (Module.finrank ℝ (HsEuclidean N)) → HsEuclidean N → ℂ,
      (∀ i, (∀ (j : ℤ) x, k i (hsTranslate (j : ℝ) x) = k i x) ∧
        MemLp (k i ∘ hsLiftPoint N) 2 (hsConfigurationVolume N) ∧
        HasWeakDirectionalDerivativeOn (hsChamber N)
          (fun x => b x • u (QuotientAddGroup.mk x)) (k i)
          (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ∧
      Integrable (fun x : HsConfiguration N => ∑ i, ‖k i (hsLiftPoint N x)‖ ^ 2)
        (hsConfigurationVolume N) ∧
      Integrable (fun x : HsConfiguration N => (W x.val + lam) *
        ‖β x • u x.val‖ ^ 2) (hsConfigurationVolume N) ∧
      Integrable (fun x : HsConfiguration N =>
        (∑ i, (fderiv ℝ b (hsLiftPoint N x) (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ^ 2) *
          ‖u x.val‖ ^ 2) (hsConfigurationVolume N) ∧
      (∫ x : HsConfiguration N, ∑ i, ‖k i (hsLiftPoint N x)‖ ^ 2 ∂hsConfigurationVolume N) +
        (∫ x : HsConfiguration N, (W x.val + lam) *
          ‖β x • u x.val‖ ^ 2 ∂hsConfigurationVolume N) =
        ∫ x : HsConfiguration N,
          (∑ i, (fderiv ℝ b (hsLiftPoint N x) (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ^ 2) *
            ‖u x.val‖ ^ 2 ∂hsConfigurationVolume N) ∧
    (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ) {u : E → ℂ}
    (huL : MemLp u 2 (volume.restrict U))
    (hu : IsDistributionalSchrodingerSolution U W lam u)
    {b : E → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ U),
    IsLocalH2 U u ∧ ∃ g : Fin (Module.finrank ℝ E) → E → ℂ,
      (∀ i, MemLp (g i) 2 volume ∧
        HasWeakDirectionalDerivativeOn univ (fun x => b x • u x) (g i)
          (stdOrthonormalBasis ℝ E i)) ∧
      Integrable (fun x => ∑ i, ‖g i x‖ ^ 2) ∧
      Integrable (fun x => (W x + lam) * ‖b x • u x‖ ^ 2) ∧
      Integrable (fun x => (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) *
        ‖u x‖ ^ 2) ∧
      (∫ x, ∑ i, ‖g i x‖ ^ 2) + (∫ x, (W x + lam) * ‖b x • u x‖ ^ 2) =
        ∫ x, (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) * ‖u x‖ ^ 2) :=
  ⟨@interiorRegularity_quotient_complex, @interiorRegularity_complex_energy⟩

/-- The complete real interior regularity assertion, on the
quotient and on every finite-dimensional Euclidean open set. -/
theorem interiorRegularity_L3232_real :
    (∀ {N : ℕ+}
    {W : HsCylinder N → ℝ}
    (hW : ContDiffOn ℝ ∞ (fun x : HsEuclidean N => W (QuotientAddGroup.mk x)) (hsChamber N))
    (lam : ℝ) {u : HsCylinder N → ℝ}
    (huL : MemLp (fun x : HsConfiguration N => u x.val) 2 (hsConfigurationVolume N))
    (hu : IsDistributionalSchrodingerSolution (hsChamber N)
      (fun x => W (QuotientAddGroup.mk x)) lam (fun x => u (QuotientAddGroup.mk x)))
    {β : HsConfiguration N → ℝ} {C : ℝ≥0} (hβ : LipschitzWith C β)
    (hβc : HasCompactSupport β),
    IsLocalH2 (hsChamber N) (fun x => u (QuotientAddGroup.mk x)) ∧
    ∃ (b : HsEuclidean N → ℝ) (D : ℝ≥0), LipschitzWith D b ∧
      (∀ (j : ℤ) x, b (hsTranslate (j : ℝ) x) = b x) ∧ tsupport b ⊆ hsChamber N ∧
      (∀ x : hsChamber N, b x.val = β (hsChamberProjection x)) ∧
      (∀ x : HsConfiguration N, b (hsLiftPoint N x) = β x) ∧
      (∀ x ∉ hsChamber N, b x = 0) ∧
      ∃ k : Fin (Module.finrank ℝ (HsEuclidean N)) → HsEuclidean N → ℝ,
      (∀ i, (∀ (j : ℤ) x, k i (hsTranslate (j : ℝ) x) = k i x) ∧
        MemLp (k i ∘ hsLiftPoint N) 2 (hsConfigurationVolume N) ∧
        HasWeakDirectionalDerivativeOn (hsChamber N)
          (fun x => b x * u (QuotientAddGroup.mk x)) (k i)
          (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ∧
      Integrable (fun x : HsConfiguration N => ∑ i, (k i (hsLiftPoint N x)) ^ 2)
        (hsConfigurationVolume N) ∧
      Integrable (fun x : HsConfiguration N => (W x.val + lam) *
        (β x * u x.val) ^ 2) (hsConfigurationVolume N) ∧
      Integrable (fun x : HsConfiguration N =>
        (∑ i, (fderiv ℝ b (hsLiftPoint N x) (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ^ 2) *
          (u x.val) ^ 2) (hsConfigurationVolume N) ∧
      (∫ x : HsConfiguration N, ∑ i, (k i (hsLiftPoint N x)) ^ 2 ∂hsConfigurationVolume N) +
        (∫ x : HsConfiguration N, (W x.val + lam) *
          (β x * u x.val) ^ 2 ∂hsConfigurationVolume N) =
        ∫ x : HsConfiguration N,
          (∑ i, (fderiv ℝ b (hsLiftPoint N x) (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ^ 2) *
            (u x.val) ^ 2 ∂hsConfigurationVolume N) ∧
    (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ) {u : E → ℝ}
    (huL : MemLp u 2 (volume.restrict U))
    (hu : IsDistributionalSchrodingerSolution U W lam u)
    {b : E → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ U),
    IsLocalH2 U u ∧ ∃ g : Fin (Module.finrank ℝ E) → E → ℝ,
      (∀ i, MemLp (g i) 2 volume ∧
        HasWeakDirectionalDerivativeOn univ (fun x => b x * u x) (g i)
          (stdOrthonormalBasis ℝ E i)) ∧
      Integrable (fun x => ∑ i, (g i x) ^ 2) ∧
      Integrable (fun x => (W x + lam) * (b x * u x) ^ 2) ∧
      Integrable (fun x => (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) *
        (u x) ^ 2) ∧
      (∫ x, ∑ i, (g i x) ^ 2) + (∫ x, (W x + lam) * (b x * u x) ^ 2) =
        ∫ x, (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) * (u x) ^ 2) :=
  ⟨@interiorRegularity_quotient_real, @interiorRegularity_real_energy⟩

end Riesz1
