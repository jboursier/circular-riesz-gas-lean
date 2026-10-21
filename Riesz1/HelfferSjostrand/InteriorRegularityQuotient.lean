/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.QuotientChartL2
public import Riesz1.HelfferSjostrand.InteriorRegularityRealEnergy

/-!
# Interior regularity of quotient L² solutions

A quotient function is written as a cylinder function restricted to the
configuration manifold. The existing
Schrödinger predicate is applied to its periodic lift. Arbitrary quotient
L² data are transported to local cover L² before applying the Euclidean
regularity theorem. The energy theorems here concern compact cover cutoffs.
They do not assert energy for general quotient-compact periodic cutoffs.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal NNReal

namespace Riesz1

/-- The complex quotient H²_loc clause of interior regularity.
Smoothness and the distributional equation are expressed in the Euclidean
charts, using the existing predicates. -/
theorem interiorRegularity_quotient_complex_h2 {N : ℕ+} {W : HsCylinder N → ℝ}
    (hW : ContDiffOn ℝ ∞ (fun x : HsEuclidean N => W (QuotientAddGroup.mk x)) (hsChamber N))
    (lam : ℝ) {u : HsCylinder N → ℂ}
    (huL : MemLp (fun x : HsConfiguration N => u x.val) 2 (hsConfigurationVolume N))
    (hu : IsDistributionalSchrodingerSolution (hsChamber N)
      (fun x => W (QuotientAddGroup.mk x)) lam (fun x => u (QuotientAddGroup.mk x))) :
    IsLocalH2 (hsChamber N) (fun x => u (QuotientAddGroup.mk x)) :=
  isLocalH2_of_locallySquareIntegrable_schrodinger (isOpen_hsChamber N) hW lam
    (locallySquareIntegrableOn_quotient_mk huL) hu

/-- The real quotient H²_loc clause of interior regularity. -/
theorem interiorRegularity_quotient_real_h2 {N : ℕ+} {W : HsCylinder N → ℝ}
    (hW : ContDiffOn ℝ ∞ (fun x : HsEuclidean N => W (QuotientAddGroup.mk x)) (hsChamber N))
    (lam : ℝ) {u : HsCylinder N → ℝ}
    (huL : MemLp (fun x : HsConfiguration N => u x.val) 2 (hsConfigurationVolume N))
    (hu : IsDistributionalSchrodingerSolution (hsChamber N)
      (fun x => W (QuotientAddGroup.mk x)) lam (fun x => u (QuotientAddGroup.mk x))) :
    IsLocalH2 (hsChamber N) (fun x => u (QuotientAddGroup.mk x)) := by
  have hC := isLocalH2_of_locallySquareIntegrable_schrodinger (isOpen_hsChamber N) hW lam
    ((locallySquareIntegrableOn_quotient_mk huL).map Complex.ofRealCLM)
    (hu.map Complex.ofRealCLM)
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.reCLM_apply,
    Complex.ofReal_re] using hC.map Complex.reCLM

/-- Quotient L² solutions obey the complex energy identity in every
compact cover chart. All integrals have their integrability certificates. -/
theorem interiorRegularity_quotient_complex_chart_energy {N : ℕ+} {W : HsCylinder N → ℝ}
    (hW : ContDiffOn ℝ ∞ (fun x : HsEuclidean N => W (QuotientAddGroup.mk x)) (hsChamber N))
    (lam : ℝ) {u : HsCylinder N → ℂ}
    (huL : MemLp (fun x : HsConfiguration N => u x.val) 2 (hsConfigurationVolume N))
    (hu : IsDistributionalSchrodingerSolution (hsChamber N)
      (fun x => W (QuotientAddGroup.mk x)) lam (fun x => u (QuotientAddGroup.mk x)))
    {b : HsEuclidean N → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ hsChamber N) :
    IsLocalH2 (hsChamber N) (fun x => u (QuotientAddGroup.mk x)) ∧
    ∃ g : Fin (Module.finrank ℝ (HsEuclidean N)) → HsEuclidean N → ℂ,
      (∀ i, MemLp (g i) 2 volume ∧
        HasWeakDirectionalDerivativeOn univ (fun x => b x • u (QuotientAddGroup.mk x)) (g i)
          (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ∧
      Integrable (fun x => ∑ i, ‖g i x‖ ^ 2) ∧
      Integrable (fun x => (W (QuotientAddGroup.mk x) + lam) * ‖b x • u (QuotientAddGroup.mk x)‖ ^ 2) ∧
      Integrable (fun x => (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ^ 2) *
        ‖u (QuotientAddGroup.mk x)‖ ^ 2) ∧
      (∫ x, ∑ i, ‖g i x‖ ^ 2) +
        (∫ x, (W (QuotientAddGroup.mk x) + lam) * ‖b x • u (QuotientAddGroup.mk x)‖ ^ 2) =
        ∫ x, (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ^ 2) *
          ‖u (QuotientAddGroup.mk x)‖ ^ 2 :=
  interiorRegularity_complex_local_energy (isOpen_hsChamber N) hW lam
    (locallySquareIntegrableOn_quotient_mk huL) hu hb hbc hbU

/-- The real counterpart, with real weak gradient coordinates. -/
theorem interiorRegularity_quotient_real_chart_energy {N : ℕ+} {W : HsCylinder N → ℝ}
    (hW : ContDiffOn ℝ ∞ (fun x : HsEuclidean N => W (QuotientAddGroup.mk x)) (hsChamber N))
    (lam : ℝ) {u : HsCylinder N → ℝ}
    (huL : MemLp (fun x : HsConfiguration N => u x.val) 2 (hsConfigurationVolume N))
    (hu : IsDistributionalSchrodingerSolution (hsChamber N)
      (fun x => W (QuotientAddGroup.mk x)) lam (fun x => u (QuotientAddGroup.mk x)))
    {b : HsEuclidean N → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ hsChamber N) :
    IsLocalH2 (hsChamber N) (fun x => u (QuotientAddGroup.mk x)) ∧
    ∃ g : Fin (Module.finrank ℝ (HsEuclidean N)) → HsEuclidean N → ℝ,
      (∀ i, MemLp (g i) 2 volume ∧
        HasWeakDirectionalDerivativeOn univ (fun x => b x * u (QuotientAddGroup.mk x)) (g i)
          (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ∧
      Integrable (fun x => ∑ i, (g i x) ^ 2) ∧
      Integrable (fun x => (W (QuotientAddGroup.mk x) + lam) * (b x * u (QuotientAddGroup.mk x)) ^ 2) ∧
      Integrable (fun x => (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ^ 2) *
        (u (QuotientAddGroup.mk x)) ^ 2) ∧
      (∫ x, ∑ i, (g i x) ^ 2) +
        (∫ x, (W (QuotientAddGroup.mk x) + lam) * (b x * u (QuotientAddGroup.mk x)) ^ 2) =
        ∫ x, (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ (HsEuclidean N) i)) ^ 2) *
          (u (QuotientAddGroup.mk x)) ^ 2 :=
  interiorRegularity_real_local_energy (isOpen_hsChamber N) hW lam
    (locallySquareIntegrableOn_quotient_mk huL) hu hb hbc hbU

end Riesz1
