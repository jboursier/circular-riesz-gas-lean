/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.InteriorRegularityEnergy
public import Riesz1.ToMathlib.EllipticRegularity.LocalLipschitz

/-!
# Compact cutoff energy with prescribed local weak derivatives

Uniqueness identifies the gradients supplied by the compact energy theorem
with the product rule for any given local L² weak representatives. This
allows the same periodic representatives to be used in different charts.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff NNReal

namespace Riesz1.Internal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The compact energy theorem with its gradient identified using
specified local L² weak derivatives. This is an internal assembly lemma. -/
theorem compact_cutoff_energy_prescribed_gradient {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ) {u : E → ℂ}
    (huL : LocallySquareIntegrableOn U u)
    (hu : IsDistributionalSchrodingerSolution U W lam u)
    {g : Fin (Module.finrank ℝ E) → E → ℂ}
    (hg : ∀ i, LocallySquareIntegrableOn U (g i) ∧
      HasWeakDirectionalDerivativeOn U u (g i) (stdOrthonormalBasis ℝ E i))
    {b : E → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b) (hbc : HasCompactSupport b)
    (hbU : tsupport b ⊆ U) :
    Integrable (fun x => ∑ i,
      ‖fderiv ℝ b x (stdOrthonormalBasis ℝ E i) • u x + b x • g i x‖ ^ 2) ∧
    Integrable (fun x => (W x + lam) * ‖b x • u x‖ ^ 2) ∧
    Integrable (fun x => (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) * ‖u x‖ ^ 2) ∧
    (∫ x, ∑ i, ‖fderiv ℝ b x (stdOrthonormalBasis ℝ E i) • u x + b x • g i x‖ ^ 2) +
      (∫ x, (W x + lam) * ‖b x • u x‖ ^ 2) =
        ∫ x, (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) * ‖u x‖ ^ 2 := by
  classical
  obtain ⟨_, k, hk, hkin, hpot, hrhs, he⟩ :=
    interiorRegularity_complex_local_energy hU hW lam huL hu hb hbc hbU
  have heq (i : Fin (Module.finrank ℝ E)) :
      k i =ᵐ[volume] (fun x => fderiv ℝ b x (stdOrthonormalBasis ℝ E i) • u x + b x • g i x) := by
    obtain ⟨haL, hdL, hd⟩ := (hg i).2.smul_lipschitz hU huL (hg i).1 hb
    have hac : HasCompactSupport (fun x => b x • u x) := hbc.smul_right
    have hdc : HasCompactSupport
        (fun x => fderiv ℝ b x (stdOrthonormalBasis ℝ E i) • u x + b x • g i x) :=
      ((hbc.fderiv_apply ℝ _).smul_right).add hbc.smul_right
    have haU := (tsupport_smul_subset_left b u).trans hbU
    have hdU : tsupport (fun x => fderiv ℝ b x (stdOrthonormalBasis ℝ E i) • u x +
        b x • g i x) ⊆ U := (tsupport_add _ _).trans (union_subset
      ((tsupport_smul_subset_left _ u).trans ((tsupport_fderiv_apply_subset ℝ _).trans hbU))
      ((tsupport_smul_subset_left b (g i)).trans hbU))
    have hglobal := weakDerivative_univ_of_compact hU hd
      (memLp_of_local_compact_interior haL hac haU)
      (memLp_of_local_compact_interior hdL hdc hdU) hac hdc haU hdU
    simpa only [Measure.restrict_univ] using (hk i).2.unique isOpen_univ hglobal
  have hkinEq : (fun x => ∑ i, ‖k i x‖ ^ 2) =ᵐ[volume]
      (fun x => ∑ i, ‖fderiv ℝ b x (stdOrthonormalBasis ℝ E i) • u x + b x • g i x‖ ^ 2) := by
    filter_upwards [ae_all_iff.mpr heq] with x hx
    simp only [hx]
  exact ⟨hkin.congr hkinEq, hpot, hrhs, by rwa [integral_congr_ae hkinEq] at he⟩

end Riesz1.Internal
